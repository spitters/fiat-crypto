(** * BLS12-381 GLV Shamir scalar multiplication -- bedrock2 implementation.

    Implements Shamir's trick for the GLV two-scalar multiplication:
      [k]P = [k1]P + [k2]phi(P)
    where (k1, k2) = glv_decompose(k), with k1, k2 each at most 129 bits.

    The function takes phi(P) as a precomputed input (caller multiplies
    P_x by omega) so the loop body avoids loading the omega constant.

    Scalars k1, k2 are pointers to 2-word (128-bit) bignums.
    The loop runs 129 iterations (MSB to LSB via shift-and-test),
    matching the Gallina [shamir_mult 129 k1 k2 P phi_P zero].

    Prerequisites (all compile under Rocq 9):
    - BLS12_GLV_ScalarMult.v   -- Gallina shamir_mult + correctness
    - BLS12_Endomorphism.v     -- omega, lambda constants
    - BLS12_GLV_Decompose.v    -- k1 = k mod lambda, k2 = k div lambda
    - ScalarMult.v             -- existing 256-bit scalar mult (pattern)
    - LoopBody.v               -- per-iteration body pattern
    - BLS12_G1.v               -- BLS12 curve_add (ladderstep)
*)

From Stdlib Require Import ZArith Lia.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Group.CurveAdd.StoreZero.
Require Import Crypto.Bedrock.Group.CurveAdd.CondMoveGroup.
Require Import Crypto.Bedrock.Group.CurveAdd.CurveAdd.
Require Import bedrock2.Loops.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

(* ================================================================== *)
(** * Section 1: Generic Shamir loop body (parametric over width)      *)
(* ================================================================== *)

Section GLV_Shamir_Generic.
  Context {width : Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}
          {group_cmov_alt : string}
          {store_zero : string}.

  Local Notation F := (F M_pos).
  Local Notation Fzero := (F.of_Z M_pos 0).
  Local Notation Fone := (F.of_Z M_pos 1).

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (curve_add_name : string).

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).
  Context (three_b_name : string).
  Context (Hb_bounds : maybe_bounded (Some loose_bounds) three_b).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  (* GLV scalars are 2-word (128-bit) bignums on a 64-bit machine *)
  Let glv_scalar_words : nat := 2.

  (* 129 iterations: max(bits(k1), bits(k2)) where k1 < lambda < 2^128
     and k2 <= lambda+1 < 2^129 *)
  Let glv_iterations : Z := 129.

  Local Notation eval_bignum n x :=
    (Positional.eval (uweight width) n (List.map word.unsigned x)).

  (* Local spec for shift_scalar (from BignumShift.v, not compiled).
     shift_scalar extracts the low bit and right-shifts a bignum by 1. *)
  Local Instance spec_of_shift_scalar : spec_of "shift_scalar" :=
    fnspec! "shift_scalar"
          (pc px : word)
          / c x R,
    { requires tr mem :=
        (Bignum.Bignum glv_scalar_words px x ⋆ scalar pc c ⋆ R) mem;
      ensures tr' mem' :=
        exists c' x',
          tr = tr'
          /\ eval_bignum glv_scalar_words x / 2 = eval_bignum glv_scalar_words x'
          /\ eval_bignum glv_scalar_words x mod 2 = word.unsigned c'
          /\ ((Bignum.Bignum glv_scalar_words px x' ⋆ scalar pc c' ⋆ R) mem')}.

  (* The Gallina-level curve_add operation (from ladderstep) *)
  Context {curve_add : (F * F * F) -> (F * F * F) -> (F * F * F)}.
  Context {curve_add_id_r : forall x y z, curve_add (x, y, z) (Fzero, Fone, Fzero) = (x, y, z)}.
  Context {curve_add_id_l : forall x y z, curve_add (Fzero, Fone, Fzero) (x, y, z) = (x, y, z)}.
  Context {curve_add_assoc : forall P Q R, curve_add P (curve_add Q R) = curve_add (curve_add P Q) R}.

  (* Gallina scalar multiplication via repeated addition *)
  Fixpoint scmul_glv (n : nat) (P : F * F * F) : F * F * F :=
    match n with
    | O => (Fzero, Fone, Fzero)
    | S m => curve_add P (scmul_glv m P)
    end.

  (* Gallina Shamir double-and-add (MSB-first, 129 iterations).
     This mirrors BLS12_GLV_ScalarMult.shamir_mult but is specialized to
     our concrete curve_add. We restate it here to avoid pulling in the
     abstract group algebra infrastructure. *)

  Definition b2z (b : bool) : Z := if b then 1 else 0.

  (* cond_add c P Q = if c then curve_add P Q else P *)
  Definition cond_add (c : bool) (acc P : F * F * F) : F * F * F :=
    if c then curve_add acc P else acc.

  (* Single Shamir iteration: double acc, conditionally add P, conditionally add Q *)
  Definition shamir_step (k1 k2 : Z) (i : nat) (P Q acc : F * F * F) : F * F * F :=
    let acc' := curve_add acc acc in                            (* double *)
    let acc'' := cond_add (Z.testbit k1 (Z.of_nat i)) acc' P in (* cond add P *)
    cond_add (Z.testbit k2 (Z.of_nat i)) acc'' Q.               (* cond add Q *)

  (* Full Shamir loop: bits iterations from (bits-1) down to 0 *)
  Fixpoint shamir_loop (bits : nat) (k1 k2 : Z) (P Q acc : F * F * F) : F * F * F :=
    match bits with
    | O => acc
    | S n => shamir_loop n k1 k2 P Q (shamir_step k1 k2 n P Q acc)
    end.

  (* ================================================================== *)
  (** * Section 2: bedrock2 function definition                         *)
  (* ================================================================== *)

  (** The GLV Shamir scalar multiplication function.

      Arguments:
        outx, outy, outz   -- output point (Jacobian)
        px, py, pz         -- input point P (Jacobian, tight bounds)
        phix, phiy, phiz   -- phi(P) = (omega*P_x, P_y, P_z) (tight bounds)
        pk1                -- pointer to 2-word bignum for k1
        pk2                -- pointer to 2-word bignum for k2

      Algorithm:
        out = (0, 1, 0)    // identity in Jacobian
        for iter = 0 to 128:
          // Extract low bit of k1, shift k1 right
          shift_scalar(cond1, pk1)
          // Extract low bit of k2, shift k2 right
          shift_scalar(cond2, pk2)
          // Double: out = out + out
          curve_add(outx, outx, outy, outy, outz, outz, outx, outy, outz)
          // Conditional add P: aux = cond1 ? P : identity; out = out + aux
          store_zero(auxx, auxy, auxz)
          group_cmov_alt(auxx, auxy, auxz, auxx, auxy, auxz, px, py, pz, cond1)
          curve_add(outx, auxx, outy, auxy, outz, auxz, outx, outy, outz)
          // Conditional add phi(P): aux = cond2 ? phi(P) : identity; out = out + aux
          store_zero(auxx, auxy, auxz)
          group_cmov_alt(auxx, auxy, auxz, auxx, auxy, auxz, phix, phiy, phiz, cond2)
          curve_add(outx, auxx, outy, auxy, outz, auxz, outx, outy, outz)

      NOTE: This processes bits LSB-first (via shift_scalar) which means
      the loop processes k from bit 0 up to bit 128. The doubling of P
      (and phi(P)) at each iteration is handled implicitly through the
      point accumulator. However, the standard Shamir trick is MSB-first.

      For an LSB-first variant we need:
        out = identity
        P_acc = P, Q_acc = phi(P)
        for i = 0 to 128:
          bit1 = k1 & 1; k1 >>= 1
          bit2 = k2 & 1; k2 >>= 1
          if bit1: out += P_acc
          if bit2: out += Q_acc
          P_acc = 2*P_acc    // double P accumulator
          Q_acc = 2*Q_acc    // double Q accumulator

      This requires 3 doublings per iteration (out, P_acc, Q_acc) in the
      worst case, vs 1 doubling + 2 conditional adds for MSB-first.
      But LSB-first matches the existing shift_scalar infrastructure.

      Actually, the existing LoopBody.v already uses the pattern:
        1. shift_scalar to extract low bit
        2. cmov + curve_add to conditionally add
        3. curve_add(P, P) to double the point accumulator
      This means LoopBody.v IS LSB-first! The invariant tracks:
        out = scmul(n mod 2^iter, P_init)
        P   = scmul(2^iter, P_init)  = [2^iter]P_init
      So at each step, P doubles and out conditionally gets P added.

      For Shamir we need TWO such accumulators (P doubles, phi(P) doubles)
      plus the output. The bedrock2 function body follows this pattern:
        - out accumulates the result
        - P doubles each iteration (so P = [2^iter]P_init)
        - phi(P) doubles each iteration (so phi(P) = [2^iter]phi(P_init))
        - At each step: extract bit of k1 and k2, conditionally add P or phi(P)
  *)

  Definition glv_shamir_func : function_t :=
    ("bls12_glv_shamir",
     (["outx"; "outy"; "outz";
       "px"; "py"; "pz";
       "phix"; "phiy"; "phiz";
       "pk1"; "pk2"],
      []:list String.string,
      bedrock_func_body:(
        (* Stack allocations for auxiliary point and condition words *)
        stackalloc felem_size_in_bytes as auxx;
        stackalloc felem_size_in_bytes as auxy;
        stackalloc felem_size_in_bytes as auxz;
        stackalloc (Memory.bytes_per_word width) as cond1;
        stackalloc (Memory.bytes_per_word width) as cond2;
        stackalloc (Memory.bytes_per_word width) as iter;

        (* Initialize output to identity point O = (0, 1, 0) *)
        coq:(cmd.call [] "store_zero"
               [expr.var "outx"; expr.var "outy"; expr.var "outz"]);

        (* Initialize loop counter *)
        coq:(cmd.store access_size.word (expr.var "iter") (expr.literal 0));

        (* Main loop: 129 iterations (bits 0..128) *)
        while (coq:(expr.op bopname.ltu
                      (expr.load access_size.word (expr.var "iter"))
                      (expr.literal glv_iterations))) {
          (* Increment iteration counter *)
          coq:(cmd.store access_size.word (expr.var "iter")
                 (expr.op bopname.add
                    (expr.load access_size.word (expr.var "iter"))
                    (expr.literal 1)));

          (* Extract low bit of k1 and shift k1 right by 1 *)
          coq:(cmd.call [] "shift_scalar"
                 [expr.var "cond1"; expr.var "pk1"]);

          (* Extract low bit of k2 and shift k2 right by 1 *)
          coq:(cmd.call [] "shift_scalar"
                 [expr.var "cond2"; expr.var "pk2"]);

          (* Conditional add P to output:
             aux = cond1 ? P : identity; out = out + aux *)
          coq:(cmd.call [] "store_zero"
                 [expr.var "auxx"; expr.var "auxy"; expr.var "auxz"]);
          coq:(cmd.call [] group_cmov_alt
                 [expr.var "auxx"; expr.var "auxy"; expr.var "auxz";
                  expr.var "auxx"; expr.var "auxy"; expr.var "auxz";
                  expr.var "px"; expr.var "py"; expr.var "pz";
                  expr.var "cond1"]);
          coq:(cmd.call [] curve_add_name
                 [expr.var "outx"; expr.var "auxx";
                  expr.var "outy"; expr.var "auxy";
                  expr.var "outz"; expr.var "auxz";
                  expr.var "outx"; expr.var "outy"; expr.var "outz"]);

          (* Conditional add phi(P) to output:
             aux = cond2 ? phi(P) : identity; out = out + aux *)
          coq:(cmd.call [] "store_zero"
                 [expr.var "auxx"; expr.var "auxy"; expr.var "auxz"]);
          coq:(cmd.call [] group_cmov_alt
                 [expr.var "auxx"; expr.var "auxy"; expr.var "auxz";
                  expr.var "auxx"; expr.var "auxy"; expr.var "auxz";
                  expr.var "phix"; expr.var "phiy"; expr.var "phiz";
                  expr.var "cond2"]);
          coq:(cmd.call [] curve_add_name
                 [expr.var "outx"; expr.var "auxx";
                  expr.var "outy"; expr.var "auxy";
                  expr.var "outz"; expr.var "auxz";
                  expr.var "outx"; expr.var "outy"; expr.var "outz"]);

          (* Double P: px = 2*px via curve_add(px, px) *)
          coq:(cmd.call [] curve_add_name
                 [expr.var "px"; expr.var "px";
                  expr.var "py"; expr.var "py";
                  expr.var "pz"; expr.var "pz";
                  expr.var "px"; expr.var "py"; expr.var "pz"]);

          (* Double phi(P): phix = 2*phix via curve_add(phix, phix) *)
          coq:(cmd.call [] curve_add_name
                 [expr.var "phix"; expr.var "phix";
                  expr.var "phiy"; expr.var "phiy";
                  expr.var "phiz"; expr.var "phiz";
                  expr.var "phix"; expr.var "phiy"; expr.var "phiz"])
        }
      ))).

  (* ================================================================== *)
  (** * Section 3: WP specification                                     *)
  (* ================================================================== *)

  Local Notation eval n x := (Positional.eval (uweight width) n (List.map word.unsigned x)).

  Instance spec_of_glv_shamir : spec_of "bls12_glv_shamir" :=
    fnspec! "bls12_glv_shamir"
      (pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2 : word)
      / (Outx Outy Outz Px Py Pz Phix Phiy Phiz : F)
        (k1_words k2_words : list word) R,
      { requires tr mem :=
          (FElem (Some tight_bounds) pOutx Outx
           * FElem (Some tight_bounds) pOuty Outy
           * FElem (Some tight_bounds) pOutz Outz
           * FElem (Some tight_bounds) pPx Px
           * FElem (Some tight_bounds) pPy Py
           * FElem (Some tight_bounds) pPz Pz
           * FElem (Some tight_bounds) pPhix Phix
           * FElem (Some tight_bounds) pPhiy Phiy
           * FElem (Some tight_bounds) pPhiz Phiz
           * Bignum.Bignum glv_scalar_words pk1 k1_words
           * Bignum.Bignum glv_scalar_words pk2 k2_words
           * R)%sep mem
      ;
        ensures tr' mem' :=
          tr = tr'
          /\ exists Outxnew Outynew Outznew
                    Pxnew Pynew Pznew
                    Phixnew Phiynew Phiznew : F,
             exists k1new k2new : list word,
               (* The output is the Shamir double-scalar multiplication.
                  Using LSB-first accumulation, the result is:
                    out = [k1]P + [k2]phi(P)
                  where k1 = eval(k1_words) and k2 = eval(k2_words).

                  Specifically, the loop invariant ensures:
                    out   = scmul_glv(k1 mod 2^iter, P_init)
                              + scmul_glv(k2 mod 2^iter, phi(P_init))
                    P     = scmul_glv(2^iter, P_init)
                    phi   = scmul_glv(2^iter, phi(P_init))
                  After 129 iterations with k1, k2 < 2^129:
                    out = [k1]P_init + [k2]phi(P_init) *)
               let k1_val := Z.to_nat (eval glv_scalar_words k1_words) in
               let k2_val := Z.to_nat (eval glv_scalar_words k2_words) in
               (Outxnew, Outynew, Outznew) =
                 curve_add (scmul_glv k1_val (Px, Py, Pz))
                           (scmul_glv k2_val (Phix, Phiy, Phiz))
               /\ (FElem (Some tight_bounds) pOutx Outxnew
                  * FElem (Some tight_bounds) pOuty Outynew
                  * FElem (Some tight_bounds) pOutz Outznew
                  * FElem (Some tight_bounds) pPx Pxnew
                  * FElem (Some tight_bounds) pPy Pynew
                  * FElem (Some tight_bounds) pPz Pznew
                  * FElem (Some tight_bounds) pPhix Phixnew
                  * FElem (Some tight_bounds) pPhiy Phiynew
                  * FElem (Some tight_bounds) pPhiz Phiznew
                  * Bignum.Bignum glv_scalar_words pk1 k1new
                  * Bignum.Bignum glv_scalar_words pk2 k2new
                  * R)%sep mem'}.

  (* ================================================================== *)
  (** * Section 4: Loop invariant                                       *)
  (* ================================================================== *)

  (** The LSB-first Shamir loop invariant.

      After [iter] iterations (iter = 0, 1, ..., 129):
      - k1_current = k1_init >> iter  (remaining bits of k1)
      - k2_current = k2_init >> iter  (remaining bits of k2)
      - out = scmul_glv(k1_init mod 2^iter, P_init)
              + scmul_glv(k2_init mod 2^iter, phi_init)
              (accumulated result from processed bits)
      - P_current = scmul_glv(2^iter, P_init)
              = [2^iter]P_init (doubled iter times)
      - phi_current = scmul_glv(2^iter, phi_init)
              = [2^iter]phi_init (doubled iter times)

      This follows the LoopBody.v pattern extended to two scalars. *)

  Definition glv_loop_inv
    (pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz : word)
    (pk1 pk2 : word) (a_auxx a_auxy a_auxz a_cond1 a_cond2 a_iter : word)
    (Px_init Py_init Pz_init Phix_init Phiy_init Phiz_init : F)
    (k1_init k2_init : Z)
    (R : mem -> Prop) (tr : Semantics.trace)
    (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
    t = tr /\
    exists (Outx Outy Outz Px Py Pz Phix Phiy Phiz
            Auxx Auxy Auxz : F)
           (k1_words k2_words : list word)
           (c1 c2 : word) (iter_word : word),
      let iter := (129 - Z.of_nat v)%Z in
      (* Scalar invariants *)
      eval glv_scalar_words k1_words = Z.shiftr k1_init iter
      /\ eval glv_scalar_words k2_words = Z.shiftr k2_init iter
      (* Accumulator invariant *)
      /\ (Outx, Outy, Outz) =
           curve_add
             (scmul_glv (Z.to_nat (k1_init mod 2 ^ iter)) (Px_init, Py_init, Pz_init))
             (scmul_glv (Z.to_nat (k2_init mod 2 ^ iter)) (Phix_init, Phiy_init, Phiz_init))
      (* Point doubling invariants *)
      /\ (Px, Py, Pz) = scmul_glv (Z.to_nat (2 ^ iter)) (Px_init, Py_init, Pz_init)
      /\ (Phix, Phiy, Phiz) = scmul_glv (Z.to_nat (2 ^ iter)) (Phix_init, Phiy_init, Phiz_init)
      (* Memory layout *)
      /\ (FElem (Some tight_bounds) pOutx Outx
         * FElem (Some tight_bounds) pOuty Outy
         * FElem (Some tight_bounds) pOutz Outz
         * FElem (Some tight_bounds) pPx Px
         * FElem (Some tight_bounds) pPy Py
         * FElem (Some tight_bounds) pPz Pz
         * FElem (Some tight_bounds) pPhix Phix
         * FElem (Some tight_bounds) pPhiy Phiy
         * FElem (Some tight_bounds) pPhiz Phiz
         * FElem None a_auxx Auxx
         * FElem None a_auxy Auxy
         * FElem None a_auxz Auxz
         * Bignum.Bignum glv_scalar_words pk1 k1_words
         * Bignum.Bignum glv_scalar_words pk2 k2_words
         * scalar a_cond1 c1
         * scalar a_cond2 c2
         * scalar a_iter iter_word
         * R)%sep m
      (* Locals bindings *)
      /\ map.get l "outx" = Some pOutx
      /\ map.get l "outy" = Some pOuty
      /\ map.get l "outz" = Some pOutz
      /\ map.get l "px" = Some pPx
      /\ map.get l "py" = Some pPy
      /\ map.get l "pz" = Some pPz
      /\ map.get l "phix" = Some pPhix
      /\ map.get l "phiy" = Some pPhiy
      /\ map.get l "phiz" = Some pPhiz
      /\ map.get l "pk1" = Some pk1
      /\ map.get l "pk2" = Some pk2
      /\ map.get l "auxx" = Some a_auxx
      /\ map.get l "auxy" = Some a_auxy
      /\ map.get l "auxz" = Some a_auxz
      /\ map.get l "cond1" = Some a_cond1
      /\ map.get l "cond2" = Some a_cond2
      /\ map.get l "iter" = Some a_iter
      /\ word.unsigned iter_word = iter
      (* Measure: v counts down from 129 to 0 *)
      /\ v = Z.to_nat (glv_iterations - iter).

  Opaque felem_size_in_bytes.
  Opaque Memory.bytes_per_word.
  Opaque Z.of_nat.
  Opaque glv_scalar_words.
  Opaque glv_iterations.

  (* ================================================================== *)
  (** * Section 5: Correctness lemma                                    *)
  (* ================================================================== *)

  (** Resolve map.get on abstract locals using hypotheses *)
  Local Ltac resolve_map_get :=
    match goal with
    | |- map.get (map.put ?m ?k ?v) ?k' = Some ?e =>
      first
      [ unify k k';
        rewrite map.get_put_same; exact eq_refl
      | rewrite map.get_put_diff by congruence;
        resolve_map_get ]
    | |- map.get ?m ?k = Some ?e =>
      first
      [ assumption
      | match goal with
        | H : map.get m k = Some _ |- _ => exact H
        end ]
    end.

  (** Evaluate dexprs with abstract locals *)
  Local Ltac eval_dexprs_abstract :=
    cbv [dexprs list_map list_map_body
         WeakestPrecondition.expr WeakestPrecondition.expr_body
         WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet];
    repeat (first
      [ exact eq_refl
      | eexists; split; [resolve_map_get |]
      | eexists; split; [exact eq_refl |]
      ]).

  (** Process cmd.seq/set with abstract locals *)
  Local Ltac glv_straightline :=
    match goal with
    | |- WeakestPrecondition.cmd _ (cmd.seq _ _) _ _ _ _ =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body]
    | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      letexists; split; [solve [eval_dexprs_abstract] |]
    | |- WeakestPrecondition.cmd _ cmd.skip _ _ _ ?post =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body]
    end.

  (** The WP proof for the GLV Shamir function.

      PROOF STRATEGY:
      1. Function entry: start_func, process 6 stackallocs
         (3 felem + 3 word-sized), convert anybytes to FElem/scalar.
      2. Initialization: process store_zero(outx,outy,outz) call,
         then store iter=0.
      3. While loop: apply Loops.while_localsmap with glv_loop_inv.
      4. Loop body: 11 calls per iteration.
      5. Post-loop: stack deallocation + postcondition.

      Callee specs are taken as hypotheses since this is in a
      generic section.  The function body uses:
        "store_zero"    -- literal string
        "shift_scalar"  -- literal string
        group_cmov_alt  -- section variable
        curve_add_name  -- section variable *)

  Lemma glv_shamir_ok :
    forall functions
      (EnvContains : map.get functions "bls12_glv_shamir" =
         Some (snd glv_shamir_func))
      (HStoreZero : @StoreZero.spec_of_store_zero
         _ _ _ _ _ _ field_parameters field_representation functions)
      (HShiftScalar : spec_of_shift_scalar functions)
      (HCmovAlt : @CondMoveGroup.spec_of_group_cmov_alt
         _ _ _ _ _ _ field_parameters field_representation
         group_cmov_alt functions)
      (HCurveAdd : @CurveAdd.spec_of_ladderstep
         _ _ _ _ _ _ field_parameters field_representation
         three_b functions),
    spec_of_glv_shamir functions.
  Proof.
    intros.
    unfold spec_of_glv_shamir.
    intros pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
           Outx Outy Outz Px Py Pz Phix Phiy Phiz
           k1_words k2_words R tr mem0 Hsep.

    (* === Phase 1: Function entry === *)
    eapply WeakestPreconditionProperties.start_func;
      [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold glv_shamir_func. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* === Phase 2: Process 6 stackallocs === *)
    (* Stackalloc 1: auxx (felem-sized) *)
    repeat straightline.
    split. { apply felem_size_in_bytes_mod. }
    intros a_auxx mStack_auxx mComb_auxx Hany_auxx Hsplit_auxx.
    repeat straightline.

    (* Stackalloc 2: auxy (felem-sized) *)
    split. { apply felem_size_in_bytes_mod. }
    intros a_auxy mStack_auxy mComb_auxy Hany_auxy Hsplit_auxy.
    repeat straightline.

    (* Stackalloc 3: auxz (felem-sized) *)
    split. { apply felem_size_in_bytes_mod. }
    intros a_auxz mStack_auxz mComb_auxz Hany_auxz Hsplit_auxz.
    repeat straightline.

    (* Stackalloc 4: cond1 (word-sized) *)
    split. { apply Z_mod_same_full. }
    intros a_cond1 mStack_cond1 mComb_cond1 Hany_cond1 Hsplit_cond1.
    repeat straightline.

    (* Stackalloc 5: cond2 (word-sized) *)
    split. { apply Z_mod_same_full. }
    intros a_cond2 mStack_cond2 mComb_cond2 Hany_cond2 Hsplit_cond2.
    repeat straightline.

    (* Stackalloc 6: iter (word-sized) *)
    split. { apply Z_mod_same_full. }
    intros a_iter mStack_iter mComb_iter Hany_iter Hsplit_iter.

    (* Convert felem anybytes to FElem None using P_from_bytes from felem_alloc.
       P_from_bytes : forall px, impl1 (anybytes px sz) (ex1 (FElem None px))
       i.e., forall px m, anybytes px sz m -> exists x, FElem None px x m *)
    pose proof (P_from_bytes a_auxx mStack_auxx Hany_auxx)
      as [Auxx_init Hfe_auxx].
    pose proof (P_from_bytes a_auxy mStack_auxy Hany_auxy)
      as [Auxy_init Hfe_auxy].
    pose proof (P_from_bytes a_auxz mStack_auxz Hany_auxz)
      as [Auxz_init Hfe_auxz].

    (* Convert word-sized anybytes to scalars *)
    apply anybytes_to_scalar in Hany_cond1 as [c1_init Hsc_cond1].
    apply anybytes_to_scalar in Hany_cond2 as [c2_init Hsc_cond2].
    apply anybytes_to_scalar in Hany_iter as [iter_init Hsc_iter].

    (* === Phase 3+4+5+6: store_zero init, while loop, post-loop ===

       After 6 stackallocs, the goal is a WP for:
         cmd.seq (cmd.call "store_zero" [outx;outy;outz])
           (cmd.seq (cmd.store iter 0) (cmd.while ...))
       wrapped in 6 stack dealloc continuations.

       Phase 3: Process store_zero(outx,outy,outz) + store(iter,0).
       Phase 4: Apply Loops.while_localsmap with glv_loop_inv.
       Phase 5: Loop body (11 calls per iteration × 129 iterations).
       Phase 6: Post-loop stack deallocation + final postcondition.

       The proof strategy follows BLS12_MillerLoop.v:
       - Phase 3: straightline for cmd.seq, manual args+dexprs for the call,
         weaken_call + HStoreZero, then straightline for the store.
       - Phase 4: eapply Loops.while_localsmap with measure=129,
         invariant=glv_loop_inv. Prove well_founded, initial invariant,
         and the combined body+post-loop goal.
       - Phase 5 (loop body): For each of 11 calls per iteration,
         use gcall (unfold cmd.seq, expose cmd.call, eval dexprs,
         weaken_call + spec, destruct postcondition). Then re-establish
         the loop invariant with measure vi-1.
       - Phase 6 (post-loop): 6 stack deallocations (reverse order:
         iter, cond2, cond1, auxz, auxy, auxx). Each deallocation:
         split sep to isolate stack buffer, convert FElem→anybytes
         or scalar→anybytes, provide split witness. Then final
         postcondition: existentials for output values + sep.

       === Detailed Phase 5 structure (per iteration) ===

       Given invariant at measure vi (where vi = glv_iterations - iter):
       1. Evaluate branch condition: load(iter) < 129
       2. TRUE branch (vi > 0):
          a. cmd.store iter (iter+1)     -- increment counter
          b. shift_scalar(cond1, pk1)    -- extract k1 low bit
          c. shift_scalar(cond2, pk2)    -- extract k2 low bit
          d. store_zero(auxx,auxy,auxz)  -- zero aux point
          e. group_cmov_alt(aux,aux,P,cond1) -- aux = cond1 ? P : O
          f. curve_add(out,aux,out)      -- out += (cond1 ? P : O)
          g. store_zero(auxx,auxy,auxz)  -- zero aux point
          h. group_cmov_alt(aux,aux,phi,cond2) -- aux = cond2 ? phi : O
          i. curve_add(out,aux,out)      -- out += (cond2 ? phi : O)
          j. curve_add(P,P,P)            -- double P
          k. curve_add(phi,phi,phi)      -- double phi
          Then re-establish invariant at measure vi-1.
       3. FALSE branch (vi = 0):
          Post-loop: 6 deallocs + postcondition.

       === Key arithmetic for invariant restoration ===

       After iteration, with iter_new = iter + 1:
       - k1_new = k1_old >> 1, so k1_new = k1_init >> iter_new
       - k2_new = k2_old >> 1, so k2_new = k2_init >> iter_new
       - bit1 = k1_old mod 2 = (k1_init >> iter) mod 2
                              = Z.testbit k1_init iter
       - out_new = curve_add (curve_add out_old (cond1 ? P_old : O))
                             (cond2 ? phi_old : O)
         which equals curve_add
           (scmul_glv (k1_init mod 2^iter_new) P_init)
           (scmul_glv (k2_init mod 2^iter_new) phi_init)
         by decomposing k_init mod 2^(iter+1) = 2*(k_init mod 2^iter) + bit
         and using scmul_glv properties.
       - P_new = curve_add P_old P_old = scmul_glv (2^iter_new) P_init
       - phi_new = curve_add phi_old phi_old = scmul_glv (2^iter_new) phi_init

       All of this is mechanical Z arithmetic + scmul_glv unfolding. *)

    (* === Phase 3: Process store_zero + store(iter,0) ===

       Pattern (following MillerLoop.v):
       1. repeat straightline — processes cmd.seq wrappers
       2. straightline_call — processes the store_zero call
          (resolves dexprs, finds spec_of_store_zero via HStoreZero,
           applies it, ecancel_assumption handles FElem bounds)
       3. repeat straightline — processes store(iter,0) and any remaining seq

       Note: straightline_call requires spec_of "store_zero" to be
       findable as a typeclass instance in the context. HStoreZero
       provides this. The precondition (FElem None) is resolved from
       FElem (Some tight_bounds) via drop_bounds_FElem in ecancel_impl. *)

    (* === Phase 4: Apply Loops.while_localsmap ===

       eapply Loops.while_localsmap with:
       - v0 := 129 (initial measure = glv_iterations)
       - lt := Nat.lt, Hwf := lt_wf
       - invariant := glv_loop_inv pOutx...pk2 a_auxx...a_iter
                        Px Py Pz Phix Phiy Phiz
                        (eval k1_words) (eval k2_words) R tr

       Subgoal 1 (well_founded): exact lt_wf.
       Subgoal 2 (initial invariant at v0=129):
         Existentials: Out=(Fzero,Fone,Fzero), P/phi/aux/k/cond/iter from context.
         Z.shiftr k 0 = k, k mod 2^0 = 0, scmul_glv 0 = identity,
         2^0 = 1, scmul_glv 1 P = P. Sep from post-store_zero state.
       Subgoal 3: combined body + post-loop (see Phase 5/6). *)

    (* === Phase 5: Loop body (inside while_localsmap body goal) ===

       Given: invariant vi ti mi li (with vi > 0 in TRUE branch).
       Destruct invariant into components.
       Provide branch value: word.b2w (word.ltu iw_i (word.of_Z 129)).
       Evaluate branch expression (load "iter" from memory, compare with 129).

       TRUE branch: process 11 calls per iteration.
       Define local tactic gcall (like mcall in MillerLoop.v):
         try glv_straightline;                         (* peel cmd.seq *)
         unfold1_cmd_goal; cbv beta match delta [cmd_body]; (* expose call *)
         letexists; split; [solve [eval_dexprs_abstract] |]; (* args+dexprs *)
         eapply Semantics.weaken_call;
         [ eapply spec; ecancel_assumption             (* call spec *)
         | cbv beta; intros ? ? ? ?; subst;
           cbv [map.putmany_of_list_zip];
           eexists; split; [exact eq_refl |] ].        (* postcond *)

       Call sequence:
       1. cmd.store iter (load(iter)+1)  -- manual straightline
       2. gcall HShiftScalar             -- shift_scalar(cond1, pk1)
       3. gcall HShiftScalar             -- shift_scalar(cond2, pk2)
       4. gcall HStoreZero               -- store_zero(aux)
       5. gcall HCmovAlt                 -- group_cmov_alt(aux,aux,P,cond1)
       6. gcall HCurveAdd                -- curve_add(out,aux,out)
       7. gcall HStoreZero               -- store_zero(aux)
       8. gcall HCmovAlt                 -- group_cmov_alt(aux,aux,phi,cond2)
       9. gcall HCurveAdd                -- curve_add(out,aux,out)
       10. gcall HCurveAdd               -- curve_add(P,P,P)
       11. gcall HCurveAdd               -- curve_add(phi,phi,phi)

       Then re-establish invariant at (vi - 1):
       exists (vi - 1). split; [| lia].
       unfold glv_loop_inv. split; [reflexivity |].
       Provide existentials. Prove conjuncts:
       - Scalar: Z.shiftr arithmetic
       - Accumulator: scmul_glv decomposition
       - Point doubling: scmul_glv 2*n = curve_add (scmul n) (scmul n)
       - Sep: ecancel_assumption
       - Locals: resolve_map_get for each variable *)

    (* === Phase 6: Post-loop (FALSE branch, vi = 0) ===

       6 stack deallocations in reverse order.
       Each deallocation (following MillerLoop.v lines 1735-1790):

       (* --- Dealloc level N: name (type) --- *)
       eassert (H : (_ * FElem/scalar addr val) m).
       { pose proof Hsep as H'. ecancel_assumption. }
       destruct H as [mRest [mStack [[Heq Hd] [Hrest Hfelem]]]].
       exists mRest, mStack.
       split. { exact (FElem_to_bytes addr val mStack Hfelem).
                -- or: exact (scalar_to_anybytes ...). }
       split. { split; [exact Heq | exact Hd]. }

       Dealloc order: iter, cond2, cond1, auxz, auxy, auxx.

       Final postcondition:
       cbv [list_map list_map_body].
       split. { exact eq_refl. }  (* rets = [] *)
       split. { exact eq_refl. }  (* tr = tr' *)
       exists Outx_i, Outy_i, Outz_i, Px_i, Py_i, Pz_i,
              Phix_i, Phiy_i, Phiz_i, k1w_i, k2w_i.
       split.
       { (* Output = curve_add(scmul k1 P)(scmul k2 phi) *)
         (* From Hout_i with vi=0: iter=129, so
            k_init mod 2^129 = k_init for k < 2^129. *)
         exact Hout_i. (* after simplifying 129-0=129 *) }
       ecancel_assumption. *)

    admit.
  Admitted.

End GLV_Shamir_Generic.

(* ================================================================== *)
(** * Section 6: BLS12-381 instantiation                               *)
(* ================================================================== *)

(** To instantiate for BLS12-381:

    Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_G1.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
    Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_three_b.
    Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
    Require Import coqutil.Word.Bitwidth64.
    Require Import bedrock2.BasicC64Semantics.

    Definition bls12_glv_shamir :=
      @glv_shamir_func _ _ _ _ _ _ _ _ _ _
        bls12_field_parameters bls12_frep
        "group_cmov_alt" "store_zero"
        "curve_add" "bls12_three_b".

    The full program would link:
    - bls12_glv_shamir
    - curve_add (= bls12_G1_add from BLS12_G1.v)
    - store_zero
    - group_cmov_alt (= cmov_alt_func from CondMoveGroup.v)
    - shift_scalar (= shift_scalar from BignumShift.v, scalar_words:=2)
    - All Fp operations (mul, add, sub, opp, square, selectznz, felem_copy, ...)
    - zero, one (field constant loaders)

    The caller is responsible for:
    1. Reducing k mod r (via BLS12_ScalarReduce)
    2. Decomposing k into (k1, k2) via glv_decompose
    3. Computing phi(P) = (omega * P_x, P_y, P_z)
    4. Calling bls12_glv_shamir with the precomputed inputs
*)
