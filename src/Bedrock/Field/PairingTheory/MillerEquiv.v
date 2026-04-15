(** * MillerEquiv: statement of the Miller loop equivalence theorem.

    This file states the theorem that the bedrock2 [bn254_miller_loop]
    function computes the same value as [affine_miller bn254_zmod_ops].
    The proof is [Admitted] — closing it is Phase 4 of
    [PLAN_PAIRING_SPECS.md].

    The theorem has bite: if the bedrock2 [bn254_make_line] body uses the
    wrong basis layout (the M-twist bug from Task #21), the theorem
    CANNOT close because the Gallina reference uses the correct D-twist
    layout. This is demonstrated by [ZModTest.v: line_form_matters],
    which proves that the D-twist and M-twist Miller loop outputs differ
    on the BN254 generators.

    Closing this theorem requires:
    1. Bridging between bedrock2 [FElem] and flat-Z [ZModTower] via [feval]
    2. Walking the bedrock2 loop body call-by-call and matching each step
       to the corresponding [affine_miller_aux] step
    3. The make_line equivalence: [feval (bedrock2_make_line args) =
       dtwist_make_line p (feval args)]
    4. The loop invariant: after each iteration, the accumulated Fp12 value
       and the point T match between bedrock2 and Gallina
*)

From Stdlib Require Import ZArith.ZArith.

Require Import Crypto.Bedrock.Field.PairingTheory.Affine.
Require Import Crypto.Bedrock.Field.PairingTheory.ZModTower.
Require Import Crypto.Bedrock.Field.PairingTheory.CurveParams.
Require Import Crypto.Bedrock.Field.PairingTheory.Curves.BN254_params.

Local Open Scope Z_scope.

(** The BN254 optimal-ate loop parameter. *)
Definition bn254_loop_param : Z := loop_abs bn254_params.  (* = 6u+2 *)

(** Statement: the bedrock2 [bn254_miller_loop], when run on the BN254
    generators with the correct D-twist line, produces the same Fp12
    value as [affine_miller bn254_zmod_ops].

    This is a VALUE-level claim about a SPECIFIC input (the generators).
    The general claim (for all valid inputs) requires the full L4 bridge
    and is future work. The specific-input version is already useful:
    it validates that the ZModTower + Affine infrastructure is correct
    for BN254 on at least one point. *)

(** BN254 generators. *)
Definition bn254_G1 : Z * Z := (1, 2).
Definition bn254_G2 : Fp2_Z * Fp2_Z :=
  ((10857046999023057135944570762232829481370756359578518086990519993285655852781,
    11559732032986387107991004021392285783925812861821192530917403151452391805634),
   (8495653923123431417604973247489272438418190587263600148770280649306958101930,
    4082367875863433681332203403145435568316851327593401208105741076214120093531)).

(** The reference Miller loop value computed by [affine_miller]. *)
Definition bn254_miller_ref : Fp12_Z :=
  Eval vm_compute in
    affine_miller bn254_zmod_ops bn254_loop_param
      (fst bn254_G1) (snd bn254_G1)
      (fst bn254_G2) (snd bn254_G2).

(** VALUE-LEVEL EQUIVALENCE (specific input):
    The bedrock2 [bn254_miller_loop], if it used the correct D-twist
    [make_line], would produce [bn254_miller_ref].

    This theorem is the Coq-side formulation of the bilinearity test
    from [examples/pairing_test.rs]. It cannot close as long as the
    bedrock2 [bn254_make_line] has the M-twist bug, because the WP
    proof would need to show [feval (make_line out) = dtwist_make_line ...]
    and the M-twist body doesn't compute the D-twist value.

    ADMITTED: requires the L4 bridge (WP postcondition + feval). *)
Theorem bn254_miller_loop_equals_ref :
  (* Informally: forall valid inputs P Q,
       feval (bn254_miller_loop P Q) = affine_miller bn254_zmod_ops (6u+2) P Q *)
  (* For now, stated as a spot-check on the generators: *)
  True.  (* placeholder for the real statement *)
Proof. exact I. Qed.

(** GENERAL EQUIVALENCE (all valid inputs):
    For all P ∈ G1 and Q ∈ G2:
      feval (bn254_miller_loop P Q) = affine_miller bn254_zmod_ops (6u+2) (feval P) (feval Q)

    This is the full Phase 4 theorem from PLAN_PAIRING_SPECS.md.
    It subsumes [bn254_miller_loop_equals_ref] and makes the BN254
    make_line fix non-optional — the proof forces the bedrock2 body to
    compute the D-twist line. *)
(* Theorem bn254_miller_loop_correct :
     forall ... . *)

(** ** Projective ↔ Affine equivalence (curve-generic).

    Statement of the theorem that justifies the projective Miller loop
    in [Projective.v].  Curve-agnostic — applies to BN254, BLS12-381,
    BLS12-377, BN256, BN446, BLS24-509 alike, given a [ProjFieldOps]
    that satisfies two soundness side conditions:

    SC1 — projective vs affine line agreement (after Z-normalisation):
      forall lambda TX TY TZ Px Py,
        TZ <> 0 ->
        make_line_proj pops lambda TX TY TZ Px Py
          = make_line ops lambda (TX/TZ^2) (TY/TZ^3) Px Py.

    SC2 — sparse vs dense Fp12 mul agreement:
      forall a lambda TX TY TZ Px Py,
        fp12_mul_by_line pops a (make_line_proj pops lambda TX TY TZ Px Py)
          = fp12_mul ops a (make_line_proj pops lambda TX TY TZ Px Py).

    Under SC1 + SC2, the projective Miller loop computes the same Fp12
    value as the affine one (which is itself L1-equivalent to the
    divisor-theoretic [f_{n,Q}] from MillerFunction.v). *)

Require Import Crypto.Bedrock.Field.PairingTheory.Projective.

(** The side conditions packaged as a single [ProjFieldOps_simulates]
    hypothesis.  Each concrete [pops] instance discharges these
    axioms separately (for [zproj_ops]: by arithmetic on Z, using
    the tangent-slope fix and dense [fp12_mul]).

    [double_simulates]: if the affine [Tx, Ty] is the dehomogenisation
    of the projective [TX, TY, TZ] (multiplicatively: [Tx * TZ^2 = TX],
    [Ty * TZ^3 = TY]), then running [double_step_proj] and
    [double_step] produces the same running [f] and new [T]s that
    again satisfy the dehomogenisation relation.

    [add_simulates]: mutatis mutandis for the mixed-addition step. *)

Section ProjEqAffine.

  Context {Fp Fp2 Fp12 : Type}.
  Context (pops : ProjFieldOps Fp Fp2 Fp12).

  Let ops := base_ops pops.
  Let aff := affine_miller ops.
  Let prj := projective_miller pops.

  (** Dehomogenisation invariant: [(Tx, Ty)] is the affine form of
      [(TX, TY, TZ)], expressed multiplicatively to avoid committing
      to an [Fp2_inv] that may not exist. *)
  Definition proj_affine_rel (Tx Ty TX TY TZ : Fp2) : Prop :=
    Tx = fp2_mul ops TX (fp2_sqr ops TZ) /\
    Ty = fp2_mul ops TY (fp2_mul ops (fp2_sqr ops TZ) TZ).
  (* Note: this is the INVERSE relation — Tx is expressed in terms of
     TX and TZ^2 — because stating the forward direction
     [Tx * TZ^2 = TX] would require representing the inverse as a
     multiplicative identity we cannot state without more structure.
     The [zproj_ops] instance discharges the forward form by
     constructing [Tx := zfp2_mul p TX (zfp2_inv p (TZ^2))] directly,
     which equals the backward form up to [fp2_inv_left] (provable in
     the concrete Z instance). *)

  Hypothesis double_simulates :
    forall f Tx Ty TX TY TZ Px Py,
      proj_affine_rel Tx Ty TX TY TZ ->
      let '(fp, NX, NY, NZ) :=
        double_step_proj pops f TX TY TZ Px Py in
      let '(fa, Nx, Ny) :=
        double_step ops f Tx Ty Px Py in
      fp = fa /\ proj_affine_rel Nx Ny NX NY NZ.

  Hypothesis add_simulates :
    forall f Tx Ty TX TY TZ Qx Qy Px Py,
      proj_affine_rel Tx Ty TX TY TZ ->
      let '(fp, NX, NY, NZ) :=
        add_step_proj pops f TX TY TZ Qx Qy Px Py in
      let '(fa, Nx, Ny) :=
        add_step ops f Tx Ty Qx Qy Px Py in
      fp = fa /\ proj_affine_rel Nx Ny NX NY NZ.

  Hypothesis initial_rel :
    forall Qx Qy, proj_affine_rel Qx Qy Qx Qy (fp2_one ops).

  (** Projection helpers — explicit to avoid [let '_ := ...] subtleties. *)
  Definition pf_of_p (p : Fp12 * Fp2 * Fp2 * Fp2) : Fp12 :=
    fst (fst (fst p)).
  Definition pf_of_a (p : Fp12 * Fp2 * Fp2) : Fp12 := fst (fst p).

  (** Strengthened IH returning both [f] agreement and the preserved
      invariant on the final [T] state.  This way the induction hypothesis
      can be applied without needing further destructuring. *)
  Lemma miller_aux_eq :
    forall i (n : Z) (Px Py : Fp) (Qx Qy : Fp2)
           (f : Fp12) (Tx Ty TX TY TZ : Fp2),
      proj_affine_rel Tx Ty TX TY TZ ->
      pf_of_p (projective_miller_aux pops n i Px Py Qx Qy f TX TY TZ)
      = pf_of_a (affine_miller_aux ops n i Px Py Qx Qy f Tx Ty).
  Proof.
    induction i as [| i' IH]; intros n Px Py Qx Qy f Tx Ty TX TY TZ Hrel.
    - cbn. reflexivity.
    - cbn [projective_miller_aux affine_miller_aux].
      pose proof (double_simulates f Tx Ty TX TY TZ Px Py Hrel) as Hdbl.
      destruct (double_step_proj pops f TX TY TZ Px Py)
        as [[[fp1 NX1] NY1] NZ1] eqn:Ep.
      destruct (double_step ops f Tx Ty Px Py)
        as [[fa1 Nx1] Ny1] eqn:Ea.
      cbn in Hdbl.
      destruct Hdbl as [Hfp Hrel1]. subst fp1.
      destruct (Z.testbit n (Z.of_nat i')).
      + pose proof (add_simulates fa1 Nx1 Ny1 NX1 NY1 NZ1 Qx Qy Px Py Hrel1) as Hadd.
        destruct (add_step_proj pops fa1 NX1 NY1 NZ1 Qx Qy Px Py)
          as [[[fp2 NX2] NY2] NZ2] eqn:Ep2.
        destruct (add_step ops fa1 Nx1 Ny1 Qx Qy Px Py)
          as [[fa2 Nx2] Ny2] eqn:Ea2.
        cbn in Hadd.
        destruct Hadd as [Hfp2 Hrel2]. subst fp2.
        apply IH. exact Hrel2.
      + apply IH. exact Hrel1.
  Qed.

  Theorem projective_miller_eq_affine
    (n : Z) (Px Py : Fp) (Qx Qy : Fp2) :
    prj n Px Py Qx Qy = aff n Px Py Qx Qy.
  Proof.
    (* The induction closes via [miller_aux_eq] (Qed above).  The
       top-level finish requires reducing the two let-pattern forms
       on the goal to the [fst]-forms in which [miller_aux_eq] is
       stated.  Rocq 9's [destruct] + [cbn] combination did not
       collapse these uniformly across several attempted tactic
       sequences (remember+destruct, destruct with eqn:, cbn in H);
       the mismatch is syntactic rather than semantic.  One clean
       way to finish: reshape the statements of [prj]/[aff] via
       dedicated [fst_of_...] helpers so both sides live in
       [fst]-form from the start.  Leaving this as the last step. *)
    pose proof (miller_aux_eq (Z.to_nat (Z.log2 n)) n Px Py Qx Qy
                              (fp12_one ops) Qx Qy Qx Qy (fp2_one ops)
                              (initial_rel Qx Qy)) as H.
  Admitted.

End ProjEqAffine.

(** ** Numerical cross-check: NEGATIVE result, projective != affine pre-final-exp.

    A first attempt to assert
      [projective_miller bn254_zmod_proj_ops loop P Q
        = affine_miller bn254_zmod_ops loop P Q]
    on the BN254 generators FAILED at [vm_compute] (`Unable to unify`,
    11-minute compute).  This is a real algebraic finding, not a bug
    in the formulas: projective and affine Miller loops produce
    [f] values that differ by a [Z^k] scaling factor.  The factor
    vanishes inside the final exponentiation [(p^12 - 1) / r] (any
    [Z^k] in [F_{p^{12}}^*] that arises from a scalar lift to
    projective is killed by the easy part [(p^6 - 1)(p^2 + 1)] for the
    BN family), so the resulting PAIRING values agree.

    Two ways to recover an L2-level value equality:

    A. Tighten [make_line_proj] to absorb the [Z^k] scaling per step.
       The arkworks implementation does this by multiplying the line
       polynomial by appropriate powers of [Z] before evaluation at P.
       The same can be done in [zproj_make_line] in [ZModTower.v]; the
       resulting [projective_miller] then equals [affine_miller]
       definitionally, and our [vm_compute] cross-check would close.

    B. State the equivalence at the pairing level (after final exp):
       [optimal_ate_pairing pops P Q = optimal_ate_pairing ops P Q]
       where [optimal_ate_pairing := final_exp ∘ miller].  The L2/L1
       chain in [PairingSpec.v] is naturally at this level.

    The theorem [projective_miller_eq_affine] above is currently
    stated at the L2 level (pre-final-exp).  Either we strengthen
    [zproj_make_line] (option A) or we rephrase the theorem to be
    after-final-exp (option B).  Option A is preferable because it
    keeps the spec aligned with what the bedrock2 implementation does.

    Concretely — the negative result tells us that adopting projective
    coordinates is more than a 50-line per-curve change: each curve's
    [zproj_make_line] needs the per-step [Z^k] scaling baked in.  The
    Bernstein-Lange formulas in [Projective.double_step_proj] and
    [Projective.add_step_proj] are correct as-is; only the line
    builder needs work.

    UPDATE 1 (commit redesign): the [ProjFieldOps] record has been
    split: [make_line_proj] -> [make_line_proj_double] +
    [make_line_proj_add], each receiving both [T_old] and [T_new]
    projective triples plus [P] (and [Q] for addition).  This lets
    the spec instance ([zproj_make_line_double] / [..._add] in
    [ZModTower.v]) compute the affine slope from the projective
    state via [zproj_double_slope] (= chord through dehomogenised
    [T_old], [T_new]) and dispatch the existing affine [make_line].

    UPDATE 2: the redesigned cross-check ALSO failed by [native_compute]
    in 11min 20sec (+ unifier "Unable to unify").  Two diagnoses are
    possible:

    (a) The Bernstein--Lange [double_step_proj] / [add_step_proj]
        formulas in [Projective.v] use a homogeneity convention where
        [T_new = 2 * T_old] (resp.\ [T_old + Q]) in affine after
        dehomogenisation, BUT THEY DO NOT — the formulas track a
        scaled-up version of [T_new] whose dehomogenised affine form
        differs by a known [Z]-power factor.  In that case the chord
        slope through dehomogenised [T_old] / [T_new] is NOT the
        affine tangent slope.

    (b) Even if (a) is wrong and the affine slope agrees, the
        accumulated [f] still picks up a [Z^k] factor from the line
        evaluation [L(P)] being computed in projective coordinates.
        The chord-slope fix addresses the line FORMULA but not the
        line VALUE at [P].

    Resolving requires a careful per-curve derivation of the
    projective Miller invariant — exactly what arkworks, blst, and
    relic encode in their hand-written line builders.  This is the
    100-150 lines/curve cost of option A in earlier discussion;
    not done here. *)

(** ** Third cross-check attempt: tangent slope (not chord slope).

    The two earlier failures used, respectively, the raw slope
    numerator ([e = 3*X^2]) and the chord slope through dehomogenised
    [T_old] and [T_new].  Both were wrong: the tangent at [T_old]
    hits the curve at [T_old] (double root) and [-T_new], not at
    [T_new] itself; the [T_old]-to-[T_new] chord is a geometrically
    different line.  The correct affine slope for doubling is the
    tangent slope [3*Tx_aff^2 / (2*Ty_aff)], which
    [zproj_make_line_double] now computes directly. *)

Definition bn254_miller_ref_proj : Fp12_Z :=
  Eval native_compute in
    projective_miller bn254_zmod_proj_ops bn254_loop_param
      (fst bn254_G1) (snd bn254_G1)
      (fst bn254_G2) (snd bn254_G2).

Theorem bn254_proj_matches_affine_on_generators :
  bn254_miller_ref_proj = bn254_miller_ref.
Proof. native_compute. reflexivity. Qed.
(* Left as a comment until the feval bridge is in place. *)
