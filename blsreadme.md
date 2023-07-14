*** Points of interest:

** Printing code:

`src/Bedrock/Group/CurveAdd/Test.v`
`src/Bedrock/Group/CurveAdd/TestFp2.v`

The printed code is not valid C, but needs some minor editing; see

`src/Bedrock/Group/CurveAdd/c_test.c`
`src/Bedrock/Group/CurveAdd/c_G2_test.c`

for templates; these files also contains some simple testing of scalar
multiplication.

** Proofs and implementations

* Generic field operations specs

`src/Bedrock/Specs/Field.v`

* Generic field implementation synthesis (for base fields, not extensions)

`src/Bedrock/Field/Synthesis/New/Signature.v`
`src/Bedrock/Field/Interface/CompilationAbstract.v`

* Generic field implementation for (quadratic) extension fields

`src/Bedrock/Field/FieldExtensions/QuadraticFieldExtensions.v`

* Generic scalar mult

`src/Bedrock/Group/CurveAdd/ScalarMult.v`

* Generic loop body (of scalar mult)

`src/Bedrock/Group/CurveAdd/LoopBody.v`

* *Non-generic* (requires limb width 4) Bignum shift

`src/Bedrock/Group/CurveAdd/BignumShift.v`

* The constant "three b" for G1 (inherently non generic)

`src/Bedrock/Field/Synthesis/Examples/bls12_three_b.v`

* The constant "three b" for G2 (inherently non generic)

`src/Bedrock/Field/Synthesis/Examples/bls12_three_b_Fp2.v`

* Generic curve zero (i.e. point at infinity)

`src/Bedrock/Group/CurveAdd/StoreZero.v`

NB: the spec should be generalized to a generic group (using a Group
typeclass). See `src/Bedrock/Specs/Group.v` for some prelimenary
work.

* *Non-generic* copy of field element of bls12 prime field

`src/Bedrock/Field/Synthesis/Examples/bls12_felem_copy.v`

NB: this should be possible to generalize?

* Conditional move of curve point 

`src/Bedrock/Group/CurveAdd/CondMoveGroup.v`

NB: the spec should be generalized to a generic group (using a Group
typeclass). See `src/Bedrock/Specs/Group.v` for some prelimenary
work.

* Specialized proofs (of field operations and curve addition) to bls12 prime and extension field

This has been done to some degree in 
`Field/Synthesis/Examples/bls12_prime.v`
`Field/Synthesis/Examples/bls12_Fp2`
`Field/Synthesis/Examples/BLS12_G1.v`
`Field/Synthesis/Examples/BLS12_G2.v`
but these are somewhat outdated.

All generic proofs should be imported to these files and reproved,
instantiating primes and proving obligations.



