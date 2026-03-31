#!/bin/bash
COQC=/home/au528660/.opam/rocq-native/bin/coqc
COQLIB=/home/au528660/.opam/rocq-native/lib/coq/user-contrib
$COQC -q -native-compiler no -R src Crypto \
  -Q $COQLIB/Coqprime Coqprime \
  -Q $COQLIB/coqutil coqutil \
  -Q $COQLIB/Rupicola Rupicola \
  -Q $COQLIB/bedrock2 bedrock2 \
  src/Bedrock/Field/Synthesis/Examples/BLS12_GLV_ScalarMultBedrock.v
