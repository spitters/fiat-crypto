Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Import SeparationLogic.
Section Test.
Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
