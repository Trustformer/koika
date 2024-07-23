Require Import SMTproofs.
Require Export Coq.extraction.Extraction.
From Coq.extraction Require Export
  ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt ExtrOcamlZInt.

Set Extraction Output Directory "extr".

Extraction Inline Types.argSigs.

Extract Constant Vect.index => int.
Extract Inductive Vect.index' => int [ "0" "Stdlib.succ" ]
                                  "(fun fthisone fanotherone n -> if n = 0 then fthisone () else fanotherone (n - 1))".
Extract Constant Vect.index_of_nat => "fun sz x -> if x < sz then Some x else None".
Extract Constant Vect.index_to_nat => "fun _ x -> x".
Extract Constant Vect.largest_index => "fun x -> x".

Separate Extraction RV32I.Sigma sf Maps.PTree.get Maps.PTree.elements
  sact_sstack_underflow
  sact_sstack_overflow
  sact_sstack_violation
  no_stack_violation add_ok
  decode_consistent_imm_type
  RV32I.Show_reg_t
  RV32I.Show_ext_fn_t.

