Inductive memory_model  := RVWMO.
Inductive base_standard := RV32I | RV64I.
Inductive extension     := RVM | RVA | RVF | RVD | RVQ | RVZiCSR | RVZifencei.

Record ISA := {
  ISA_memory_model  : memory_model;
  ISA_base_standard : base_standard;
  ISA_extensions    : list extension;
}.
