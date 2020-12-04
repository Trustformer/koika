Require Import Ensembles.

(* Standards *)
Inductive memory_model : Type :=
| RVWMO.

Inductive base_standard : Type :=
| RV32I
| RV64I.

Inductive extension : Type :=
| RVM
| RVA
| RVF
| RVD
| RVQ
| RVZiCSR
| RVZifencei.

(* Extensions *)
Definition extensionsSet := Ensemble extension.

(* ISA *)
Record ISA : Type := {
  ISA_memory_model: memory_model;
  ISA_base_standard : base_standard;
  ISA_activated_extensions : extensionsSet;
}.
