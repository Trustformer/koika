(*! Definition of the available instruction types !*)

Require Import rv.Instructions.

Inductive i_type := RType | R4Type | IType | SType | BType | UType | JType.
