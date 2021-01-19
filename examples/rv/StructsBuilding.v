Require Import List.
Import ListNotations.

Require Import Koika.Frontend Koika.Std.

Require Import rv.ISA rv.Instructions rv.ModuleInstructions rv.IFields rv.ITypes rv.InstructionsProperties.

(* inst_field *)
Definition get_i_field_information_quantity (f : i_field) :=
  let fp := get_i_field_properties f in
  if (is_sign_extended fp) then 32 else
  let sfs := i_field_subfields fp in
  (shift fp) + (fold_left (fun c sfp => c + subfield_length sfp) sfs 0) .

Definition get_i_field_base_information_quantity (f : i_field) :=
  let fp := get_i_field_properties f in
  let sfs := i_field_subfields fp in
  (shift fp) + (fold_left (fun c sfp => c + subfield_length sfp) sfs 0) .

Definition get_i_fields_formatted_for_struct (instrs : list instruction) :=
  fold_left (fun l f =>
    (get_i_field_name f, bits_t (get_i_field_information_quantity f))::l
  ) (get_i_fields_list_from_instructions instrs) [].

Definition get_inst_fields_struct_from_ISA (isa : ISA) := {|
  struct_name   := "instFields";
  struct_fields := (get_i_fields_formatted_for_struct (ISA_instructions_set isa));
|}.
