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

(* get_fields *)
Context {reg_t: Type}.

Definition rv32i_ISA : ISA := {|
  ISA_memory_model  := RVWMO;
  ISA_base_standard := RV32I;
  ISA_extensions    := [];
|}.

Definition inst_field_s := get_inst_fields_struct_from_ISA rv32i_ISA.
Definition fields_list  := get_i_fields_list_from_instructions (ISA_instructions_set rv32i_ISA).

Definition example_struct := 
  {|
  struct_name   := "exampleStruct";
  struct_fields := ("fied", bits_t 1) :: nil
|}.

Compute {{
    struct example_struct {
      fied := Ob~1
    }
}}.

Compute UStructInit example_struct [("fied", USugar (UConstBits Ob~1))].

Require Import Strings.String.

Definition get_shift_data (f : i_field)
  : option (uaction reg_t empty_ext_fn_t)
:=
  let fp := get_i_field_properties f in
  match shift fp with
  | 0 => None
  | x => Some (USugar (UConstBits (Bits.of_N x 0)))
  end.

Definition get_single_slice (sp : subfield_properties)
  : uaction reg_t empty_ext_fn_t
:=
  UBinop (UBits2 (UIndexedSlice (subfield_length sp))) {{ inst }}
  (USugar (UConstBits (Bits.of_N 5 (first_bit sp)))).

Definition merge_actions (a1 a2 : uaction reg_t empty_ext_fn_t)
  : uaction reg_t empty_ext_fn_t
:=
  UBinop (UBits2 UConcat) a1 a2.

Definition sign_extend_if_required
  (f : i_field) (initial_action : uaction reg_t empty_ext_fn_t)
  : uaction reg_t empty_ext_fn_t
:=
  let fp := get_i_field_properties f in
  match is_sign_extended fp with
  | false =>
      let base_info_qtt := get_i_field_base_information_quantity f in
      USugar (
        UCallModule id Lift_self
          (signExtend base_info_qtt (32 - base_info_qtt))
          [initial_action]
      )
  | true  => initial_action
  end.

Definition get_slice_actions (f : i_field)
  : uaction reg_t empty_ext_fn_t
:=
  let option_slices := fold_left (fun a c =>
      match a with
      | None => Some (get_single_slice c)
      | Some x => Some (merge_actions x (get_single_slice c))
      end
    ) (i_field_subfields (get_i_field_properties f)) None
  in
  match option_slices with
  | None   => USugar USkip
  | Some x => x
  end.

Definition extend_action_with_shift
  (f : i_field) (action : uaction reg_t empty_ext_fn_t)
  : uaction reg_t empty_ext_fn_t
:=
  match get_shift_data f with
  | None   => action
  | Some x => merge_actions x action
  end.

Definition get_field_action (f : i_field) : uaction reg_t empty_ext_fn_t :=
  sign_extend_if_required f (extend_action_with_shift f (get_slice_actions f)).

Definition manage_field (f : i_field)
  : (string * uaction reg_t empty_ext_fn_t)
:=
  (get_i_field_name f, get_field_action f).

Definition generate_get_field_function (fields : list i_field)
  : UInternalFunction reg_t empty_ext_fn_t
:= {|
  int_name := "getFields";
  int_argspec := [prod_of_argsig
    {| arg_name := "inst"; arg_type := bits_t 32 |}
  ];
  int_retSig := struct_t inst_field_s;
  int_body := USugar (UStructInit inst_field_s
    (fold_left (fun a f => (manage_field f) :: a) fields [])
  )
|}.
