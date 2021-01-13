Require Import List.
Import ListNotations.

Require Import ITypes.

Inductive i_field :=
| opcode | fct2 | fct3 | fct7 | rs1 | rs2 | rs3 | rd | immI | immS | immB | immU
| immJ.

Definition has_opcode (t : i_type) :=
  match t with
  | RType => true | R4Type => true | IType => true | SType => true
  | BType => true | UType  => true | JType => true
  end.

Definition has_fct2 (t : i_type) :=
  match t with
  | RType => false | R4Type => true  | IType => false | SType => false
  | BType => false | UType  => false | JType => false
  end.

Definition has_fct3 (t : i_type) :=
  match t with
  | RType => true | R4Type => true  | IType => true  | SType => true
  | BType => true | UType  => false | JType => false
  end.

Definition has_fct7 (t : i_type) :=
  match t with
  | RType => true  | R4Type => false | IType => false | SType => false
  | BType => false | UType  => false | JType => false
  end.

Definition has_rs1 (t : i_type) :=
  match t with
  | RType => true | R4Type => true  | IType => true  | SType => true
  | BType => true | UType  => false | JType => false
  end.

Definition has_rs2 (t : i_type) :=
  match t with
  | RType => true | R4Type => true  | IType => false | SType => true
  | BType => true | UType  => false | JType => false
  end.

Definition has_rs3 (t : i_type) :=
  match t with
  | RType => false | R4Type => true  | IType => false | SType => false
  | BType => false | UType  => false | JType => false
  end.

Definition has_rd (t : i_type) :=
  match t with
  | RType => true  | R4Type => true | IType => true | SType => false
  | BType => false | UType  => true | JType => true
  end.

Definition has_immI (t : i_type) :=
  match t with
  | RType => false | R4Type => false | IType => true | SType => false
  | BType => false | UType  => false | JType => false
  end.

Definition has_immS (t : i_type) :=
  match t with
  | RType => false | R4Type => false | IType => false | SType => true
  | BType => false | UType  => false | JType => false
  end.

Definition has_immB (t : i_type) :=
  match t with
  | RType => false | R4Type => false | IType => false | SType => false
  | BType => true  | UType  => false | JType => false
  end.

Definition has_immU (t : i_type) :=
  match t with
  | RType => false | R4Type => false | IType => false | SType => false
  | BType => false | UType  => true  | JType => false
  end.

Definition has_immJ (t : i_type) :=
  match t with
  | RType => false | R4Type => false | IType => false | SType => false
  | BType => false | UType  => false | JType => true
  end.

Record subfield_properties := {
  first_bit : nat;
  length : nat
}.

Record i_field_properties := {
  is_sign_extended : bool;
  shift : nat;
  i_field_subfields : list subfield_properties
}.

Definition get_i_field_properties (f : i_field) :=
  match f with
  | opcode => {|
      is_sign_extended  := false;
      shift             := 0;
      i_field_subfields := {| first_bit := 0 ; length := 7 |}::[]
    |}
  | rd     => {|
      is_sign_extended  := false;
      shift             := 0;
      i_field_subfields := {| first_bit := 7 ; length := 5 |}::[]
    |}
  | rs1    => {|
      is_sign_extended  := false;
      shift             := 0;
      i_field_subfields := {| first_bit := 15; length := 5 |}::[]
    |}
  | rs2    => {|
      is_sign_extended  := false;
      shift             := 0;
      i_field_subfields := {| first_bit := 20; length := 5 |}::[]
    |}
  | rs3    => {|
      is_sign_extended  := false;
      shift             := 0;
      i_field_subfields := {| first_bit := 27; length := 5 |}::[]
    |}
  | fct2 => {|
      is_sign_extended  := false;
      shift             := 0;
      i_field_subfields := {| first_bit := 25; length := 2 |}::[]
    |}
  | fct3 => {|
      is_sign_extended  := false;
      shift             := 0;
      i_field_subfields := {| first_bit := 12; length := 3 |}::[]
    |}
  | fct7 => {|
      is_sign_extended  := false;
      shift             := 0;
      i_field_subfields := {| first_bit := 25; length := 7 |}::[]
    |}
  | immI   => {|
      is_sign_extended  := true;
      shift             := 0;
      i_field_subfields := {| first_bit := 20; length := 12 |}::[]
    |}
  | immS   => {|
      is_sign_extended  := true;
      shift             := 0;
      i_field_subfields :=
        {| first_bit := 25; length := 7 |}::
        {| first_bit := 7 ; length := 5 |}::[]
    |}
  | immB   => {|
      is_sign_extended  := true;
      shift             := 1;
      i_field_subfields :=
        {| first_bit := 31; length := 1 |}::
        {| first_bit := 7 ; length := 1 |}::
        {| first_bit := 25; length := 6 |}::
        {| first_bit := 8 ; length := 4 |}::[]
    |}
  | immU   => {|
      is_sign_extended := false;
      shift            := 12;
      i_field_subfields  := {| first_bit := 12; length := 20 |}::[];
    |}
  | immJ   => {|
      is_sign_extended := true;
      shift            := 1;
      i_field_subfields  :=
        {| first_bit := 31; length := 1  |}::
        {| first_bit := 12; length := 8  |}::
        {| first_bit := 20; length := 1  |}::
        {| first_bit := 21; length := 10 |}::[]
    |}
  end.

Definition is_i_field_identifier (f : i_field) :=
  match f with
  | opcode => true  | fct2 => true  | fct3 => true  | fct7 => true
  | rs1    => false | rs2  => false | rs3  => false | rd   => false
  | immI   => false | immS => false | immB => false | immU => false
  | immJ   => false
  end.

Definition is_i_field_data (f : i_field) := negb (is_i_field_identifier f).
