Require Import Koika.BitsToLists Koika.Std.
Require Import rv.RVCore rv.rv32i.
Import RV32I.

Definition ext_sigma (e: ext_fn_t) (bits: BitsToLists.val) : BitsToLists.val :=
  match e with
  | ext_mem _ =>
    match bits with
    | Struct mem_input _ =>
      Struct mem_output [
        Bits 1 [true]; Bits 1 [true];
        Struct mem_resp [
          Bits 4 [true; true; true; true];
          Bits 32 [
            true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true ];
          Bits 32 [
            true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true;
            true; true; true; true; true; true; true; true ]]]
    | _ => Bits 1 [false] (* illegal *)
    end
  | ext_uart_read =>
    match bits with
    | Bits 1 _ =>
      Struct
        (Maybe (bits_t 8))
        [Bits 1 [true]; Bits 8 [true; true; true; true; true; true; true; true]]
    | _ => Bits 1 [false] (* illegal *)
    end
  | ext_uart_write =>
    match bits with
    | Struct uart_input _ => Bits 1 [true]
    | _ => Bits 1 [false] (* illegal *)
    end
  | ext_led =>
    match bits with
    | Struct led_input _ => Bits 1 [true]
    | _ => Bits 1 [false] (* illegal *)
    end
  | ext_host_id =>
    match bits with
    | Bits 1 _ =>
      match vect_index "NoHost" (host_id).(enum_members) with
      | None => Bits 1 [false] (* Should never happen *)
      | Some idx =>
        @val_of_value
          (enum_t host_id) (vect_nth (host_id).(enum_bitpatterns) idx)
      end
    | _ => Bits 1 [false] (* illegal *)
    end
  | ext_finish =>
    match bits with
    | Struct ext_input _ => Bits 1 [true]
    | _ => Bits 1 [false] (* illegal *)
    end
  end.

Definition external_env := {|
  mem := list ();
  uart_in := list val; (* Queue *)
|}.
