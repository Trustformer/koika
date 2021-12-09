Lemma new_names_no_collision : forall (ua : uact) (n : nat) (id: string),
  n > get_highest_binding_number ua -> s = generate_binding_name ->
