Definition bind
  {A B: Type} (o: option A) (f: A -> option B)
: option B :=
  match o with
  | None => None
  | Some x => f x
  end.
Notation "A >>= F" := (bind A F) (at level 42, left associativity).
