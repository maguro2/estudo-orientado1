Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Module Playground.
  Definition b : rgb := blue.
End Playground.
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.
Module TuplePlayground.
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
    : nybble.
Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.
Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)
End TuplePlayground.
Check (S (S (S (S O)))).
Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.
Compute (minustwo 4).
