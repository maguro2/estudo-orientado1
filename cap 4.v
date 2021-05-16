From LF Require Export Lists.

(*Cap: POLY
POLYMORPHISM AND HIGHER-ORDER FUNCTIONS*)

(*1.1: POLYMORPHISM*)

(*1.1.1: Polymorphic Lists*)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type -> Type.

