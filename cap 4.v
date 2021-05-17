From LF Require Export Lists.

(*Cap: POLY
POLYMORPHISM AND HIGHER-ORDER FUNCTIONS*)

(*********1.1: POLYMORPHISM*********)

(******1.1.1: Polymorphic Lists******)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type -> Type.

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

Check cons : forall X : Type, X -> list X -> list X.

Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. simpl. reflexivity. Qed.

(*Exercise: 2 stars, standard (mumble_grumble)
Consider the following two inductively defined types.*)

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).
(*Which of the following are well-typed elements of grumble X for some type X? 
(Add YES or NO to each line.)
d (b a 5)
d mumble (b a 5)
d bool (b a 5)
e bool true
e mumble (b c 0)
e bool (b c 0)
c
 NO, YES, NO, YES, YES, NO*)
End MumbleGrumble.
(* Do not modify the following line: *)
Definition manual_grade_for_mumble_grumble : option (nat*string) := None.

(***1.1.1.1 Type Annotation Inference***)
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.
Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(***1.1.1.2 Type Argument Synthesis***)
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(***1.1.1.3 Implicit Arguments***)
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.
(*don't make like this*)
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').


Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. simpl. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. simpl. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. simpl. reflexivity. Qed.

(***1.1.1.4 Supplying Type Arguments Explicitly***)
Fail Definition mynil := nil.

Definition mynil : list nat := nil.
Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(*Exercise: 2 stars, standard, optional (poly_exercises)
Here are a few simple exercises, just like ones in the Lists chapter,
for practice with polymorphism. Complete the proofs below.*)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X. intros l. induction l as [| n l'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity. Qed.
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A. intros l m n. induction l as [| n' l'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity. Qed.
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X. intros l1 l2. induction l1 as [| n l1'].
  - simpl. reflexivity.
  - simpl. rewrite IHl1'. reflexivity. Qed.

(*Exercise: 2 stars, standard, optional (more_poly_exercises)
Here are some slightly more interesting ones...*)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity. Qed.
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity. Qed.

(******1.1.2 Polymorphic Pairs******)
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x , y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(*Exercise: 1 star, standard, optional (combine_checks)*)
(*Try answering the following questions on paper and checking your answers in Coq:
What is the type of combine (i.e., what does Check @combine print?)
What does
        Compute (combine [1;2] [false;false;true;true]).
print?*)
Check @combine. (*forall X Y : Type, list X -> list Y -> list (X * Y)*)
Compute (combine [1;2] [false;false;true;true]). 
(*= [(1, false); (2, false)]
     : list (nat * bool)*)

(*Exercise: 2 stars, standard, especially useful (split)
The function split is the right inverse of combine: it takes a list of pairs 
and returns a pair of lists. In many functional languages, it is called unzip.
Fill in the definition of split below. Make sure it passes the given unit test.*)

Fixpoint split {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y)
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
    (*match l with
  | nil => ([], [])
  | (lx, ly) :: l' => (cons lx, cons ly) (split l')
end.*)
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. Admitted.

(******1.1.3  Polymorphic Options******)
Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X} _.
Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. simpl. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. simpl. reflexivity. Qed.

(*Exercise: 1 star, standard, optional (hd_error_poly)
Complete the definition of a polymorphic version of the hd_error 
function from the last chapter. Be sure that it passes the unit tests below.*)

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

(*Once again, to force the implicit arguments to be explicit, 
we can use @ before the name of the function.*)

Check @hd_error : forall X : Type, list X -> option X.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. simpl. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. simpl. reflexivity. Qed.
Example test_hd_error3 : hd_error [] = None.
Proof. reflexivity. Qed.