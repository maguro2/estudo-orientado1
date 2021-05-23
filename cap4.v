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

(*********1.2: Functions as Data*********)

(******1.2.1: Higher-Order Functions******)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).


Check @doit3times : forall X : Type, (X -> X) -> X -> X.
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. simpl. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. simpl. reflexivity. Qed.

(******1.2.2: Filter******)

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. simpl. reflexivity. Qed.
Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. simpl. reflexivity. Qed.

(******1.2.2: Anonymous Functions******)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. simpl. reflexivity. Qed.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. simpl. reflexivity. Qed.

(*Exercise: 2 stars, standard (filter_even_gt7)
Use filter (instead of Fixpoint) to write a Coq function filter_even_gt7 
that takes a list of natural numbers as input and returns a list of just 
those that are even and greater than 7.*)
Definition filter_even_gt7 (l : list nat) : list nat:=
  filter (leb 7) (filter evenb l).
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(*Exercise: 3 stars, standard (partition)
Use filter to write a Coq function partition:
      partition : ∀ X : Type,
                  (X → bool) → list X → list X × list X
Given a set X, a predicate of type X → bool and a list X, partition should 
return a pair of lists. The first member of the pair is the sublist of the 
original list containing the elements that satisfy the test, and the second 
is the sublist containing those that fail the test. The order of elements in 
the two sublists should be the same as their order in the original list.*)
Fixpoint filter_not {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then filter_not test t
                        else h :: (filter_not test t)
  end.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  pair (filter test l) (filter_not test l).
Check @partition. 
Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. simpl. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. simpl. reflexivity. Qed.

(******1.2.3: Maps******)
Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(*Exercise: 3 stars, standard (map_rev)
Show that map and rev commute. You may need to 
define an auxiliary lemma.*)
Lemma map_l_n : forall (X Y: Type) (f : X -> Y) (l : list X) (n : X),
  map f l ++ [f n] = map f (l ++ [n]).
Proof.
  intros X Y f l n. induction l as [| s l'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity. Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| s l'].
  - simpl. reflexivity.
  - simpl. rewrite <- map_l_n. rewrite <- IHl'. reflexivity. Qed.

(*Exercise: 2 stars, standard, especially useful (flat_map)
The function map maps a list X to a list Y using a function 
of type X → Y. We can define a similar function, flat_map, 
which maps a list X to a list Y using a function f of 
type X → list Y. Your definition should work by 'flattening' 
the results of f, like so:
        flat_map (fun n ⇒ [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].*)

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y):=
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.
Example test_flat_map2: flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(******1.2.4: Fold******)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.
Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.
Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(******1.2.5: Functions That Construct Functions******)
Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(*********1.3: Additional Exercises*********)
Module Exercises.

(*Exercise: 2 stars, standard (fold_length)
Many common functions on lists can be implemented in terms of fold. 
For example, here is an alternative definition of length:*)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.
(*Prove the correctness of fold_length. 
(Hint: It may help to know that reflexivity simplifies 
expressions a bit more aggressively than simpl does -- i.e.,
 you may find yourself in a situation where simpl does nothing 
but reflexivity solves the goal.)*)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof. 
  intros X l. induction l as [|s l'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl'. reflexivity. Qed.

(*Exercise: 3 stars, standard (fold_map)
We can also define map in terms of fold. Finish fold_map below.*)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y:=
  fold (fun x lx => [f x] ++ lx) l [].

Example test_fold_map1: fold_map (fun x => plus3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
(*Write down a theorem fold_map_correct in Coq stating that fold_map
 is correct, and prove it. (Hint: again, remember that reflexivity
 simplifies expressions a bit more aggressively than simpl.)*)

(*Exercise: 2 stars, advanced (currying)
In Coq, a function f : A → B → C really has the type A → (B → C). 
That is, if you give f a value of type A, it will give you 
function f' : B → C. If you then give f' a value of type B, it will 
return a value of type C. This allows for partial application, as in 
plus3. Processing a list of arguments with functions that return functions 
is called currying, in honor of the logician Haskell Curry.
Conversely, we can reinterpret the type A → B → C as (A × B) → C. 
This is called uncurrying. With an uncurried binary function, both 
arguments must be given at once as a pair; there is no partial application.
We can define currying as follows:*)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
As an exercise, define its inverse, prod_uncurry. Then prove the theorems below to show that the two are inverses.

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X × Y) : Z
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
As a (trivial) example of the usefulness of currying, we can use it to shorten one of the examples that we saw above:

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].

(*Thought exercise: before running the following commands, 
can you calculate the types of prod_curry and prod_uncurry?*)

Check @prod_curry.
Check @prod_uncurry.
Theorem uncurry_curry : forall(X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.