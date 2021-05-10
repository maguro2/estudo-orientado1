From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst (pair 3 5)).
(* ===> 3 *)

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).
Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(*Exercise: 1 star, standard (snd_fst_is_swap)*)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(*Exercise: 1 star, standard, optional (fst_swap_is_snd)*)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(*The app function concatenates (appends) two lists.*)
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist:=
  match l with
  | nil => nil
  | h :: t => match h with
              | O => nonzeros t
              | nat => h :: nonzeros t
              end
  end.
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist:=
  match l with
  | nil => nil
  | h :: t => match h with
              | O => oddmembers (t)
              | nat => match oddb (nat) with
                       | true => h :: oddmembers t
                       | false => oddmembers(t)
                       end
              end
  end.
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. simpl. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat:=
    match l with
  | nil => O
  | h :: t => match h with
              | O => countoddmembers (t)
              | nat => match oddb (nat) with
                       | true => S (countoddmembers (t))
                       | false => countoddmembers(t)
                       end
              end
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
  Proof. simpl. reflexivity. Qed.

(*Exercise: 3 stars, advanced (alternate)*)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 => match l2 with
                | nil => h1 :: t1
                | h2 :: t2 => [ h1; h2 ] ++ (alternate t1 t2)
                end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
  Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

(*Exercise: 3 stars, standard, especially useful(bag_functions)*)
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => O
  | h :: t => match h =? v with
              | true => S ( count v t)
              | false => count v t
              end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
 Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
 Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
 Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag := cons v s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
 Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
 Proof. simpl. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
   1 <=? count v s.
Example test_member1: member 1 [1;4;1] = true.
  Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
  Proof. simpl. reflexivity. Qed.

(*Exercise: 3 stars, standard, optional (bag_more_functions)*)
Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match h =? v with
              | true => t
              | false => cons h (remove_one v t)
              end
  end.
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match h =? v with
              | true => remove_all v t
              | false => cons h (remove_all v t)
              end
  end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
 Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1 : bag) (s2 : bag) : bool:=
  match s1 with
  | nil => true
  | h :: t => match count h s1 <=? count h s2 with
              | false => false
              | true => subset t s2
              end
  end. 
Example test_subset1: subset [1;2] [2;1;4;1] = true.
 Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
 Proof. simpl. reflexivity. Qed.

(*listas*)
Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

(*indução para listas*)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite plus_comm.
    reflexivity. Qed.

(*Exercise: 3 stars, standard (list_exercises)
More practice with lists:*)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity. Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. simpl. reflexivity. Qed.

(*Exercise: 2 stars, standard (eqblist)
Fill in the definition of eqblist, which compares lists of numbers for equality. 
Prove that eqblist l l yields true for every list l.*)

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => match l2 with 
           | nil => true
           | h2 :: t2 => false
           end
  | h1 :: t1 => match l2 with
                | nil => false
                | h2 :: t2 => match h1 =? h2 with 
                              | true => eqblist t1 t2
                              | false => false
                              end
                end
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
  Proof. simpl. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
  Proof. simpl. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
  Proof. simpl. reflexivity. Qed.

Theorem beq_nat_n_n : forall n: nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl'. rewrite -> beq_nat_n_n. reflexivity. Qed.

(*List Exercises, Part 2
Here are a couple of little theorems to prove about your definitions about bags above.
Exercise: 1 star, standard (count_member_nonzero)*)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. simpl. reflexivity. Qed.

(*The following lemma about leb might help you in the next exercise.*)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.
(*Before doing the next exercise, make sure you've filled in the definition of remove_one 
above.
Exercise: 3 stars, advanced (remove_does_not_increase_count)*)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [| s'].
  - simpl. reflexivity.
  - simpl. destruct s'.
    + simpl. rewrite -> leb_n_Sn. reflexivity.
    + simpl. rewrite -> IHs. reflexivity. Qed.

Theorem bag_count_sum: forall a b : bag, forall n : nat,
                         count n a + count n b = count n (sum a b).
Proof.
  intros a b n. induction a as [| a'].
  - simpl. reflexivity.
  - simpl. destruct  a'.
    + simpl. rewrite <- IHa. 
Abort.

(*Exercise: 4 stars, advanced (rev_injective)
Prove that the rev function is injective. There is a hard way and an easy way to do this.*)

Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H. rewrite <- (rev_involutive l1). rewrite -> H. 
  rewrite-> (rev_involutive l2). reflexivity. Qed.

