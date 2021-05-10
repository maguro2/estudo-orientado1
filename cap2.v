From LF Require Export Basics.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

(*Exercise: 2 stars, standard, especially useful (basic_induction)*)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. rewrite <- plus_n_O. reflexivity.
  - (* n = S n' *) simpl. rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity. Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
 intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

(*Exercise: 2 stars, standard (double_plus)
Consider the following function, which doubles its argument:*)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
(*Use induction to prove this simple fact about double:*)

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) simpl. reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.

(*Exercise: 2 stars, standard, optional (evenb_S)*)
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  -(* n = 0 *) simpl. reflexivity.
  -(* n = S n' *) rewrite -> IHn'. rewrite -> negb_involutive. simpl. reflexivity. Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

(*Exercise: 3 stars, standard, especially useful (mult_comm)
Use assert to help prove plus_swap. You don't need to use induction yet.*)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> plus_comm.
  assert (H: p + n = n + p).
  { rewrite -> plus_comm. reflexivity. }
  rewrite <- H. rewrite -> plus_assoc. reflexivity. Qed.

(*Now prove commutativity of multiplication. 
You will probably want to define and prove a "helper" theorem to be used in 
the proof of this one. Hint: what is n × (1 + k)?*)

Theorem aux: forall n m : nat,
  m + m * n = m * (1 + n).
Proof.
  intros n m. induction m as [| m' IHm'].
   - simpl. reflexivity.
   - simpl. rewrite -> plus_swap. rewrite -> IHm'. simpl. reflexivity. Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m. 
  induction n as [| n' IHn'].
  - simpl. rewrite -> mult_0_r. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> aux. simpl. reflexivity. Qed.

(*Exercise: 3 stars, standard, optional (more_exercises)*)
Check leb.
Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p. intros H. induction p as [| p'].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity. Qed.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intros n. destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 
  1 * n = n.
Proof.
  intros n. simpl. rewrite -> plus_comm. simpl. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros b c. destruct b.
  - simpl. destruct c.
    + reflexivity.
    + reflexivity.
  - simpl. reflexivity. Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity. Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. 
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity. Qed.

(*Exercise: 2 stars, standard, optional (eqb_refl)*)

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> plus_comm.
  replace (n + p) with (p + n).
  - rewrite -> plus_assoc. reflexivity.
  - rewrite -> plus_comm. reflexivity. Qed.