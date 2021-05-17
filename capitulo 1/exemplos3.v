Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. intros n. reflexivity. Qed.
Theorem plus_id_example : forall n m:nat,
  n = m ->  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.
Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof. intros p q. rewrite <- mult_n_O. rewrite <- mult_n_O. reflexivity. Qed.
