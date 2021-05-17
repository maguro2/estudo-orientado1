Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. intros H. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + rewrite <- H. reflexivity.
  - destruct c eqn:Ec.
    + rewrite <- H. reflexivity.
    + rewrite <- H. reflexivity.
Qed.

