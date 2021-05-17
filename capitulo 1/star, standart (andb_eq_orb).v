Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c. destruct b.
    + simpl. intros H. rewrite H. reflexivity.
    + simpl. intros H. rewrite H. reflexivity. Qed.
