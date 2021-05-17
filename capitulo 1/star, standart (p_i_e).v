Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros n m o. intros H. intros G. rewrite -> H, G. reflexivity. Qed.