Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof. intros p. rewrite <-mult_n_Sm. rewrite <- mult_n_O. reflexivity. Qed.