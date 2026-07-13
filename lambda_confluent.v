Require Export project_adbmal_lambda.
Require Export lift_lambda_adbmal.
Require Export adbmal_confluent.

Set Implicit Arguments.

Section confluence_of_lambda_beta.

Lemma omega_lambda_refl :
 forall (M : Lambda) (X : stack),
   omega (emb M) (emb M) X.
Proof.
induction M; intro X; simpl.
apply omega_var.
apply omega_abs; apply IHM.
apply omega_ap; [ apply IHM1 | apply IHM2 ].
Qed.

Lemma A_star :
 forall M1 M2 : Lambda,
   Rstar lambda_beta M1 M2 ->
   forall P1 Q1 : Adbmal,
     kahrs P1 Q1 ->
     omega Q1 (emb M1) Nil ->
     exists P2 : Adbmal, exists Q2 : Adbmal,
       kahrs P2 Q2 /\
       omega Q2 (emb M2) Nil /\
       Rstar adbmal_beta P1 P2.
Proof.
intros M1 M2 h; elim h; clear h M1 M2.
(* refl *)
intros M P1 Q1 h h0.
exists P1; exists Q1; split;
 [ exact h | split; [ exact h0 | apply Rstar_refl ] ].
(* contains lambda_beta *)
intros M1 M2 h P1 Q1 h0 h1.
elim (lift_beta h h1); intros R2 h2; elim h2; clear h2; intros Q2 h2;
 elim h2; clear h2; intros h2 h3; elim h3; clear h3; intros h3 h4.
elim (commute_kahrs_beta (omega_scb h1) h4 (kahrs_symm h0));
 intros P2 h5; elim h5; clear h5; intros h5 h6.
exists P2; exists Q2; split.
exact (kahrs_trans (kahrs_symm h6) h2).
split.
exact h3.
apply Rstar_ext; exact h5.
(* trans *)
intros M1 M2 M3 h1 IH1 h2 IH2 P1 Q1 h3 h4.
elim (IH1 P1 Q1 h3 h4); intros P2 h5; elim h5; clear h5; intros Q2 h5;
 elim h5; clear h5; intros h5 h6; elim h6; clear h6; intros h6 h7.
elim (IH2 P2 Q2 h5 h6); intros P3 h8; elim h8; clear h8; intros Q3 h8;
 elim h8; clear h8; intros h8 h9; elim h9; clear h9; intros h9 h10.
exists P3; exists Q3; split.
exact h8.
split.
exact h9.
exact (Rstar_trans h7 h10).
Qed.

Lemma C_star :
 forall P1 P2 : Adbmal,
   Rstar adbmal_beta P1 P2 ->
   forall (M1 : Lambda) (Q1 : Adbmal),
     kahrs P1 Q1 ->
     omega Q1 (emb M1) Nil ->
     exists M2 : Lambda, exists Q2 : Adbmal,
       kahrs P2 Q2 /\
       omega Q2 (emb M2) Nil /\
       Rstar lambda_beta M1 M2.
Proof.
intros P1 P2 h; elim h; clear h P1 P2.
(* refl *)
intros P M1 Q1 h h0.
exists M1; exists Q1; split;
 [ exact h | split; [ exact h0 | apply Rstar_refl ] ].
(* contains lambda_beta *)
intros P1 P2 h M1 Q1 h0 h1.
elim (commute_kahrs_beta (kahrs_scb (kahrs_symm h0) (omega_scb h1)) h h0);
 intros R2 h2; elim h2; clear h2; intros h2 h3.
elim (project_beta h2 M1 h1); intros Q2 h4; elim h4; clear h4; intros M2 h4;
 elim h4; clear h4; intros h4 h5; elim h5; clear h5; intros h5 h6.
exists M2; exists Q2; split.
exact (kahrs_trans h3 h4).
split.
exact h5.
apply Rstar_ext; exact h6.
(* trans *)
intros P1 P2 P3 h1 IH1 h2 IH2 M1 Q1 h3 h4.
elim (IH1 M1 Q1 h3 h4); intros M2 h5; elim h5; clear h5; intros Q2 h5;
 elim h5; clear h5; intros h5 h6; elim h6; clear h6; intros h6 h7.
elim (IH2 M2 Q2 h5 h6); intros M3 h8; elim h8; clear h8; intros Q3 h8;
 elim h8; clear h8; intros h8 h9; elim h9; clear h9; intros h9 h10.
exists M3; exists Q3; split.
exact h8.
split.
exact h9.
exact (Rstar_trans h7 h10).
Qed.

Definition lambda_kahrs := fun M N => kahrs (emb M) (emb N).

Lemma lambda_confluent_up_to_kahrs : (confluent_up_to lambda_beta lambda_kahrs).
Proof.
unfold confluent_up_to, diamond_up_to.
intros M M1 h1 M2 h2.
elim (A_star h1 (kahrs_refl (emb M) Nil) (omega_lambda_refl M Nil));
 intros N1 h3; elim h3; clear h3; intros Q1 h3; elim h3; clear h3;
 intros h3 h4; elim h4; clear h4; intros h4 h5.
elim (A_star h2 (kahrs_refl (emb M) Nil) (omega_lambda_refl M Nil));
 intros N2 h6; elim h6; clear h6; intros Q2 h6; elim h6; clear h6;
 intros h6 h7; elim h7; clear h7; intros h7 h8.
elim (beta_confluent h5 h8);
 intros P h9; elim h9; clear h9; intros h9 h10.
elim (C_star h9 M1 h3 h4); intros P1 h11; elim h11; clear h11; intros T1 h11;
 elim h11; clear h11; intros h11 h12; elim h12; clear h12; intros h12 h13.
elim (C_star h10 M2 h6 h7); intros P2 h14; elim h14; clear h14; intros T2 h14;
 elim h14; clear h14; intros h14 h15; elim h15; clear h15; intros h15 h16.
pose proof (kahrs_trans (kahrs_symm h11) h14) as h17.
pose proof (kahrs_omega_commute h17 h12 h15) as h18.
exists P1; exists P2; split; [ exact h13 | split; [ exact h16 | exact h18 ]].
Qed.

End confluence_of_lambda_beta.
