Require Export lambda.
Require Export alpha.
Require Export adbmal_subst_lems.
Require Export project_adbmal_lambda.

Set Implicit Arguments.

Section Lifting_Lambda_to_Adbmal.

(* diagram A' *)

Lemma lift_beta : 
 forall M N : Lambda,
   lambda_beta M N ->
   forall (M' : Adbmal) (X : stack),
     omega M' (emb M) X ->
     exists N1 : Adbmal, exists N2 : Adbmal,
       kahrs' N1 X N2 X /\
       omega N2 (emb N) X /\
       adbmal_beta M' N1.
Proof.
induction M; intros N h; inversion_clear h; clear N; simpl.
(* pbeta_abs *)
induction M';  intros X h; inversion_clear h.
(* M' = abs n M' *)
clear IHM'.
elim (IHM N0 H M' (cons n X) H0); intros N1 h; elim h; clear h; intros N2 h; 
 elim h; clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (abs n N1); exists (abs n N2); split.
apply kahrs_abs; exact h.
split.
apply omega_abs; exact h0.
apply beta_abs; exact h1.
(* M' = eos n0 M' *)
elim (IHM' X0 H1); intros N1 h; elim h; clear h; intros N2 h; elim h;
 clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (eos n0 N1); exists (eos n0 N2); split.
apply kahrs_eos2; exact h.
split.
apply omega_rule.
rewrite <- (kahrs_FV_eq2 h).
red; intro h2; apply H0.
exact (beta_FV_sub h1 Nil n0 h2).
exact h0.
apply beta_eos; exact h1.
(* pbeta_apl *)
clear IHM2.
rename M' into M1'.
induction M'; intros X h; inversion_clear h.
(* M' = eos n0 M' *)
elim (IHM' X0 H1); intros N1 h; elim h; clear h; intros N2 h; elim h;
 clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (eos n N1); exists (eos n N2); split.
apply kahrs_eos2; exact h.
split.
apply omega_rule.
rewrite <- (kahrs_FV_eq2 h).
red; intro h2; apply H0.
exact (beta_FV_sub h1 Nil n h2).
exact h0.
apply beta_eos; exact h1.
(* M' = ap M'1 M'2 *)
clear IHM'1 IHM'2.
elim (IHM1 M1' H M'1 X H0); intros N1 h; elim h; clear h; intros N2 h;
 elim h; clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (ap N1 M'2); exists (ap N2 M'2); split.
apply kahrs_ap.
exact h. 
apply kahrs_refl.
split.
apply omega_ap; assumption.
apply beta_apl.
exact h1.
(* pbeta_apr *)
clear IHM1.
rename M' into M2'.
induction M'; intros X h; inversion_clear h.
(* M' = eos n0 M' *)
elim (IHM' X0 H1); intros N1 h; elim h; clear h; intros N2 h; elim h;
 clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (eos n N1); exists (eos n N2); split.
apply kahrs_eos2; exact h.
split.
apply omega_rule.
rewrite <- (kahrs_FV_eq2 h).
red; intro h2; apply H0.
exact (beta_FV_sub h1 Nil n h2).
exact h0.
apply beta_eos; exact h1.
(* M' = ap M'1 M'2 *)
clear IHM'1 IHM'2.
elim (IHM2 M2' H M'2 X H1); intros N1 h; elim h; clear h; intros N2 h;
 elim h; clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (ap M'1 N1); exists (ap M'1 N2); split.
apply kahrs_ap.
apply kahrs_refl.
exact h.
split.
apply omega_ap; assumption.
apply beta_apr.
exact h1.
(* pbeta_rule *)
clear IHM1 IHM2 M1.
induction M'; intros X h; inversion_clear h.
elim (IHM' X0 H0); intros N1 h; elim h; clear h; intros N2 h; elim h;
 clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (eos n N1); exists (eos n N2); split.
apply kahrs_eos2; exact h.
split.
apply omega_rule.
rewrite <- (kahrs_FV_eq2 h).
red; intro h2; apply H.
exact (beta_FV_sub h1 Nil n h2).
exact h0.
apply beta_eos; exact h1.
(* M' = ap M'1 M'2 *)
clear IHM'1 IHM'2.
elim (omega_eoss_abs_inv H); intros X' h; elim h; clear h; intros M1 h; elim h;
 clear h; intros Z h; elim h; clear h; intros h h0; elim h0; clear h0;
 intros h0 h1; elim h1; clear h1; intros h1 h2.
rewrite h in H; rewrite h0 in H; rewrite h0 in H0; rewrite h; rewrite h0.
rename M2 into N.
rename M'2 into N'.
clear h h0 X M'1.
rename X' into X.
pose proof (scb_abs_inv (@scb_eoss_inv2 (abs x M1) X Z (omega_scb H))) as b. (* ... *)
exists (adbmal_subst X Nil M1 x N').
elim (@project_subst M1 M1 N' M N x X Nil Nil Z
      b h1 (fun _ f _ => f) (kahrs_refl M1 (cons x Z)) h2 H0);
 intros P h; elim h; clear h; intros h h0.
exists (adbmal_subst X (@nil name) P x N'); split; [ exact h | split; [ exact h0 | apply beta_rule ]].
Qed.

End Lifting_Lambda_to_Adbmal.
