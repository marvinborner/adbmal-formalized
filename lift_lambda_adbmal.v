Require Export lambda.
Require Export alpha.
Require Export adbmal_subst_lems.
Require Export project_adbmal_lambda.

Set Implicit Arguments.

Section Lifting_Lambda_to_Adbmal.

(* diagram A' *)

Lemma lift_beta : 
 (M,N:Lambda)
  (lambda_beta M N)
   ->(M':Adbmal;X:stack)
      (omega M' (emb M) X)
       ->(EX N1:Adbmal|(EX N2:Adbmal|
           (kahrs' N1 X N2 X)
            /\(omega N2 (emb N) X)
             /\(adbmal_beta M' N1))).
Proof.
NewInduction M; Intros N h; Inversion_clear h; Clear N; Simpl.
(* pbeta_abs *)
NewInduction M';  Intros X h; Inversion_clear h.
(* M' = abs n M' *)
Clear IHM'.
Elim (IHM N0 H M' (cons n X) H0); Intros N1 h; Elim h; Clear h; Intros N2 h; 
 Elim h; Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (abs n N1); Exists (abs n N2); Split.
Apply kahrs_abs; Exact h.
Split.
Apply omega_abs; Exact h0.
Apply beta_abs; Exact h1.
(* M' = eos n0 M' *)
Elim (IHM' X0 H1); Intros N1 h; Elim h; Clear h; Intros N2 h; Elim h;
 Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (eos n0 N1); Exists (eos n0 N2); Split.
Apply kahrs_eos2; Exact h.
Split.
Apply omega_rule.
Rewrite <- (kahrs_FV_eq2 h).
Red; Intro h2; Apply H0.
Exact (beta_FV_sub h1 h2).
Exact h0.
Apply beta_eos; Exact h1.
(* pbeta_apl *)
Clear IHM2.
Rename M' into M1'.
NewInduction M'; Intros X h; Inversion_clear h.
(* M' = eos n0 M' *)
Elim (IHM' X0 H1); Intros N1 h; Elim h; Clear h; Intros N2 h; Elim h;
 Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (eos n N1); Exists (eos n N2); Split.
Apply kahrs_eos2; Exact h.
Split.
Apply omega_rule.
Rewrite <- (kahrs_FV_eq2 h).
Red; Intro h2; Apply H0.
Exact (beta_FV_sub h1 h2).
Exact h0.
Apply beta_eos; Exact h1.
(* M' = ap M'1 M'2 *)
Clear IHM'1 IHM'2.
Elim (IHM1 M1' H M'1 X H0); Intros N1 h; Elim h; Clear h; Intros N2 h;
 Elim h; Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (ap N1 M'2); Exists (ap N2 M'2); Split.
Apply kahrs_ap.
Exact h. 
Apply kahrs_refl.
Split.
Apply omega_ap; Assumption.
Apply beta_apl.
Exact h1.
(* pbeta_apr *)
Clear IHM1.
Rename M' into M2'.
NewInduction M'; Intros X h; Inversion_clear h.
(* M' = eos n0 M' *)
Elim (IHM' X0 H1); Intros N1 h; Elim h; Clear h; Intros N2 h; Elim h;
 Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (eos n N1); Exists (eos n N2); Split.
Apply kahrs_eos2; Exact h.
Split.
Apply omega_rule.
Rewrite <- (kahrs_FV_eq2 h).
Red; Intro h2; Apply H0.
Exact (beta_FV_sub h1 h2).
Exact h0.
Apply beta_eos; Exact h1.
(* M' = ap M'1 M'2 *)
Clear IHM'1 IHM'2.
Elim (IHM2 M2' H M'2 X H1); Intros N1 h; Elim h; Clear h; Intros N2 h;
 Elim h; Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (ap M'1 N1); Exists (ap M'1 N2); Split.
Apply kahrs_ap.
Apply kahrs_refl.
Exact h.
Split.
Apply omega_ap; Assumption.
Apply beta_apr.
Exact h1.
(* pbeta_rule *)
Clear IHM1 IHM2 M1.
NewInduction M'; Intros X h; Inversion_clear h.
Elim (IHM' X0 H0); Intros N1 h; Elim h; Clear h; Intros N2 h; Elim h;
 Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (eos n N1); Exists (eos n N2); Split.
Apply kahrs_eos2; Exact h.
Split.
Apply omega_rule.
Rewrite <- (kahrs_FV_eq2 h).
Red; Intro h2; Apply H.
Exact (beta_FV_sub h1 h2).
Exact h0.
Apply beta_eos; Exact h1.
(* M' = ap M'1 M'2 *)
Clear IHM'1 IHM'2.
Elim (omega_eoss_abs_inv H); Intros X' h; Elim h; Clear h; Intros M1 h; Elim h;
 Clear h; Intros Z h; Elim h; Clear h; Intros h h0; Elim h0; Clear h0;
 Intros h0 h1; Elim h1; Clear h1; Intros h1 h2.
Rewrite h in H; Rewrite h0 in H; Rewrite h0 in H0; Rewrite h; Rewrite h0.
Rename M2 into N.
Rename M'2 into N'.
Clear h h0 X M'1.
Rename X' into X.
Assert b := (scb_abs_inv (scb_eoss_inv2 (omega_scb H))). (* ... *)
Exists (adbmal_subst X Nil M1 x N').
Elim (project_subst 8!Nil 9!Nil b h1 [_;f;_]f (kahrs_refl M1 (cons x Z)) h2 H0);
 Intros P h; Elim h; Clear h; Intros h h0.
Exists (adbmal_subst X (nil name) P x N'); Split; [ Exact h | Split; [ Exact h0 | Apply beta_rule ]].
Qed.

End Lifting_Lambda_to_Adbmal.
