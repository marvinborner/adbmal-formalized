Require Export project_adbmal_lambda.
Require Export lift_lambda_adbmal.
Require Export adbmal_confluent.

Set Implicit Arguments.

Section confluence_of_lambda_beta.

Lemma omega_lambda_refl :
 (M:Lambda;X:stack)
  (omega (emb M) (emb M) X).
Proof.
NewInduction M; Intro X; Simpl.
Apply omega_var.
Apply omega_abs; Apply IHM.
Apply omega_ap; [ Apply IHM1 | Apply IHM2 ].
Qed.

Lemma A_star :
 (M1,M2:Lambda)
 (Rstar lambda_beta M1 M2)
  ->(P1,Q1:Adbmal)
     (kahrs P1 Q1)
      ->(omega Q1 (emb M1) Nil)
       ->(EX P2:Adbmal|(EX Q2:Adbmal|
           (kahrs P2 Q2)
            /\(omega Q2 (emb M2) Nil) 
             /\(Rstar adbmal_beta P1 P2))).
Proof.
Intros M1 M2 h; Elim h; Clear h M1 M2.
(* refl *)
Intros M P1 Q1 h h0.
Exists P1; Exists Q1; Split;
 [ Exact h | Split; [ Exact h0 | Apply Rstar_refl ] ].
(* contains lambda_beta *)
Intros M1 M2 h P1 Q1 h0 h1.
Elim (lift_beta h h1); Intros R2 h2; Elim h2; Clear h2; Intros Q2 h2; 
 Elim h2; Clear h2; Intros h2 h3; Elim h3; Clear h3; Intros h3 h4.
Elim (commute_kahrs_beta (omega_scb h1) h4 (kahrs_symm h0)); 
 Intros P2 h5; Elim h5; Clear h5; Intros h5 h6.
Exists P2; Exists Q2; Split.
Exact (kahrs_trans (kahrs_symm h6) h2).
Split.
Exact h3.
Apply Rstar_ext; Exact h5.
(* trans *)
Intros M1 M2 M3 h1 IH1 h2 IH2 P1 Q1 h3 h4.
Elim (IH1 P1 Q1 h3 h4); Intros P2 h5; Elim h5; Clear h5; Intros Q2 h5; 
 Elim h5; Clear h5; Intros h5 h6; Elim h6; Clear h6; Intros h6 h7.
Elim (IH2 P2 Q2 h5 h6); Intros P3 h8; Elim h8; Clear h8; Intros Q3 h8; 
 Elim h8; Clear h8; Intros h8 h9; Elim h9; Clear h9; Intros h9 h10.
Exists P3; Exists Q3; Split.
Exact h8.
Split.
Exact h9.
Exact (Rstar_trans h7 h10).
Qed.

Lemma C_star :
 (P1,P2:Adbmal)
 (Rstar adbmal_beta P1 P2)
  ->(M1:Lambda;Q1:Adbmal)
     (kahrs P1 Q1)
      ->(omega Q1 (emb M1) Nil)
       ->(EX M2:Lambda|(EX Q2:Adbmal|
           (kahrs P2 Q2)
            /\(omega Q2 (emb M2) Nil) 
             /\(Rstar lambda_beta M1 M2))).
Proof.
Intros P1 P2 h; Elim h; Clear h P1 P2.
(* refl *)
Intros P M1 Q1 h h0.
Exists M1; Exists Q1; Split;
 [ Exact h | Split; [ Exact h0 | Apply Rstar_refl ] ].
(* contains lambda_beta *)
Intros P1 P2 h M1 Q1 h0 h1.
Elim (commute_kahrs_beta (kahrs_scb (kahrs_symm h0) (omega_scb h1)) h h0); 
 Intros R2 h2; Elim h2; Clear h2; Intros h2 h3.
Elim (project_beta h2 h1); Intros Q2 h4; Elim h4; Clear h4; Intros M2 h4; 
 Elim h4; Clear h4; Intros h4 h5; Elim h5; Clear h5; Intros h5 h6.
Exists M2; Exists Q2; Split.
Exact (kahrs_trans h3 h4).
Split.
Exact h5.
Apply Rstar_ext; Exact h6.
(* trans *)
Intros P1 P2 P3 h1 IH1 h2 IH2 M1 Q1 h3 h4.
Elim (IH1 M1 Q1 h3 h4); Intros M2 h5; Elim h5; Clear h5; Intros Q2 h5; 
 Elim h5; Clear h5; Intros h5 h6; Elim h6; Clear h6; Intros h6 h7.
Elim (IH2 M2 Q2 h5 h6); Intros M3 h8; Elim h8; Clear h8; Intros Q3 h8; 
 Elim h8; Clear h8; Intros h8 h9; Elim h9; Clear h9; Intros h9 h10.
Exists M3; Exists Q3; Split.
Exact h8.
Split.
Exact h9.
Exact (Rstar_trans h7 h10).
Qed.

Definition lambda_kahrs := [M,N](kahrs (emb M) (emb N)).

Lemma lambda_confluent_up_to_kahrs : (confluent_up_to lambda_beta lambda_kahrs).
Proof.
Unfold confluent_up_to diamond_up_to.
Intros M M1 h1 M2 h2.
Elim (A_star h1 (kahrs_refl (emb M) Nil) (omega_lambda_refl M Nil));
 Intros N1 h3; Elim h3; Clear h3; Intros Q1 h3; Elim h3; Clear h3; 
 Intros h3 h4; Elim h4; Clear h4; Intros h4 h5.
Elim (A_star h2 (kahrs_refl (emb M) Nil) (omega_lambda_refl M Nil));
 Intros N2 h6; Elim h6; Clear h6; Intros Q2 h6; Elim h6; Clear h6; 
 Intros h6 h7; Elim h7; Clear h7; Intros h7 h8.
Elim (beta_confluent h5 h8);
 Intros P h9; Elim h9; Clear h9; Intros h9 h10.
Elim (C_star h9 h3 h4); Intros P1 h11; Elim h11; Clear h11; Intros T1 h11;
 Elim h11; Clear h11; Intros h11 h12; Elim h12; Clear h12; Intros h12 h13.
Elim (C_star h10 h6 h7); Intros P2 h14; Elim h14; Clear h14; Intros T2 h14;
 Elim h14; Clear h14; Intros h14 h15; Elim h15; Clear h15; Intros h15 h16.
Assert h17 := (kahrs_trans (kahrs_symm h11) h14).
Assert h18 := (kahrs_omega_commute h17 h12 h15).
Exists P1; Exists P2; Split; [ Exact h13 | Split; [ Exact h16 | Exact h18 ]].
Qed.

End confluence_of_lambda_beta.
