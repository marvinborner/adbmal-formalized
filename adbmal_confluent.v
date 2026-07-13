Require Export ars.
Require Export adbmal_subst_lems.

Set Implicit Arguments.

Section adbmal_beta_confluent.

(**
  Multisteps satisfy the diamond property.
*)

Lemma multistep_diamond : (diamond multistep).
Proof. (* messy script *)
Intros t t1 h1.
Elim h1; Clear h1 t t1.
(* multistep_var *)
Intros x t2 h2.
Rewrite (multistep_var_inv h2).
Exists (var x).
Split; Apply multistep_var.
(* multistep_abs *)
Intros t t1 x d1 ih1 t2 h2.
Elim (multistep_abs_inv h2); Intros t2' h.
Elim h; Clear h; Intros e d2.
Rewrite e.
Elim (ih1 t2' d2).
Intros u h.
Elim h; Clear h.
Intros c1 c2.
Exists (abs x u).
Split; Apply multistep_abs.
Exact c1.
Exact c2.
(* multistep_eos *)
Intros t' t1' x d1 ih1 t2 h2.
Elim (multistep_eos_inv h2); Intros t2' h.
Elim h; Clear h; Intros e d2.
Rewrite e.
Elim (ih1 t2' d2); Intros u h.
Elim h; Clear h; Intros c1 c2.
Exists (eos x u).
Split; Apply multistep_eos.
Exact c1.
Exact c2.
(* multistep_beta *)
(* t = (ap (eoss X (abs x p)) q) ; t1 = (adbmal_subst X (nil name) p1 x q1) *)
Intros p p1 q q1 x X dp1 ihp1 dq1 ihq1 t2 h2.
Inversion h2.
Elim (eoss_abs_inj H); Intros h h0; Elim h0; Clear h0; Intros h0 h1.
(* t2 = (adbmal_subst X (nil name) M2 x N2) *)
Rewrite h.
Rewrite h0.
Rewrite h1 in H1.
Elim (ihp1 M2 H1); Intros p' h3.
Elim h3; Clear h3; Intros cp1 cp2.
Elim (ihq1 N2 H3); Intros q' h3; Elim h3; Clear h3; Intros cq1 cq2.
Exists (adbmal_subst X (nil name) p' x q'); Split.
Exact (multistep_subst_lemma cp1 cq1 X Nil x).
Exact (multistep_subst_lemma cp2 cq2 X Nil x).
(* t2 = (ap M2 N2) *)
Elim (multistep_eoss_inv H1); Intros p5 h; Elim h; Clear h; Intros h3 h4.
Elim (multistep_abs_inv h4); Intros p2 h5; Elim h5; Clear h5; Intros h6 dp2.
Rewrite h3.
Rewrite h6.
Elim (ihp1 p2 dp2); Intros p' h; 
 Elim h; Clear h; Intros cp1 cp2.
Elim (ihq1 N2 H3); Intros q' h; Elim h; Clear h; Intros cq1 cq2.
Exists (adbmal_subst X (nil name) p' x q'); Split.
Exact (multistep_subst_lemma cp1 cq1 X Nil x).
Exact (multistep_beta x X cp2 cq2).
(* multistep_ap *)
Intros p p1 q q1 dp1 ihp1 dq1 ihq1 t2 h2.
Inversion h2.
(* t2 = (adbmal_subst X (nil name) M2 x N2) *)
Rewrite <- H in dp1.
Elim (multistep_eoss_inv dp1).
Intros p3 h; Elim h; Clear h; Intros e h3.
Elim (multistep_abs_inv h3); Intros p1' h4; Elim h4; Clear h4; Intros h4 dp1'.
Rewrite h4 in e.
Clear h4 h3 p3.
Rewrite e in ihp1.
Rewrite e.
Rewrite <- H in ihp1.
Elim (ihp1 (eoss X (abs x M2))(multistep_eoss X (multistep_abs x H1)));
 Intros p'' h; Elim h; Clear h; Intros cp1 cp2.
Elim (multistep_eoss_inv cp1); Intros p3 h; Elim h; Clear h; Intros e0 h3.
Elim (multistep_abs_inv h3); Clear h3; Intros p' h; Elim h; Clear h; Intros e1 cp1'.
Rewrite e1 in e0.
Clear e1 p3.
Rewrite e0 in cp2.
Elim (multistep_eoss_inv cp2).
Intros p11 h; Elim h; Clear h; Intros e2 h3.
Elim (multistep_abs_inv h3).
Intros p3 h; Elim h; Clear h; Intros e3 cp2'.
Rewrite e3 in e2.
Clear e3 h3 p11.
Cut (abs x p')=(abs x p3); [ Intro c | Exact (eoss_inj2 e2) ].
Injection c; Intro c'; Rewrite c' in cp1'.
Elim (ihq1 N2 H3); Intros q' h; Elim h; Clear h; Intros cq1 cq2.
Exists (adbmal_subst X (nil name) p3 x q'); Split.
Exact (multistep_beta x X cp1' cq1).
Exact (multistep_subst_lemma cp2' cq2 X Nil x).
(* t2 = (ap M2 N2) *)
Elim (ihp1 M2 H1); Intros p' h; Elim h; Clear h; Intros cp1 cp2.
Elim (ihq1 N2 H3); Intros q' h; Elim h; Clear h; Intros cq1 cq2.
Exists (ap p' q').
Split; Apply multistep_ap; Assumption.
Qed.

(**
  The reflexive-transitive closure of beta-reduction, [(Rstar adbmal_beta)],
  is a congruence.
*)

Lemma adbmal_beta_star_cxt_congr :
 (c:Adbmal->Adbmal)(cxt c)
   ->(t,t':Adbmal)(Rstar adbmal_beta t t')->(Rstar adbmal_beta (c t)(c t')).
Proof.
Intros c h.
Elim h; Clear h c.
Exact [t,u;h]h.
Exact [c,d;hc;ihc;hd;ihd;t;u;h](ihc (d t)(d u)(ihd t u h)).
Intros x t t' h.
Elim h; [ Intro; Apply Rstar_refl
   | Intros; Apply Rstar_ext; Apply beta_abs; Assumption
   | Intros t1 t2 t3 h0 h1 h2 h3; Exact (Rstar_trans h1 h3) ].
Intros x t t' h.
Elim h; [ Intro; Apply Rstar_refl
   | Intros; Apply Rstar_ext; Apply beta_eos; Assumption
   | Intros t1 t2 t3 h0 h1 h2 h3; Exact (Rstar_trans h1 h3) ].
Intros u t t' h.
Elim h; [ Intro; Apply Rstar_refl
   | Intros; Apply Rstar_ext; Apply beta_apl; Assumption
   | Intros t1 t2 t3 h0 h1 h2 h3; Exact (Rstar_trans h1 h3) ].
Intros t u t' h.
Elim h; [ Intro; Apply Rstar_refl
   | Intros; Apply Rstar_ext; Apply beta_apr; Assumption
   | Intros t1 t2 t3 h0 h1 h2 h3; Exact (Rstar_trans h1 h3) ].
Qed.

(**
  [adbmal_beta] is a subrelation of [multistep].
*)

Lemma incl_adbmal_beta_multistep : (incl_rel adbmal_beta multistep).
Proof.
Red.
Intros s t h.
Elim h; Clear h s t.
Intros t t' x h h0.
Apply multistep_abs.
Exact h0.
Intros t t' x h h0.
Apply multistep_eos.
Exact h0.
Intros t t' u h h0.
Apply multistep_ap.
Exact h0.
Apply multistep_refl.
Intros t t' u h h0.
Apply multistep_ap.
Apply multistep_refl.
Exact h0.
Intros t u x X.
Apply multistep_beta; Apply multistep_refl.
Qed.

(**
  [multistep] is a subrelation of [(Rstar adbmal_beta)]. 
*)

Lemma incl_multistep_adbmal_beta_star : (incl_rel multistep (Rstar adbmal_beta)).
Proof.
Red.
Intros s t h.
Elim h; Clear h s t.
Intro; Apply Rstar_refl.
Intros t t' x h h0.
Exact (adbmal_beta_star_cxt_congr (cxt_abs x) h0).
Intros t t' x h h0.
Exact (adbmal_beta_star_cxt_congr (cxt_eos x) h0).
Intros t t' s s' x X mt st ms ss.
Apply Rstar_trans with y:=(ap (eoss X (abs x t')) s).
Exact (adbmal_beta_star_cxt_congr
 (cxt_comp (cxt_apl s) (cxt_comp (cxt_eoss X)(cxt_abs x))) st).
Apply Rstar_trans with y:=(ap (eoss X (abs x t')) s').
Exact (adbmal_beta_star_cxt_congr (cxt_apr (eoss X (abs x t'))) ss).
Apply Rstar_ext.
Apply beta_rule.
Intros t t' s s' mt st ms ss.
Apply Rstar_trans with y:=(ap t' s).
Exact (adbmal_beta_star_cxt_congr (cxt_apl s) st).
Exact (adbmal_beta_star_cxt_congr (cxt_apr t') ss).
Qed.

(**
  Beta-reduction, [adbmal_beta], transits parallel reduction, [multistep].
*)

Lemma transits_adbmal_beta_multistep : (transits adbmal_beta multistep).
Proof (conj ?? incl_adbmal_beta_multistep incl_multistep_adbmal_beta_star).

(**
  Beta-reduction, [adbmal_beta], is confluent on the set of adbmal-terms, [Adbmal]. 
*)

Lemma beta_confluent : (confluent adbmal_beta).
Proof (transits_diamond_confluent transits_adbmal_beta_multistep multistep_diamond).

End adbmal_beta_confluent.
