Require Export ars.
Require Export adbmal_subst_lems.

Set Implicit Arguments.

Section adbmal_beta_confluent.

(**
  Multisteps satisfy the diamond property.
*)

Lemma multistep_diamond : (diamond multistep).
Proof. (* messy script *)
intros t t1 h1.
elim h1; clear h1 t t1.
(* multistep_var *)
intros x t2 h2.
rewrite (multistep_var_inv h2).
exists (var x).
split; apply multistep_var.
(* multistep_abs *)
intros t t1 x d1 ih1 t2 h2.
elim (multistep_abs_inv h2); intros t2' h.
elim h; clear h; intros e d2.
rewrite e.
elim (ih1 t2' d2).
intros u h.
elim h; clear h.
intros c1 c2.
exists (abs x u).
split; apply multistep_abs.
exact c1.
exact c2.
(* multistep_eos *)
intros t' t1' x d1 ih1 t2 h2.
elim (multistep_eos_inv h2); intros t2' h.
elim h; clear h; intros e d2.
rewrite e.
elim (ih1 t2' d2); intros u h.
elim h; clear h; intros c1 c2.
exists (eos x u).
split; apply multistep_eos.
exact c1.
exact c2.
(* multistep_beta *)
(* t = (ap (eoss X (abs x p)) q) ; t1 = (adbmal_subst X (nil name) p1 x q1) *)
intros p p1 q q1 x X dp1 ihp1 dq1 ihq1 t2 h2.
inversion h2.
elim (eoss_abs_inj X0 X x0 x M1 p H); intros h h0;
 elim h0; clear h0; intros h0 h1.
(* t2 = (adbmal_subst X (nil name) M2 x N2) *)
rewrite h.
rewrite h0.
rewrite h1 in H1.
elim (ihp1 M2 H1); intros p' h3.
elim h3; clear h3; intros cp1 cp2.
elim (ihq1 N2 H3); intros q' h3; elim h3; clear h3; intros cq1 cq2.
exists (adbmal_subst X (@nil name) p' x q'); split.
exact (multistep_subst_lemma cp1 cq1 X (@nil name) x).
exact (multistep_subst_lemma cp2 cq2 X (@nil name) x).
(* t2 = (ap M2 N2) *)
elim (multistep_eoss_inv X (abs x p) H1); intros p5 h;
 elim h; clear h; intros h3 h4.
elim (multistep_abs_inv h4); intros p2 h5; elim h5; clear h5; intros h6 dp2.
rewrite h3.
rewrite h6.
elim (ihp1 p2 dp2); intros p' h;
 elim h; clear h; intros cp1 cp2.
elim (ihq1 N2 H3); intros q' h; elim h; clear h; intros cq1 cq2.
exists (adbmal_subst X (@nil name) p' x q'); split.
exact (multistep_subst_lemma cp1 cq1 X (@nil name) x).
exact (multistep_beta x X cp2 cq2).
(* multistep_ap *)
intros p p1 q q1 dp1 ihp1 dq1 ihq1 t2 h2.
inversion h2.
(* t2 = (adbmal_subst X (nil name) M2 x N2) *)
rewrite <- H in dp1.
elim (multistep_eoss_inv X _ dp1).
intros p3 h; elim h; clear h; intros e h3.
elim (multistep_abs_inv h3); intros p1' h4; elim h4; clear h4; intros h4 dp1'.
rewrite h4 in e.
clear h4 h3 p3.
rewrite e in ihp1.
rewrite e.
rewrite <- H in ihp1.
elim (ihp1 (eoss X (abs x M2))(multistep_eoss X (multistep_abs x H1)));
 intros p'' h; elim h; clear h; intros cp1 cp2.
elim (multistep_eoss_inv X _ cp1); intros p3 h;
 elim h; clear h; intros e0 h3.
elim (multistep_abs_inv h3); clear h3; intros p' h; elim h; clear h; intros e1 cp1'.
rewrite e1 in e0.
clear e1 p3.
rewrite e0 in cp2.
elim (multistep_eoss_inv X _ cp2).
intros p11 h; elim h; clear h; intros e2 h3.
elim (multistep_abs_inv h3).
intros p3 h; elim h; clear h; intros e3 cp2'.
rewrite e3 in e2.
clear e3 h3 p11.
cut (abs x p' = abs x p3);
 [ intro c | exact (eoss_inj2 X (abs x p') (abs x p3) e2) ].
injection c; intro c'; rewrite c' in cp1'.
elim (ihq1 N2 H3); intros q' h; elim h; clear h; intros cq1 cq2.
exists (adbmal_subst X (@nil name) p3 x q'); split.
exact (multistep_beta x X cp1' cq1).
exact (multistep_subst_lemma cp2' cq2 X (@nil name) x).
(* t2 = (ap M2 N2) *)
elim (ihp1 M2 H1); intros p' h; elim h; clear h; intros cp1 cp2.
elim (ihq1 N2 H3); intros q' h; elim h; clear h; intros cq1 cq2.
exists (ap p' q').
split; apply multistep_ap; assumption.
Qed.

(**
  The reflexive-transitive closure of beta-reduction, [(Rstar adbmal_beta)],
  is a congruence.
*)

Lemma adbmal_beta_star_cxt_congr :
 forall c : Adbmal -> Adbmal, cxt c ->
   forall t t' : Adbmal,
     Rstar adbmal_beta t t' -> Rstar adbmal_beta (c t) (c t').
Proof.
intros c h.
elim h; clear h c.
exact (fun t u h => h).
exact (fun c d hc ihc hd ihd t u h => ihc (d t) (d u) (ihd t u h)).
intros x t t' h.
elim h; [ intro; apply Rstar_refl
   | intros; apply Rstar_ext; apply beta_abs; assumption
   | intros t1 t2 t3 h0 h1 h2 h3; exact (Rstar_trans h1 h3) ].
intros x t t' h.
elim h; [ intro; apply Rstar_refl
   | intros; apply Rstar_ext; apply beta_eos; assumption
   | intros t1 t2 t3 h0 h1 h2 h3; exact (Rstar_trans h1 h3) ].
intros u t t' h.
elim h; [ intro; apply Rstar_refl
   | intros; apply Rstar_ext; apply beta_apl; assumption
   | intros t1 t2 t3 h0 h1 h2 h3; exact (Rstar_trans h1 h3) ].
intros t u t' h.
elim h; [ intro; apply Rstar_refl
   | intros; apply Rstar_ext; apply beta_apr; assumption
   | intros t1 t2 t3 h0 h1 h2 h3; exact (Rstar_trans h1 h3) ].
Qed.

(**
  [adbmal_beta] is a subrelation of [multistep].
*)

Lemma incl_adbmal_beta_multistep : (incl_rel adbmal_beta multistep).
Proof.
red.
intros s t h.
elim h; clear h s t.
intros t t' x h h0.
apply multistep_abs.
exact h0.
intros t t' x h h0.
apply multistep_eos.
exact h0.
intros t t' u h h0.
apply multistep_ap.
exact h0.
apply multistep_refl.
intros t t' u h h0.
apply multistep_ap.
apply multistep_refl.
exact h0.
intros t u x X.
apply multistep_beta; apply multistep_refl.
Qed.

(**
  [multistep] is a subrelation of [(Rstar adbmal_beta)]. 
*)

Lemma incl_multistep_adbmal_beta_star : (incl_rel multistep (Rstar adbmal_beta)).
Proof.
red.
intros s t h.
elim h; clear h s t.
intro; apply Rstar_refl.
intros t t' x h h0.
exact (adbmal_beta_star_cxt_congr (cxt_abs x) h0).
intros t t' x h h0.
exact (adbmal_beta_star_cxt_congr (cxt_eos x) h0).
intros t t' s s' x X mt st ms ss.
apply Rstar_trans with (y := ap (eoss X (abs x t')) s).
exact (adbmal_beta_star_cxt_congr
 (cxt_comp (cxt_apl s) (cxt_comp (cxt_eoss X)(cxt_abs x))) st).
apply Rstar_trans with (y := ap (eoss X (abs x t')) s').
exact (adbmal_beta_star_cxt_congr (cxt_apr (eoss X (abs x t'))) ss).
apply Rstar_ext.
apply beta_rule.
intros t t' s s' mt st ms ss.
apply Rstar_trans with (y := ap t' s).
exact (adbmal_beta_star_cxt_congr (cxt_apl s) st).
exact (adbmal_beta_star_cxt_congr (cxt_apr t') ss).
Qed.

(**
  Beta-reduction, [adbmal_beta], transits parallel reduction, [multistep].
*)

Lemma transits_adbmal_beta_multistep : (transits adbmal_beta multistep).
Proof (conj incl_adbmal_beta_multistep incl_multistep_adbmal_beta_star).

(**
  Beta-reduction, [adbmal_beta], is confluent on the set of adbmal-terms, [Adbmal]. 
*)

Lemma beta_confluent : (confluent adbmal_beta).
Proof (transits_diamond_confluent transits_adbmal_beta_multistep multistep_diamond).

End adbmal_beta_confluent.
