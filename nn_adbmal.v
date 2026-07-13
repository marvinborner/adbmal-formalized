Require Export ars.

Set Implicit Arguments.

Section unnamed_adbmal_calculus.

Inductive trm : Set :=
| var : trm                (* variable *)
| abs : trm -> trm         (* abstraction *)
| eos : trm -> trm         (* end-of-scope *)
| ap  : trm -> trm -> trm. (* application *)

(* unary `contexts' (built from abs,eos,ap only) *)

Inductive cxt : (trm->trm)->Prop :=
| cxt_id  : cxt (fun t => t)
| cxt_comp: forall c c' : trm -> trm,
    cxt c -> cxt c' -> cxt (fun t => c (c' t))
| cxt_abs : (cxt abs)
| cxt_eos : (cxt eos)
| cxt_apl : forall u : trm, cxt (fun t => ap t u)
| cxt_apr : forall t : trm, cxt (fun u => ap t u).


(* N is used to represent lists of (/unary contexts over) eos's
   rather than nat to avoid the use of commutativity lemmas etc. (...)
   and to parallel the (def,prf) structures of the named counterparts.
*)

Inductive N : Set := base : N | next : N -> N.

(* plus/append *)
Fixpoint pls (n : N) : N -> N :=
fun m => match n with
| base     => m
|(next n') => (next (pls n' m))
end.

(* n eos's *)
Fixpoint eoss (n : N) : trm -> trm :=
fun t => match n with
| base     => t
|(next n') => (eos (eoss n' t))
end.

Fixpoint subst (n m : N) (t : trm) : trm -> trm :=
fun u => match t with
| var => match m with
         | base    => u
         |(next _) => var
         end
|(abs t') => (abs (subst n (next m) t' u))
|(eos t') => match m with
             | base     => (eoss n t')
             |(next m') => (eos (subst n m' t' u))
             end
|(ap t1 t2) => (ap (subst n m t1 u)(subst n m t2 u))
end.

(* *)
Inductive beta : trm->trm->Prop :=
| beta_abs : forall t t' : trm, beta t t' -> beta (abs t) (abs t')
| beta_eos : forall t t' : trm, beta t t' -> beta (eos t) (eos t')
| beta_apl : forall t t' u : trm, beta t t' -> beta (ap t u) (ap t' u)
| beta_apr : forall t t' u : trm, beta t t' -> beta (ap u t) (ap u t')
| beta_rule: forall (t u : trm) (n : N),
    beta (ap (eoss n (abs t)) u) (subst n base t u).

Infix "-->" := beta (at level 70).

(* parallel reduction *)
Inductive multistep : trm->trm->Prop :=
| ms_var : multistep var var
| ms_abs : forall t t' : trm,
    multistep t t' -> multistep (abs t) (abs t')
| ms_eos : forall t t' : trm,
    multistep t t' -> multistep (eos t) (eos t')
| ms_beta: forall (t t' s s' : trm) (n : N),
    multistep t t' -> multistep s s' ->
    multistep (ap (eoss n (abs t)) s) (subst n base t' s')
| ms_ap : forall t t' s s' : trm,
    multistep t t' -> multistep s s' -> multistep (ap t s) (ap t' s').

Infix "==>" := multistep (at level 70).

Lemma eoss_lls : forall (n m : N) (t : trm),
  eoss (pls n m) t = eoss n (eoss m t).
Proof.
intros n m t.
elim n.
reflexivity.
intros n' IH.
simpl.
apply f_equal.
exact IH.
Qed.

Lemma pls_ass : forall n m k : N, pls (pls n m) k = pls n (pls m k).
Proof.
intros n m k.
induction n as [|n IH]; simpl.
reflexivity.
rewrite IH; reflexivity.
Qed.

(* plus n O / append n nil *)
Lemma pls_n_base : forall n : N, pls n base = n.
Proof.
intro n.
induction n as [|n IH]; simpl.
reflexivity.
rewrite IH; reflexivity.
Qed.

Lemma le_or_gt_N :
 forall n m : N,
   (exists k : N, m = pls n k)(*n<=m*)\/
   (exists k : N, n = pls m (next k))(*n>m*).
Proof.
intro n.
induction n as [|n IH]; intro m.
destruct m as [|m].
left; exists base; reflexivity.
left; exists (next m); reflexivity.
destruct m as [|m].
right; exists n; reflexivity.
destruct (IH m) as [[k H] | [k H]]; rewrite H.
left; exists k; reflexivity.
right; exists k; reflexivity.
Qed.

Lemma ms_refl : forall t : trm, t ==> t.
Proof.
intro t.
induction t as [|t h|t h|t h u h0].
apply ms_var.
apply ms_abs; exact h.
apply ms_eos; exact h.
apply ms_ap; assumption.
Qed.

Lemma cxt_eoss : forall n : N, cxt (eoss n).
Proof.
intro n.
induction n as [|n ih].
exact cxt_id.
simpl.
exact (cxt_comp cxt_eos ih).
Qed.

Lemma beta_eoss :
 forall (n : N) (t t' : trm), beta t t' -> beta (eoss n t) (eoss n t').
Proof.
intros n t t' h.
elim n.
exact h.
exact (fun n' ih => beta_eos ih).
Qed.

Lemma ms_eoss : forall (t t' : trm) (n : N),
  multistep t t' -> multistep (eoss n t) (eoss n t').
Proof.
intros t t' n h.
induction n as [|n ih].
exact h.
simpl.
apply ms_eos.
exact ih.
Qed.

(* inversion lemmas are preferred above the use of Inversion tactic;
 the large proof terms it constructs are now folded and opaque in proofs
 which use inversion (e.g. diamond_multistep). *)

Lemma ms_var_inv : forall t : trm, multistep var t -> t = var.
Proof.
intros t h.
inversion_clear h.
reflexivity.
Qed.

Lemma ms_abs_inv :
 forall t u : trm, multistep (abs t) u ->
   exists t' : trm, u = abs t' /\ multistep t t'.
Proof.
intros t u h.
inversion_clear h.
exists t'.
split; auto.
Qed.

Lemma ms_eos_inv :
 forall t u : trm, multistep (eos t) u ->
   exists t' : trm, u = eos t' /\ multistep t t'.
Proof.
intros t u h.
inversion_clear h.
exists t'.
split; auto.
Qed.

Lemma ms_eoss_inv :
 forall (n : N) (t u : trm), multistep (eoss n t) u ->
   exists t' : trm, u = eoss n t' /\ multistep t t'.
Proof.
intro n.
induction n as [|n ih].
intros t u h.
exists u.
split.
reflexivity.
exact h.
intros t u h.
simpl in h.
elim (ms_eos_inv h).
intros t' h0.
elim h0.
intros h1 h2.
simpl.
elim (ih t t' h2).
intros t'' h3.
elim h3.
intros h4 h5.
exists t''.
split.
rewrite h1.
rewrite h4.
reflexivity.
exact h5.
Qed.

Lemma ms_ap_inv :
 forall p q r : trm, multistep (ap p q) r ->
   (exists n : N, exists s : trm, exists s' : trm, exists q' : trm,
      p = eoss n (abs s) /\ r = subst n base s' q' /\
      multistep s s' /\ multistep q q')
   \/ (exists p' : trm, exists q' : trm,
      r = ap p' q' /\ multistep p p' /\ multistep q q').
Proof.
intros p q r h.
inversion_clear h.
left.
exists n.
exists t.
exists t'.
exists s'.
split.
reflexivity.
split.
reflexivity.
split; assumption.
right.
exists t'.
exists s'.
split.
reflexivity.
split; assumption.
Qed.

Lemma eoss_inj : forall (n : N) (t t' : trm), eoss n t = eoss n t' -> t = t'.
Proof.
intros n t t'.
elim n; simpl.
exact (fun h => h).
intros n' ih h.
injection h.
intro h0.
exact (ih h0).
Qed.

Lemma eoss_abs_inj :
 forall (t u : trm) (n m : N),
   eoss n (abs t) = eoss m (abs u) -> n = m /\ t = u.
Proof.
intros t u n.
induction n as [|n ih]; intro m; destruct m as [|m]; simpl; intro h.
split.
reflexivity.
injection h; exact (fun h => h).
discriminate h.
discriminate h.
injection h as h.
destruct (ih m h) as [h1 h2].
split.
now rewrite h1.
exact h2.
Qed.

Lemma subst_eoss :
 forall (t u : trm) (n k m : N),
   subst n (pls m k) (eoss m t) u = eoss m (subst n k t u).
Proof.
intros t u n k m.
induction m as [|m IH].
reflexivity.
simpl.
apply f_equal.
exact IH.
Qed.

Lemma closed_subst_lem :
 forall (s t u : trm) (n n' m m' : N),
   subst n' (pls m m') (subst (pls m' (next n)) m s t) u =
   subst (pls m' (pls n' n)) m s (subst n' m' t u).
Proof.
intro s.
induction s as [|s IH|s IH|s1 IH1 s2 IH2].
(* s = var *)
intros t u n n' m m'.
destruct m; reflexivity.
(* s = abs s' *)
intros t u n n' m m'.
simpl.
apply f_equal.
exact (IH t u n n' (next m) m').
(* s = eos s' *)
intros t u n n' m m'.
destruct m; simpl.
 (* m = base *)
 rewrite (eoss_lls m' (next n)).
 pattern m' at 1.
 rewrite <- (pls_n_base m').
 rewrite (subst_eoss (eoss (next n) s) u n' base m').
 simpl.
 rewrite eoss_lls.
 rewrite eoss_lls.
 reflexivity.
 (* m = next m0 *)
 apply f_equal.
 apply IH.
(* s = ap s1 s2 *)
intros t u n n' m m'.
simpl.
rewrite (IH1 t u n n' m m').
rewrite (IH2 t u n n' m m').
reflexivity.
Qed.

Lemma open_subst_lem :
 forall (s t u : trm) (n n' m m' : N),
   subst n (pls m (pls n' m')) (subst n' m s t) u =
   subst n' m (subst n (pls m (next m')) s u)
              (subst n (pls n' m') t u).
Proof.
intro s.
induction s as [|s IH|s IH|s1 IH1 s2 IH2].
(* s = var *)
intros t u n n' m m'.
destruct m; reflexivity.
(* s = abs s' *)
intros t u n n' m m'.
simpl.
apply f_equal.
exact (IH t u n n' (next m) m').
(* s = eos s' *)
intros t u n n' m m'.
destruct m; simpl.
 (* m = base *)
apply subst_eoss.
 (* next m0 *)
apply f_equal.
apply IH.
(* s = ap s1 s2 *)
intros t u n n' m m'.
simpl.
rewrite (IH1 t u n n' m m').
rewrite (IH2 t u n n' m m').
reflexivity.
Qed.

(* multistep substitution lemma *)

Lemma multistep_subst :
 forall t t' u u' : trm, t ==> t' -> u ==> u' -> forall n m : N,
   subst n m t u ==> subst n m t' u'.
Proof.
intros t t' u u' h0 h.
elim h0; clear h0 t t'; simpl.
(* ms_var *)
destruct m.
exact h.
exact ms_var.
(* ms_abs *)
intros t t' h0 h1 n m.
apply ms_abs.
apply h1.
(* ms_eos *)
intros t t' h0 h1 n m.
destruct m.
apply ms_eoss.
exact h0.
apply ms_eos.
apply h1.
(* ms_beta *)
intros s s' t t' n h0 h1 h2 h3 m m'.
elim (le_or_gt_N n m'); intro H; elim H; clear H; intros p H; rewrite H.
(* n <= m' *)
rewrite subst_eoss.
simpl.
replace (pls n p) with (pls base (pls n p));
 [ rewrite open_subst_lem | reflexivity ].
simpl.
apply ms_beta.
apply h1.
apply h3.
(* n > m' *)
rewrite eoss_lls.
simpl.
pattern m' at 1.
rewrite <- pls_n_base.
rewrite subst_eoss.
simpl.
rewrite <- eoss_lls.
rewrite <- eoss_lls.
pattern m' at 3.
replace m' with (pls base m'); [ rewrite closed_subst_lem | reflexivity ].
rewrite pls_ass.
apply ms_beta.
exact h0.
apply h3.
(* ms_ap *)
intros t t' s s' h0 h1 h2 h3 n m.
apply ms_ap.
apply h1.
apply h3.
Qed.

Section Confluence.

Lemma multistep_diamond : (diamond multistep).
Proof.
unfold diamond, diamond'.
intros t t1 h1.
elim h1.
(* ms_var *)
intros t2 h2.
rewrite (ms_var_inv h2).
exists var.
split; apply ms_var.
(* ms_abs *)
intros t' t1' d1 ih1 t2 h2.
elim (ms_abs_inv h2).
intros t2' h.
elim h; clear h.
intros h3 d2.
rewrite h3.
elim (ih1 t2' d2).
intros u h.
elim h; clear h.
intros c1 c2.
exists (abs u).
split; apply ms_abs; assumption.
(* ms_eos *)
intros t' t1' d1 ih1 t2 h2.
elim (ms_eos_inv h2).
intros t2' h.
elim h; clear h.
intros h3 d2.
rewrite h3.
elim (ih1 t2' d2).
intros u h.
elim h; clear h.
intros c1 c2.
exists (eos u).
split; apply ms_eos; assumption.
(* ms_beta *)
(* t = (ap (eoss n (abs p)) q) ; t1 = (subst n base p1 q1) *)
intros p p1 q q1 n dp1 ihp1 dq1 ihq1 t2 h2.
inversion h2.
(* t2 = (subst n0 base t' s') *)
elim (eoss_abs_inj t0 p n0 n H).
intros h h0.
rewrite h0 in H1.
rewrite h.
elim (ihp1 t' H1).
intros p' h3.
elim h3.
intros cp1 cp2.
elim (ihq1 s' H3).
intros q' h4.
elim h4.
intros cq1 cq2.
exists (subst n base p' q').
split; apply multistep_subst; assumption.
(* t2 = (ap t' s') *)
elim (ms_eoss_inv n (abs p) H1).
intros p5 h.
elim h.
intros h3 h4.
elim (ms_abs_inv h4).
intros p2 h5.
elim h5.
intros h6 dp2.
clear h h5.
rewrite h3.
rewrite h6.
elim (ihp1 p2 dp2).
intros p' h.
elim h; clear h; intros cp1 cp2.
elim (ihq1 s' H3).
intros q' h.
elim h; clear h; intros cq1 cq2.
exists (subst n base p' q').
split.
apply multistep_subst.
exact cp1.
exact cq1.
apply ms_beta.
exact cp2.
exact cq2.
(* ms_ap *)
(* use of inversion lemma's instead of Inversion tactic, messy script ... *)
(* t = ap p q ; t1 = ap p1 q1 *)
intros p p1 q q1 dp1 ihp1 dq1 ihq1 t2 h2.
elim (ms_ap_inv h2); intro h.
(* t2 = (subst n base p2 q2) *)
elim h.
intros n h3.
elim h3.
intros p0 h4.
elim h4.
intros p2 h5.
elim h5.
intros q2 h6.
elim h6.
intros h7 h8.
elim h8.
intros h9 h10.
elim h10.
intros dp2 dq2.
clear h h3 h4 h5 h6 h8 h10.
rewrite h7 in dp1.
elim (ms_eoss_inv n _ dp1).
intros p27 h.
elim h.
intros h3 h4.
elim (ms_abs_inv h4).
intros p1' h5.
elim h5.
intro h6.
rewrite h6 in h3.
clear h h4 h5 h6 p27.
intro dp1'.
rewrite h7 in ihp1.
rewrite h3 in ihp1.
elim (ihp1 (eoss n (abs p2))(ms_eoss n (ms_abs dp2))).
intros p'' cp.
elim cp.
intros cp1 cp2.
elim (ms_eoss_inv n _ cp1).
intros p27 h.
elim h.
intros h4 h5.
elim (ms_abs_inv h5).
intros p' h6.
elim h6.
intros h8 cp1'.
rewrite h4 in cp2.
rewrite h8 in cp2.
clear h h4 h5 h6 h8 p27 cp.
elim (ihq1 q2 dq2).
intros q' h.
elim h. clear h.
intros cq1 cq2.
exists (subst n base p' q').
split.
rewrite h3.
apply ms_beta.
exact cp1'.
exact cq1.
rewrite h9.
apply multistep_subst.
elim (ms_eoss_inv n _ cp2).
intros p27 h.
elim h.
intros h4 h5.
elim (ms_abs_inv h5).
intros pprime h6.
elim h6.
intros h8 cp2'.
rewrite h8 in h4.
cut (p' = pprime).
intro h0.
rewrite h0.
exact cp2'.
cut (abs p' = abs pprime);
 [ intro sighhh; injection sighhh; exact (fun h => h)
 | exact (eoss_inj n (abs p') (abs pprime) h4) ].
exact cq2.
(* t2 = ap p2 q2 *)
elim h.
intros p2 h3.
elim h3.
intros q2 h4.
elim h4.
intros h5 h6.
elim h6.
intros dp2 dq2.
elim (ihp1 p2 dp2).
intros p' h7.
elim h7.
intros cp1 cp2.
elim (ihq1 q2 dq2).
intros q' h8.
elim h8.
intros cq1 cq2.
exists (ap p' q').
rewrite h5.
split; apply ms_ap; assumption.
Qed.

Lemma adbmal_beta_star_cxt_congr :
 forall c : trm -> trm, cxt c -> forall t t' : trm,
   Rstar beta t t' -> Rstar beta (c t) (c t').
Proof.
intros c h.
elim h; clear h c.
exact (fun t u h => h).
exact (fun c d hc ihc hd ihd t u h => ihc (d t) (d u) (ihd t u h)).
intros t t' h.
elim h; [ intro; apply Rstar_refl
   | intros; apply Rstar_ext; apply beta_abs; assumption
   | intros x y z h0 h1 h2 h3; exact (Rstar_trans h1 h3) ].
intros t t' h.
elim h; [ intro; apply Rstar_refl
   | intros; apply Rstar_ext; apply beta_eos; assumption
   | intros x y z h0 h1 h2 h3; exact (Rstar_trans h1 h3) ].
intros u t t' h.
elim h; [ intro; apply Rstar_refl
   | intros; apply Rstar_ext; apply beta_apl; assumption
   | intros x y z h0 h1 h2 h3; exact (Rstar_trans h1 h3) ].
intros t u t' h.
elim h; [ intro; apply Rstar_refl
   | intros; apply Rstar_ext; apply beta_apr; assumption
   | intros x y z h0 h1 h2 h3; exact (Rstar_trans h1 h3) ].
Qed.

Lemma incl_beta_multistep : (incl_rel beta multistep).
Proof.
red.
intros s t h.
elim h; clear h s t.
intros t t' h h0.
apply ms_abs.
exact h0.
intros t t' h h0.
apply ms_eos.
exact h0.
intros t t' u h h0.
apply ms_ap.
exact h0.
apply ms_refl.
intros t t' u h h0.
apply ms_ap.
apply ms_refl.
exact h0.
intros t u n.
apply ms_beta; apply ms_refl.
Qed.

Lemma incl_multistep_beta_star : (incl_rel multistep (Rstar beta)).
Proof.
red.
intros s t h.
elim h; clear h s t.
apply Rstar_refl.
intros t t' h h0.
exact (adbmal_beta_star_cxt_congr cxt_abs h0).
intros t t' h h0.
exact (adbmal_beta_star_cxt_congr cxt_eos h0).
intros t t' s s' n mt st ms ss.
apply Rstar_trans with (y := ap (eoss n (abs t')) s).
exact (adbmal_beta_star_cxt_congr
 (cxt_comp (cxt_apl s) (cxt_comp (cxt_eoss n) cxt_abs)) st).
apply Rstar_trans with (y := ap (eoss n (abs t')) s').
exact (adbmal_beta_star_cxt_congr (cxt_apr (eoss n (abs t'))) ss).
apply Rstar_ext.
apply beta_rule.
intros t t' s s' mt st ms ss.
apply Rstar_trans with (y := ap t' s).
exact (adbmal_beta_star_cxt_congr (cxt_apl s) st).
exact (adbmal_beta_star_cxt_congr (cxt_apr t') ss).
Qed.

Lemma transits_beta_multistep : (transits beta multistep).
Proof. exact (conj incl_beta_multistep incl_multistep_beta_star). Qed.

Lemma beta_confluent : (confluent beta).
Proof.
  exact (transits_diamond_confluent transits_beta_multistep multistep_diamond).
Qed.

End Confluence.

End unnamed_adbmal_calculus.
