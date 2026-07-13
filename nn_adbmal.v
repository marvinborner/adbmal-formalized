Require Export ars.

Infix 4  "-->" beta .
Infix 4  "==>" multistep .

Set Implicit Arguments.

Section unnamed_adbmal_calculus.

Inductive trm : Set :=
| var : trm                (* variable *)
| abs : trm -> trm         (* abstraction *)
| eos : trm -> trm         (* end-of-scope *)
| ap  : trm -> trm -> trm. (* application *)

(* unary `contexts' (built from abs,eos,ap only) *)

Inductive cxt : (trm->trm)->Prop :=
| cxt_id  : (cxt [t]t)
| cxt_comp: (c,c':trm->trm)(cxt c)->(cxt c')->(cxt [t](c (c' t)))
| cxt_abs : (cxt abs)
| cxt_eos : (cxt eos)
| cxt_apl : (u:trm)(cxt [t](ap t u))
| cxt_apr : (t:trm)(cxt [u](ap t u)).


(* N is used to represent lists of (/unary contexts over) eos's
   rather than nat to avoid the use of commutativity lemmas etc. (...)
   and to parallel the (def,prf) structures of the named counterparts.
*)

Inductive N : Set := base : N | next : N -> N.

(* plus/append *)
Fixpoint pls [n:N] : N -> N :=
[m] Cases n of
| base     => m
|(next n') => (next (pls n' m))
end.

(* n eos's *)
Fixpoint eoss [n:N] : trm->trm :=
[t] Cases n of
| base     => t
|(next n') => (eos (eoss n' t))
end.

Fixpoint subst [n,m:N;t:trm] : trm->trm :=
[u] Cases t of
| var => Cases m of
         | base    => u
         |(next _) => var
         end
|(abs t') => (abs (subst n (next m) t' u))
|(eos t') => Cases m of
             | base     => (eoss n t')
             |(next m') => (eos (subst n m' t' u))
             end
|(ap t1 t2) => (ap (subst n m t1 u)(subst n m t2 u))
end.

(* *)
Inductive beta : trm->trm->Prop :=
| beta_abs : (t,t':trm) t-->t' -> (abs t)-->(abs t')
| beta_eos : (t,t':trm) t-->t' -> (eos t)-->(eos t')
| beta_apl : (t,t',u:trm) t-->t' -> (ap t u)-->(ap t' u)
| beta_apr : (t,t',u:trm) t-->t' -> (ap u t)-->(ap u t')
| beta_rule: (t,u:trm;n:N)(ap (eoss n (abs t)) u)-->(subst n base t u).

(* parallel reduction *)
Inductive multistep : trm->trm->Prop :=
| ms_var : var==>var
| ms_abs : (t,t':trm) t==>t' -> (abs t)==>(abs t')
| ms_eos : (t,t':trm) t==>t' -> (eos t)==>(eos t')
| ms_beta: (t,t',s,s':trm;n:N) t==>t' -> s==>s'
            -> (ap (eoss n (abs t)) s)==>(subst n base t' s')
| ms_ap : (t,t',s,s':trm) t==>t' -> s==>s' -> (ap t s)==>(ap t' s').

Lemma eoss_lls : (n,m:N;t:trm)(eoss (pls n m) t)=(eoss n (eoss m t)).
Proof.
Intros n m t.
Elim n.
Reflexivity.
Intros n' IH.
Simpl.
Apply (f_equal trm).
Exact IH.
Qed.

Lemma pls_ass : (n,m,k:N)(pls (pls n m) k)=(pls n (pls m k)).
Proof.
Induction n.
Reflexivity.
Intros n' IH m k.
Simpl.
Rewrite IH.
Reflexivity.
Qed.

(* plus n O / append n nil *)
Lemma pls_n_base : (n:N)(pls n base)=n.
Proof.
Induction n.
Reflexivity.
Intros n' IH.
Simpl.
Rewrite IH.
Reflexivity.
Qed.

Lemma le_or_gt_N :
 (n,m:N)(EX k:N | m=(pls n k))(*n<=m*)\/(EX k:N | n=(pls m (next k)))(*n>m*).
Proof.
Induction n.
Destruct m.
Left. Exists base. Reflexivity.
Intro m'. Left. Exists (next m'). Reflexivity.
Intros n' IH m.
Case m.
Right. Exists n'. Reflexivity.
Intro m'.
Elim (IH m'); Intro H; Elim H; Clear H; Intros k H; Rewrite H.
Left. Exists k. Reflexivity.
Right. Exists k.  Reflexivity.
Qed.

Lemma ms_refl : (t:trm)t==>t.
Proof.
Induction t; Clear t.
Apply ms_var.
Intros t h. Apply ms_abs. Exact h.
Intros t h. Apply ms_eos. Exact h.
Intros t h u h0. Apply ms_ap. Exact h. Exact h0.
Qed.

Lemma cxt_eoss : (n:N)(cxt (eoss n)).
Proof.
Induction n.
Exact cxt_id.
Intros n' ih.
Simpl.
Exact (cxt_comp cxt_eos ih).
Qed.

Lemma beta_eoss :
 (n:N;t,t':trm)(beta t t')->(beta (eoss n t)(eoss n t')).
Proof.
Intros n t t' h.
Elim n.
Exact h.
Exact [n';ih](beta_eos ih).
Qed.

Lemma ms_eoss : (t,t':trm;n:N)(multistep t t')->(multistep (eoss n t)(eoss n
t')).
Proof.
Induction n.
Exact [h]h.
Intros n' ih h.
Simpl.
Apply ms_eos.
Exact (ih h).
Qed.

(* inversion lemmas are preferred above the use of Inversion tactic;
 the large proof terms it constructs are now folded and opaque in proofs
 which use inversion (e.g. diamond_multistep). *)

Lemma ms_var_inv : (t:trm)(multistep var t)->t=var.
Proof.
Intros t h.
Inversion_clear h.
Reflexivity.
Qed.

Lemma ms_abs_inv :
 (t,u:trm)
  (multistep (abs t) u)
   ->(EX t' | u=(abs t')/\(multistep t t')).
Proof.
Intros t u h.
Inversion_clear h.
Exists t'.
Split; Auto.
Qed.

Lemma ms_eos_inv :
 (t,u:trm)
  (multistep (eos t) u)
   ->(EX t' | u=(eos t')/\(multistep t t')).
Proof.
Intros t u h.
Inversion_clear h.
Exists t'.
Split; Auto.
Qed.

Lemma ms_eoss_inv :
 (n:N;t,u:trm)
  (multistep (eoss n t) u)
   ->(EX t' | u=(eoss n t')/\(multistep t t')).
Proof.
Induction n.
Intros t u h.
Exists u.
Split.
Reflexivity.
Exact h.
Intros n' ih t u h.
Simpl in h.
Elim (ms_eos_inv h).
Intros t' h0.
Elim h0.
Intros h1 h2.
Simpl.
Elim (ih t t' h2).
Intros t'' h3.
Elim h3.
Intros h4 h5.
Exists t''.
Split.
Rewrite h1.
Rewrite h4.
Reflexivity.
Exact h5.
Qed.

Lemma ms_ap_inv :
 (p,q,r:trm)
  (multistep (ap p q) r)
   ->(EX n|(EX s|(EX s'|(EX q'|
      p=(eoss n (abs s))/\r=(subst n base s' q')
       /\ (multistep s s')/\(multistep q q')))))
   \/ (EX p'|(EX q'|r=(ap p' q')/\(multistep p p')/\(multistep q q'))).
Proof.
Intros p q r h.
Inversion_clear h.
Left.
Exists n.
Exists t.
Exists t'.
Exists s'.
Split.
Reflexivity.
Split.
Reflexivity.
Split; Assumption.
Right.
Exists t'.
Exists s'.
Split.
Reflexivity.
Split; Assumption.
Qed.

Lemma eoss_inj : (n:N;t,t':trm)(eoss n t)=(eoss n t')->t=t'.
Proof.
Intros n t t'.
Elim n; Simpl.
Exact [h]h.
Intros n' ih h.
Injection h.
Intro h0.
Exact (ih h0).
Qed.

Lemma eoss_abs_inj :
 (t,u:trm;n,m:N)(eoss n (abs t))=(eoss m (abs u))->n=m/\t=u.
Proof.
Intros t u n.
Elim n.
Destruct m.
Intro h.
Split.
Reflexivity.
Injection h.
Exact [h]h.
Intros m' h.
Inversion h.
Intros n' ih.
Destruct m; Simpl.
Intro h.
Inversion h.
Intros m' h.
Injection h.
Intro h0.
Elim (ih m' h0).
Intros h1 h2.
Split.
Rewrite h1.
Reflexivity.
Exact h2.
Qed.

Lemma subst_eoss :
 (t,u:trm;n,k,m:N)
  (subst n (pls m k)(eoss m t) u)=(eoss m (subst n k t u)).
Proof.
Induction m.
Reflexivity.
Intros m' IH.
Simpl.
Apply (f_equal trm).
Exact IH.
Qed.

Lemma closed_subst_lem :
 (s,t,u:trm;n,n',m,m':N)
  (subst n' (pls m m')(subst (pls m' (next n)) m s t) u)
   = (subst (pls m' (pls n' n)) m s (subst n' m' t u)).
Proof.
Induction s.
(* s = var *)
Intros t u n n' m m'.
Case m; Reflexivity.
(* s = abs s' *)
Intros s' IH t u n n' m m'.
Simpl.
Apply (f_equal trm).
Exact (IH t u n n' (next m) m').
(* s = eos s' *)
Intros s' IH t u n n' m m'.
Case m; Simpl.
 (* m = base *)
 Rewrite (eoss_lls m' (next n)).
 Pattern 1 m'.
 Rewrite <- (pls_n_base m').
 Rewrite (subst_eoss (eoss (next n) s') u n' base m').
 Simpl.
 Rewrite eoss_lls.
 Rewrite eoss_lls.
 Reflexivity.
 (* m = next m0 *)
 Intro m0.
 Apply (f_equal trm).
 Apply IH.
(* s = ap s1 s2 *)
Intros s1 IH1 s2 IH2 t u n n' m m'.
Simpl.
Rewrite (IH1 t u n n' m m').
Rewrite (IH2 t u n n' m m').
Reflexivity.
Qed.

Lemma open_subst_lem :
 (s,t,u:trm;n,n',m,m':N)
  (subst n (pls m (pls n' m')) (subst n' m s t) u)
  = (subst n' m (subst n (pls m (next m')) s u)
                       (subst n (pls n' m') t u) ).
Proof.
Induction s.
(* s = var *)
Destruct m; Reflexivity.
(* s = abs s' *)
Intros s' IH t u n n' m m'.
Simpl.
Apply (f_equal trm).
Exact (IH t u n n' (next m) m').
(* s = eos s' *)
Intros s' IH t u n n' m m'.
Case m; Simpl.
 (* m = base *)
Apply subst_eoss.
 (* next m0 *)
Intro m0.
Apply (f_equal trm).
Apply IH.
(* s = ap s1 s2 *)
Intros s1 IH1 s2 IH2 t u n n' m m'.
Simpl.
Rewrite (IH1 t u n n' m m').
Rewrite (IH2 t u n n' m m').
Reflexivity.
Qed.

(* multistep substitution lemma *)

Lemma multistep_subst :
 (t,t',u,u':trm) t==>t' -> u==>u' -> (n,m:N)(subst n m t u)==>(subst n m t' u').
Proof.
Intros t t' u u' h0 h.
Elim h0; Clear h0 t t'; Simpl.
(* ms_var *)
Destruct m.
Exact h.
Intro. Exact ms_var.
(* ms_abs *)
Intros t t' h0 h1 n m.
Apply ms_abs.
Apply h1.
(* ms_eos *)
Intros t t' h0 h1 n m.
Case m.
Apply ms_eoss.
Exact h0.
Intro m'.
Apply ms_eos.
Apply h1.
(* ms_beta *)
Intros s s' t t' n h0 h1 h2 h3 m m'.
Elim (le_or_gt_N n m'); Intro H; Elim H; Clear H; Intros p H; Rewrite H.
(* n <= m' *)
Rewrite subst_eoss.
Simpl.
Replace (pls n p) with (pls base (pls n p));
 [ Rewrite open_subst_lem | Reflexivity ].
Simpl.
Apply ms_beta.
Apply h1.
Apply h3.
(* n > m' *)
Rewrite eoss_lls.
Simpl.
Pattern 1 m'.
Rewrite <- pls_n_base.
Rewrite subst_eoss.
Simpl.
Rewrite <- eoss_lls.
Rewrite <- eoss_lls.
Pattern 3 m'.
Replace m' with (pls base m'); [ Rewrite closed_subst_lem | Reflexivity ].
Rewrite pls_ass.
Apply ms_beta.
Exact h0.
Apply h3.
(* ms_ap *)
Intros t t' s s' h0 h1 h2 h3 n m.
Apply ms_ap.
Apply h1.
Apply h3.
Qed.

Section Confluence.

Lemma multistep_diamond : (diamond multistep).
Proof.
Unfold diamond diamond'.
Intros t t1 h1.
Elim h1.
(* ms_var *)
Intros t2 h2.
Rewrite (ms_var_inv h2).
Exists var.
Split; Apply ms_var.
(* ms_abs *)
Intros t' t1' d1 ih1 t2 h2.
Elim (ms_abs_inv h2).
Intros t2' h.
Elim h; Clear h.
Intros h3 d2.
Rewrite h3.
Elim (ih1 t2' d2).
Intros u h.
Elim h; Clear h.
Intros c1 c2.
Exists (abs u).
Split; Apply ms_abs; Assumption.
(* ms_eos *)
Intros t' t1' d1 ih1 t2 h2.
Elim (ms_eos_inv h2).
Intros t2' h.
Elim h; Clear h.
Intros h3 d2.
Rewrite h3.
Elim (ih1 t2' d2).
Intros u h.
Elim h; Clear h.
Intros c1 c2.
Exists (eos u).
Split; Apply ms_eos; Assumption.
(* ms_beta *)
(* t = (ap (eoss n (abs p)) q) ; t1 = (subst n base p1 q1) *)
Intros p p1 q q1 n dp1 ihp1 dq1 ihq1 t2 h2.
Inversion h2.
(* t2 = (subst n0 base t' s') *)
Elim (eoss_abs_inj H).
Intros h h0.
Rewrite h0 in H1.
Rewrite h.
Elim (ihp1 t' H1).
Intros p' h3.
Elim h3.
Intros cp1 cp2.
Elim (ihq1 s' H3).
Intros q' h4.
Elim h4.
Intros cq1 cq2.
Exists (subst n base p' q').
Split; Apply multistep_subst; Assumption.
(* t2 = (ap t' s') *)
Elim (ms_eoss_inv H1).
Intros p5 h.
Elim h.
Intros h3 h4.
Elim (ms_abs_inv h4).
Intros p2 h5.
Elim h5.
Intros h6 dp2.
Clear h h5.
Rewrite h3.
Rewrite h6.
Elim (ihp1 p2 dp2).
Intros p' h.
Elim h; Clear h; Intros cp1 cp2.
Elim (ihq1 s' H3).
Intros q' h.
Elim h; Clear h; Intros cq1 cq2.
Exists (subst n base p' q').
Split.
Apply multistep_subst.
Exact cp1.
Exact cq1.
Apply ms_beta.
Exact cp2.
Exact cq2.
(* ms_ap *)
(* use of inversion lemma's instead of Inversion tactic, messy script ... *)
(* t = ap p q ; t1 = ap p1 q1 *)
Intros p p1 q q1 dp1 ihp1 dq1 ihq1 t2 h2.
Elim (ms_ap_inv h2); Intro h.
(* t2 = (subst n base p2 q2) *)
Elim h.
Intros n h3.
Elim h3.
Intros p0 h4.
Elim h4.
Intros p2 h5.
Elim h5.
Intros q2 h6.
Elim h6.
Intros h7 h8.
Elim h8.
Intros h9 h10.
Elim h10.
Intros dp2 dq2.
Clear h h3 h4 h5 h6 h8 h10.
Rewrite h7 in dp1.
Elim (ms_eoss_inv dp1).
Intros p27 h.
Elim h.
Intros h3 h4.
Elim (ms_abs_inv h4).
Intros p1' h5.
Elim h5.
Intro h6.
Rewrite h6 in h3.
Clear h h4 h5 h6 p27.
Intro dp1'.
Rewrite h7 in ihp1.
Rewrite h3 in ihp1.
Elim (ihp1 (eoss n (abs p2))(ms_eoss n (ms_abs dp2))).
Intros p'' cp.
Elim cp.
Intros cp1 cp2.
Elim (ms_eoss_inv cp1).
Intros p27 h.
Elim h.
Intros h4 h5.
Elim (ms_abs_inv h5).
Intros p' h6.
Elim h6.
Intros h8 cp1'.
Rewrite h4 in cp2.
Rewrite h8 in cp2.
Clear h h4 h5 h6 h8 p27 cp.
Elim (ihq1 q2 dq2).
Intros q' h.
Elim h. Clear h.
Intros cq1 cq2.
Exists (subst n base p' q').
Split.
Rewrite h3.
Apply ms_beta.
Exact cp1'.
Exact cq1.
Rewrite h9.
Apply multistep_subst.
Elim (ms_eoss_inv cp2).
Intros p27 h.
Elim h.
Intros h4 h5.
Elim (ms_abs_inv h5).
Intros pprime h6.
Elim h6.
Intros h8 cp2'.
Rewrite h8 in h4.
Cut p'=pprime.
Intro h0.
Rewrite h0.
Exact cp2'.
Cut (abs p')=(abs pprime);
 [ Intro sighhh; Injection sighhh; Exact [h]h | Exact (eoss_inj h4) ].
Exact cq2.
(* t2 = ap p2 q2 *)
Elim h.
Intros p2 h3.
Elim h3.
Intros q2 h4.
Elim h4.
Intros h5 h6.
Elim h6.
Intros dp2 dq2.
Elim (ihp1 p2 dp2).
Intros p' h7.
Elim h7.
Intros cp1 cp2.
Elim (ihq1 q2 dq2).
Intros q' h8.
Elim h8.
Intros cq1 cq2.
Exists (ap p' q').
Rewrite h5.
Split; Apply ms_ap; Assumption.
Qed.

Lemma adbmal_beta_star_cxt_congr :
 (c:trm->trm)(cxt c)
   ->(t,t':trm)(Rstar beta t t')->(Rstar beta (c t)(c t')).
Proof.
Intros c h.
Elim h; Clear h c.
Exact [t,u;h]h.
Exact [c,d;hc;ihc;hd;ihd;t;u;h](ihc (d t)(d u)(ihd t u h)).
Intros t t' h.
Elim h; [ Intro; Apply Rstar_refl
   | Intros; Apply Rstar_ext; Apply beta_abs; Assumption
   | Intros x y z h0 h1 h2 h3; Exact (Rstar_trans h1 h3) ].
Intros t t' h.
Elim h; [ Intro; Apply Rstar_refl
   | Intros; Apply Rstar_ext; Apply beta_eos; Assumption
   | Intros x y z h0 h1 h2 h3; Exact (Rstar_trans h1 h3) ].
Intros u t t' h.
Elim h; [ Intro; Apply Rstar_refl
   | Intros; Apply Rstar_ext; Apply beta_apl; Assumption
   | Intros x y z h0 h1 h2 h3; Exact (Rstar_trans h1 h3) ].
Intros t u t' h.
Elim h; [ Intro; Apply Rstar_refl
   | Intros; Apply Rstar_ext; Apply beta_apr; Assumption
   | Intros x y z h0 h1 h2 h3; Exact (Rstar_trans h1 h3) ].
Qed.

Lemma incl_beta_multistep : (incl_rel beta multistep).
Proof.
Red.
Intros s t h.
Elim h; Clear h s t.
Intros t t' h h0.
Apply ms_abs.
Exact h0.
Intros t t' h h0.
Apply ms_eos.
Exact h0.
Intros t t' u h h0.
Apply ms_ap.
Exact h0.
Apply ms_refl.
Intros t t' u h h0.
Apply ms_ap.
Apply ms_refl.
Exact h0.
Intros t u n.
Apply ms_beta; Apply ms_refl.
Qed.

Lemma incl_multistep_beta_star : (incl_rel multistep (Rstar beta)).
Proof.
Red.
Intros s t h.
Elim h; Clear h s t.
Apply Rstar_refl.
Intros t t' h h0.
Exact (adbmal_beta_star_cxt_congr cxt_abs h0).
Intros t t' h h0.
Exact (adbmal_beta_star_cxt_congr cxt_eos h0).
Intros t t' s s' n mt st ms ss.
Apply Rstar_trans with y:=(ap (eoss n (abs t')) s).
Exact (adbmal_beta_star_cxt_congr
 (cxt_comp (cxt_apl s) (cxt_comp (cxt_eoss n) cxt_abs)) st).
Apply Rstar_trans with y:=(ap (eoss n (abs t')) s').
Exact (adbmal_beta_star_cxt_congr (cxt_apr (eoss n (abs t'))) ss).
Apply Rstar_ext.
Apply beta_rule.
Intros t t' s s' mt st ms ss.
Apply Rstar_trans with y:=(ap t' s).
Exact (adbmal_beta_star_cxt_congr (cxt_apl s) st).
Exact (adbmal_beta_star_cxt_congr (cxt_apr t') ss).
Qed.

Lemma transits_beta_multistep : (transits beta multistep).
Proof (conj ?? incl_beta_multistep incl_multistep_beta_star).

Lemma beta_confluent : (confluent beta).
Proof (transits_diamond_confluent transits_beta_multistep multistep_diamond).

End Confluence.

End unnamed_adbmal_calculus.
