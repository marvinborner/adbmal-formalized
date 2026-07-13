Require Export balancedness.
Require Export adbmal_subst_lems.

Set Implicit Arguments.

Section scope_balanced_substitution_lemmas.

(** 
  [closed_subst_lemma_scb] Closed Substitution Lemma for scope-balanced terms;
  follows from [closed_subst_lemma_msv].
  [[

  s[X1yX2,x:=t,W][Z,y:=u,WX1] = s[X1ZX2,x:=t[Z,y:=u,X1],W]

  ]]
*)

Lemma closed_subst_lemma_scb :
 (s,t,u:Adbmal;X1,X2,W,Z:stack;x,y:name)
  (adbmal_subst Z (juxt W X1) (adbmal_subst (juxt X1 (cons y X2)) W s x t) y u)
   = (adbmal_subst (juxt X1 (juxt Z X2)) W s x (adbmal_subst Z X1 t y u)).
Proof
 [s,t,u;X1,X2,W,Z;x,y]
  (closed_subst_lemma_msv s t u W Z 9!Nil x (scope_subtract_neg_scb X1 X2 y)(refl_equal name y)).



(** 
  [open_subst_lemma_scb] Open Substitution Lemma for scope-balanced terms;
  follows from [open_subst_lemma].
  [[

  s[Y1,x:=t,W][Z,y:=u,WY1Y2] = s[Z,y:=u,WxY2][Y1,x:=t[Z,y:=u,Y1Y2],W]
  s[X,x:=t,X'][Y,y:=u,X'XY'] = s[Y,y:=u,X'xY'][X,x:=t[Y,y:=u,XY'],X']
  ]]
*)

Lemma open_subst_lemma_scb :
 (s,t,u:Adbmal;Y1,Y2,W,Z:stack;x,y:name)
  (adbmal_subst Z (juxt W (juxt Y1 Y2)) (adbmal_subst Y1 W s x t) y u)
   = (adbmal_subst Y1 W (adbmal_subst Z (juxt W (cons x Y2)) s y u) x 
                            (adbmal_subst Z (juxt Y1 Y2) t y u)).
Proof [s,t,u;Y1,Y2,W,Z;x,y](open_subst_lemma s t u W Z x y (scope_subtract_pos_scb Y1 Y2)).

(** 
  Scope-balancedness is closed under substitution.
  [[

  <YxZ>t,<XZ>u -> <YXZ>t[X,x:=u,Y]

  ]]
*)
Lemma scb_subst :
 (t,u:Adbmal;X,Y,Z:stack;x:name)
 (scb (juxt Y (cons x Z)) t)
  -> (scb (juxt X Z) u)
  -> (scb (juxt Y (juxt X Z)) (adbmal_subst X Y t x u)).
Proof.
Induction t; Simpl.
(* var y *)
Intros y u X Y Z x bt bu.
Case (in_dec y Y); Intro h.
Apply scb_var.
Case (eq_dec x y); Intro h0.
Apply scb_eoss.
Exact bu.
Apply scb_eoss.
Apply scb_eoss.
Apply scb_var.
(* abs y t' *)
Intros y t' ih u X Y Z x bt bu.
Apply scb_abs.
Replace (cons y (juxt Y (juxt X Z))) with (juxt (cons y Y) (juxt X Z)); 
 [ Apply ih | Reflexivity ].
Simpl.
Apply scb_abs_inv.
Exact bt.
Exact bu.
(* eos y t' *)
Intros y t' ih u X Y Z x.
Case Y; Simpl.
Intros bt bu.
Case (eq_dec x y); Intro h.
Apply scb_eoss.
Elim (scb_eos_inv bt).
Trivial.
Elim (scb_eos_inv bt); Intros h0 h1.
Elim h; Symmetry; Exact h0.
Intros a Y' bt bu.
Elim (scb_eos_inv bt).
Intros h h0.
Case (eq_dec y a); Intro h1.
Rewrite h1.
Apply scb_eos.
Apply ih.
Exact h0.
Exact bu.
Elim (h1 h).
(* ap t1 t2 *)
Intros t1 ih1 t2 ih2 u X Y Z x bt bu.
Elim (scb_ap_inv bt).
Intros bt1 bt2.
Apply scb_ap.
Apply ih1 with 1:=bt1 2:=bu.
Apply ih2 with 1:=bt2 2:=bu.
Qed.

(** 
  [scb_beta] Scope-balancedness is closed under beta reduction.
  [[
 
   t-->t' -> <X>t -> <X>t'

  ]]
*)

Lemma scb_beta : (M,N:Adbmal)(adbmal_beta M N)->(Y:stack)(scb Y M)->(scb Y N).
Proof.
NewInduction 1; Intros Y b.
Exact (scb_abs (IHadbmal_beta (cons x Y) (scb_abs_inv b))).
Elim (scb_eos_inv2 b); Intros Y' h; Elim h; Clear h; Intros h h0.
Rewrite h.
Exact (scb_eos x (IHadbmal_beta Y' h0)).
Elim (scb_ap_inv b); Intros b1 b2.
Apply scb_ap.
Exact (IHadbmal_beta Y b1).
Exact b2.
Elim (scb_ap_inv b); Intros b1 b2.
Apply scb_ap.
Exact b1.
Exact (IHadbmal_beta Y b2).
Elim (scb_ap_inv b); Intros b1 b2.
Elim (scb_eoss_inv b1); Intros X' h; Elim h; Clear h; Intros h h0.
Rewrite <- h.
Rewrite <- h in b2.
Exact (scb_subst 4!Nil (scb_abs_inv h0) b2).
Qed.

(** 
  [scb_multistep] Scope-balancedness is closed under multistep.
  [[
 
   t==>t' -> <X>t -> <X>t'

  ]]
*)

Lemma multistep_subst_scb_lemma :
 (t,t':Adbmal)(multistep t t')->(X:stack)(scb X t)->(scb X t').
Proof.
Intros t t' h.
Elim h; Clear h t t'.
(* var *)
Trivial.
(* abs *)
Intros t t' x h ih X h0.
Apply scb_abs.
Apply ih.
Apply scb_abs_inv.
Exact h0.
(* eos *)
Intros t t' x h ih X h0.
Elim (scb_eos_inv2 h0).
Intros X' h1.
Elim h1.
Intros h2 h3.
Rewrite h2.
Apply scb_eos.
Apply ih.
Exact h3.
(* adbmal_beta *)
Intros t t' s s' x X ht iht hs ihs X' h.
Elim (scb_ap_inv h).
Intros h0 h1.
Elim (scb_eoss_inv h0).
Intros X'' h2.
Elim h2.
Intros h3 h4.
Replace X' with (juxt Nil X'); [ Rewrite <- h3 | Reflexivity ].
Apply scb_subst.
Simpl.
Apply iht.
Apply scb_abs_inv.
Exact h4.
Apply ihs.
Rewrite h3.
Exact h1.
(* ap *)
Intros t t' s s' ht iht hs ihs X h.
Elim (scb_ap_inv h).
Intros bt bs.
Apply scb_ap.
Apply iht.
Exact bt.
Apply ihs.
Exact bs.
Qed.

End scope_balanced_substitution_lemmas.

