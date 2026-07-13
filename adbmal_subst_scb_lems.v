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
 forall (s t u : Adbmal) (X1 X2 W Z : stack) (x y : name),
  adbmal_subst Z (juxt W X1) (adbmal_subst (juxt X1 (cons y X2)) W s x t) y u
   = adbmal_subst (juxt X1 (juxt Z X2)) W s x (adbmal_subst Z X1 t y u).
Proof
  (fun s t u X1 X2 W Z x y =>
    @closed_subst_lemma_msv s t u X1 X1 X2 W Z Nil x y y
      (scope_subtract_neg_scb X1 X2 y) (eq_refl y)).



(** 
  [open_subst_lemma_scb] Open Substitution Lemma for scope-balanced terms;
  follows from [open_subst_lemma].
  [[

  s[Y1,x:=t,W][Z,y:=u,WY1Y2] = s[Z,y:=u,WxY2][Y1,x:=t[Z,y:=u,Y1Y2],W]
  s[X,x:=t,X'][Y,y:=u,X'XY'] = s[Y,y:=u,X'xY'][X,x:=t[Y,y:=u,XY'],X']
  ]]
*)

Lemma open_subst_lemma_scb :
 forall (s t u : Adbmal) (Y1 Y2 W Z : stack) (x y : name),
  adbmal_subst Z (juxt W (juxt Y1 Y2)) (adbmal_subst Y1 W s x t) y u
   = adbmal_subst Y1 W (adbmal_subst Z (juxt W (cons x Y2)) s y u) x
                            (adbmal_subst Z (juxt Y1 Y2) t y u).
Proof
  (fun s t u Y1 Y2 W Z x y =>
    @open_subst_lemma s t u Y1 Y1 Y2 W Z x y
      (scope_subtract_pos_scb Y1 Y2)).

(** 
  Scope-balancedness is closed under substitution.
  [[

  <YxZ>t,<XZ>u -> <YXZ>t[X,x:=u,Y]

  ]]
*)
Lemma scb_subst :
 forall (t u : Adbmal) (X Y Z : stack) (x : name),
 scb (juxt Y (cons x Z)) t
  -> (scb (juxt X Z) u)
  -> (scb (juxt Y (juxt X Z)) (adbmal_subst X Y t x u)).
Proof.
intro t; induction t as [y|y t' ih|y t' ih|t1 ih1 t2 ih2];
  intros u X Y Z x bt bu; simpl.
(* var y *)
- destruct (in_dec y Y) as [h|h].
  + apply scb_var.
  + destruct (eq_dec x y) as [h0|h0].
    * apply scb_eoss. exact bu.
    * apply scb_eoss. apply scb_eoss. apply scb_var.
(* abs y t' *)
- apply scb_abs.
  replace (cons y (juxt Y (juxt X Z)))
    with (juxt (cons y Y) (juxt X Z)); [|reflexivity].
  apply ih.
  + simpl. apply scb_abs_inv. exact bt.
  + exact bu.
(* eos y t' *)
- destruct Y as [|a Y']; simpl in *.
  + destruct (eq_dec x y) as [h|h].
    * apply scb_eoss.
      destruct (scb_eos_inv bt) as [_ bt']. exact bt'.
    * destruct (scb_eos_inv bt) as [h0 _].
      exfalso. apply h. symmetry. exact h0.
  + destruct (scb_eos_inv bt) as [h h0].
    destruct (eq_dec y a) as [h1|h1].
    * subst a. apply scb_eos. apply ih; assumption.
    * exfalso. apply h1. exact h.
(* ap t1 t2 *)
- destruct (scb_ap_inv bt) as [bt1 bt2].
  apply scb_ap.
  + apply ih1 with (1:=bt1) (2:=bu).
  + apply ih2 with (1:=bt2) (2:=bu).
Qed.

(** 
  [scb_beta] Scope-balancedness is closed under beta reduction.
  [[
 
   t-->t' -> <X>t -> <X>t'

  ]]
*)

Lemma scb_beta : forall M N : Adbmal,
  adbmal_beta M N -> forall Y : stack, scb Y M -> scb Y N.
Proof.
induction 1; intros Y b.
exact (scb_abs (IHadbmal_beta (cons x Y) (scb_abs_inv b))).
elim (scb_eos_inv2 b); intros Y' h; elim h; clear h; intros h h0.
rewrite h.
exact (scb_eos x (IHadbmal_beta Y' h0)).
elim (scb_ap_inv b); intros b1 b2.
apply scb_ap.
exact (IHadbmal_beta Y b1).
exact b2.
elim (scb_ap_inv b); intros b1 b2.
apply scb_ap.
exact b1.
exact (IHadbmal_beta Y b2).
elim (scb_ap_inv b); intros b1 b2.
elim (@scb_eoss_inv X Y (abs x M) b1); intros X' h;
  elim h; clear h; intros h h0.
rewrite <- h.
rewrite <- h in b2.
exact (@scb_subst M N X Nil X' x (scb_abs_inv h0) b2).
Qed.

(** 
  [scb_multistep] Scope-balancedness is closed under multistep.
  [[
 
   t==>t' -> <X>t -> <X>t'

  ]]
*)

Lemma multistep_subst_scb_lemma :
 forall t t' : Adbmal,
   multistep t t' -> forall X : stack, scb X t -> scb X t'.
Proof.
intros t t' h.
elim h; clear h t t'.
(* var *)
trivial.
(* abs *)
intros t t' x h ih X h0.
apply scb_abs.
apply ih.
apply scb_abs_inv.
exact h0.
(* eos *)
intros t t' x h ih X h0.
elim (scb_eos_inv2 h0).
intros X' h1.
elim h1.
intros h2 h3.
rewrite h2.
apply scb_eos.
apply ih.
exact h3.
(* adbmal_beta *)
intros t t' s s' x X ht iht hs ihs X' h.
elim (scb_ap_inv h).
intros h0 h1.
elim (@scb_eoss_inv X X' (abs x t) h0).
intros X'' h2.
elim h2.
intros h3 h4.
rewrite <- h3.
apply (@scb_subst t' s' X Nil X'' x).
apply iht.
apply scb_abs_inv.
exact h4.
apply ihs.
rewrite h3.
exact h1.
(* ap *)
intros t t' s s' ht iht hs ihs X h.
elim (scb_ap_inv h).
intros bt bs.
apply scb_ap.
apply iht.
exact bt.
apply ihs.
exact bs.
Qed.

End scope_balanced_substitution_lemmas.
