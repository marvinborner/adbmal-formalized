Require Export name.

Set Implicit Arguments.

Section lambda_calculus.

Inductive Lambda : Set :=
| var_l : name->Lambda            (* variable    *)
| abs_l : name->Lambda->Lambda    (* abstraction *)
| ap_l  : Lambda->Lambda->Lambda. (* application *)

Fixpoint FV_l_rec (t : Lambda) (X : stack) : stack :=
  match t with
  | var_l x => match in_dec x X with left _ => Nil | right _ => cons x Nil end
  | abs_l x t' => FV_l_rec t' (cons x X)
  | ap_l t1 t2 => juxt (FV_l_rec t1 X) (FV_l_rec t2 X)
  end.

Definition FV_l := fun M => FV_l_rec M Nil.

Fixpoint rename_l (M : Lambda) (x y : name) : Lambda :=
  match M with
  | var_l z => match eq_dec z x with left _ => var_l y | right _ => var_l z end
  | abs_l z m =>
      match eq_dec z x with
      | left _ => abs_l z m (* no renaming *)
      | right _ => abs_l z (rename_l m x y)
      end
  | ap_l m n => ap_l (rename_l m x y) (rename_l n x y)
  end.

Fixpoint names_l (M : Lambda) : stack :=
  match M with
  | var_l x => cons x Nil
  | abs_l x t => cons x (names_l t)
  | ap_l t u => juxt (names_l t) (names_l u)
  end.

Inductive skel_l : Set :=
| skel_l_var : skel_l
| skel_l_abs : skel_l->skel_l
| skel_l_ap  : skel_l->skel_l->skel_l.

Fixpoint skeleton_l (M : Lambda) : skel_l :=
  match M with
  | var_l _ => skel_l_var
  | abs_l _ m => skel_l_abs (skeleton_l m)
  | ap_l m n => skel_l_ap (skeleton_l m) (skeleton_l n)
  end.

Lemma rename_l_skel_eq : 
 forall (M : Lambda) (x y : name),
  (skeleton_l (rename_l M x y))=(skeleton_l M).
Proof.
induction M; intros x y; simpl.
destruct (eq_dec n x); reflexivity.
destruct (eq_dec n x); simpl.
reflexivity.
rewrite IHM; reflexivity.
rewrite IHM1; rewrite IHM2; reflexivity.
Qed.

(* discriminable equalities *)

Definition skel_l_discr_var_abs : 
 forall (A : Set) (s : skel_l), skel_l_var=(skel_l_abs s)->A.
Proof. intros A s h; discriminate h. Defined.

Definition skel_l_discr_var_ap : 
 forall (A : Set) (s1 s2 : skel_l), skel_l_var=(skel_l_ap s1 s2)->A.
Proof. intros A s1 s2 h; discriminate h. Defined.

Definition skel_l_discr_abs_var : 
 forall (A : Set) (s : skel_l), (skel_l_abs s)=skel_l_var->A.
Proof. intros A s h; discriminate h. Defined.

Definition skel_l_discr_abs_ap : 
 forall (A : Set) (s s1 s2 : skel_l), (skel_l_abs s)=(skel_l_ap s1 s2)->A.
Proof. intros A s s1 s2 h; discriminate h. Defined.

Definition skel_l_discr_ap_var : 
 forall (A : Set) (s1 s2 : skel_l), (skel_l_ap s1 s2)=skel_l_var->A.
Proof. intros A s1 s2 h; discriminate h. Defined.

Definition skel_l_discr_ap_abs : 
 forall (A : Set) (s s1 s2 : skel_l), (skel_l_ap s1 s2)=(skel_l_abs s)->A.
Proof. intros A s s1 s2 h; discriminate h. Defined.

Definition skel_l_inj_abs : 
 forall s s' : skel_l, (skel_l_abs s)=(skel_l_abs s') -> s=s'.
Proof. intros s s' h; injection h; intro h0; exact h0. Defined.

Definition skel_l_inj_ap : 
 forall s1 s2 t1 t2 : skel_l,
  (skel_l_ap s1 s2)=(skel_l_ap t1 t2) -> s1=t1/\s2=t2.
Proof. intros s1 s2 t1 t2 h; injection h; intros h0 h1; exact (conj h1 h0).
Defined.

Definition in_10 := 
 fun (y : name) (l : stack) =>
   match in_dec y l with left _ => S O | right _ => O end.

Unset Implicit Arguments.

(** 
Substitution M[x:=N], main call:
[[

(lambda_subst M x N) 
 = (lambda_subst_skel_rec M (skeleton_l M) x N Nil (refl_equal skel_l (skeleton_l M)))

]]
recursive in skeleton of [M] (skeleton of [(rename_l M y y' Nil)] equals skeleton of [M].)
Capture of free variables in N is avoided by renaming lambda's 'on the fly':
 [[

(\y.M)[x:=N] = (\y'.M[y:=y'])[x:=N] if y free in N, for y' fresh w.r.t. FV(MN)

]] 
*)

Fixpoint lambda_subst_skel_rec
  (t : Lambda) (s : skel_l) (x : name) (u : Lambda)
  (d : skeleton_l t = s) {struct s} : Lambda :=
  (match s as s0 return skeleton_l t = s0 -> Lambda with
   | skel_l_var =>
       match t as t0 return skeleton_l t0 = skel_l_var -> Lambda with
       | var_l y => fun _ =>
           match eq_dec y x with left _ => u | right _ => var_l y end
       | abs_l _ _ => fun h => skel_l_discr_abs_var Lambda h
       | ap_l _ _ => fun h => skel_l_discr_ap_var Lambda h
       end
   | skel_l_abs s' =>
       match t as t0 return skeleton_l t0 = skel_l_abs s' -> Lambda with
       | var_l _ => fun h => skel_l_discr_var_abs Lambda h
       | abs_l y t' => fun h =>
           let FVu := FV_l u in
           let fix aux
             (z : name) (p : Lambda) (dp : skeleton_l p = s')
             (n : nat) {struct n} : Lambda :=
             match n with
             | O => abs_l z (lambda_subst_skel_rec p s' x u dp)
             | S m =>
                 let y' := fresh (cons x (juxt (names_l p) FVu)) in
                 aux y' (rename_l p z y')
                   (eq_trans (rename_l_skel_eq p z y') dp) m
             end
           in aux
             (*z*) y
             (*p*) t'
             (*d*) (skel_l_inj_abs h)
             (*n*) (in_10 y (cons x FVu))
       | ap_l _ _ => fun h => skel_l_discr_ap_abs Lambda h
       end
   | skel_l_ap s1 s2 =>
       match t as t0 return skeleton_l t0 = skel_l_ap s1 s2 -> Lambda with
       | var_l _ => fun h => skel_l_discr_var_ap Lambda h
       | abs_l _ _ => fun h => skel_l_discr_abs_ap Lambda h
       | ap_l t1 t2 => fun h =>
           let c := skel_l_inj_ap h in
           ap_l (lambda_subst_skel_rec t1 s1 x u (proj1 c))
                (lambda_subst_skel_rec t2 s2 x u (proj2 c))
       end
   end) d.

Set Implicit Arguments.

Definition lambda_subst := fun t x u =>
  lambda_subst_skel_rec t (skeleton_l t) x u (eq_refl (skeleton_l t)).

Lemma lambda_subst_skel_rec_repl_skel :
 forall (s : skel_l) (t u : Lambda) (x : name)
   (d : skeleton_l t = s) (s' : skel_l) (d' : skeleton_l t = s'),
  (lambda_subst_skel_rec t s x u d)
   =(lambda_subst_skel_rec t s' x u d').
Proof.
intros s t u x d s' d'.
destruct d; destruct d'; reflexivity.
Qed.

Lemma subst_l_var1 : 
 forall (y x : name) (N : Lambda),
  y = x 
   -> (lambda_subst (var_l y) x N) = N.
Proof.
intros y x N h; unfold lambda_subst; simpl.
destruct (eq_dec y x) as [h0|h0].
reflexivity.
elim (h0 h).
Qed.

Lemma subst_l_var2 : 
 forall (y x : name) (N : Lambda),
  ~(y = x)
   -> (lambda_subst (var_l y) x N) = (var_l y).
Proof.
intros y x N h; unfold lambda_subst; simpl.
destruct (eq_dec y x) as [h0|h0].
elim (h h0).
reflexivity.
Qed.

Lemma subst_l_abs1 : 
 forall (y : name) (M : Lambda) (x : name) (N : Lambda),
 let y' := fresh (cons x (juxt (names_l M) (FV_l N))) in
  (In y (cons x (FV_l N)))
   -> (lambda_subst (abs_l y M) x N) = (lambda_subst (abs_l y' (rename_l M y y')) x N).
Proof.
intros y M x N y' h; unfold lambda_subst; simpl (* --> body of skeleton_l unfolded, why? *);
 unfold in_10; fold skeleton_l.
destruct (in_dec y (cons x (FV_l N))) as [h0|h0].
fold y'.
destruct (in_dec y' (cons x (FV_l N))) as [h1|h1].
assert (h2 : In y' (cons x (juxt (names_l M) (FV_l N)))).
elim h1; intro h2.
left; exact h2.
right; apply in_or_juxt; right; exact h2.
elim (fresh_not_in (cons x (juxt (names_l M) (FV_l N))) h2).
set (d := eq_trans (rename_l_skel_eq M y y')
                   (eq_refl (skeleton_l M))).
set (d' := eq_refl (skeleton_l (rename_l M y y'))).
rewrite (@lambda_subst_skel_rec_repl_skel
  (skeleton_l M) (rename_l M y y') N x d
  (skeleton_l (rename_l M y y')) d'); reflexivity.
elim (h0 h).
Qed.

Lemma subst_l_abs2 : 
 forall (y : name) (M : Lambda) (x : name) (N : Lambda),
  ~(In y (cons x (FV_l N)))
    -> (lambda_subst (abs_l y M) x N) = (abs_l y (lambda_subst M x N)).
Proof.
intros y M x N h; unfold lambda_subst; simpl; unfold in_10; fold skeleton_l.
destruct (in_dec y (cons x (FV_l N))) as [h0|h0].
elim (h h0).
reflexivity.
Qed.

Lemma subst_l_ap : 
 forall (M1 M2 : Lambda) (x : name) (N : Lambda),
  (lambda_subst (ap_l M1 M2) x N) = (ap_l (lambda_subst M1 x N)(lambda_subst M2 x N)).
Proof.
intros M1 M2 x N.
unfold lambda_subst; simpl; fold skeleton_l.
f_equal; apply lambda_subst_skel_rec_repl_skel.
Qed.

(* closure of adbmal_beta-rule (lambda_beta_rule) under Adbmal-constructors *)

Inductive lambda_beta : Lambda->Lambda->Prop :=
| lambda_beta_abs : forall (M N : Lambda) (x : name),
    lambda_beta M N -> lambda_beta (abs_l x M) (abs_l x N)
| lambda_beta_apl : forall (M M' N : Lambda),
    lambda_beta M M' -> lambda_beta (ap_l M N) (ap_l M' N)
| lambda_beta_apr : forall (M M' N : Lambda),
    lambda_beta M M' -> lambda_beta (ap_l N M) (ap_l N M')
| lambda_beta_rule : forall (M N : Lambda) (x : name),
    lambda_beta (ap_l (abs_l x M) N) (lambda_subst M x N).


(*----------------------------------------------------------------*)

Require Export alpha.

Fixpoint emb (M : Lambda) : Adbmal :=
  match M with
  | var_l x => var x
  | abs_l x m => abs x (emb m)
  | ap_l m1 m2 => ap (emb m1) (emb m2)
  end.

Lemma lambda_eos_free : forall M : Lambda, eos_free (emb M).
Proof.
induction M.
exact I.
exact IHM.
split; [ exact IHM1 | exact IHM2 ].
Qed.

Lemma lambda_scope_balanced : forall M : Lambda, scope_balanced (emb M).
Proof. intro M; exact (eos_free_scb (emb M) Nil (lambda_eos_free M)). Qed.

Lemma FV_l2s : forall (M : Lambda) (X : stack), FV (emb M) X = FV_l_rec M X.
Proof.
induction M; intro X.
reflexivity.
exact (IHM (cons n X)).
simpl; rewrite IHM1; rewrite IHM2; reflexivity.
Qed.

Lemma rename_l2s : 
 forall (x y : name) (M : Lambda) (X : stack),
  ~(In x X)
   ->(emb (rename_l M x y)) = (rename (emb M) x y X).
Proof.
induction M; intros X h; simpl.
destruct (in_dec n X) as [h0|h0]; destruct (eq_dec n x) as [h1|h1].
elim h; rewrite <- h1; exact h0.
reflexivity.
reflexivity.
reflexivity.
destruct (eq_dec n x) as [h0|h0].
rewrite rename_eos_free_in_stack.
reflexivity.
apply lambda_eos_free.
left; exact h0.
rewrite <- IHM.
reflexivity.
intro h1; elim h1; [ exact h0 | exact h ].
rewrite (IHM1 X h); rewrite (IHM2 X h); reflexivity.
Qed.

Lemma names_l2s : forall M : Lambda, names_l M = names (emb M).
Proof.
induction M; simpl.
reflexivity.
rewrite IHM; reflexivity.
rewrite IHM1; rewrite IHM2; reflexivity.
Qed.

Lemma FV_lambda_subst_skel_rec_sub :
 forall (x : name) (N : Lambda) (s : skel_l) (M : Lambda)
   (d : skeleton_l M = s) (Y : stack),
  (sub (FV_l_rec (lambda_subst_skel_rec M s x N d) Y) (juxt (FV_l_rec M Y) (FV_l N))).
Proof.
intros x N s; induction s; intros M d Y;
 destruct M as [n | n t | t1 t2]; simpl.
assert (a : sub (FV_l_rec N Y) (FV_l N)).
unfold FV_l; rewrite <- FV_l2s; rewrite <- FV_l2s.
rewrite (juxt_nil_end Y).
exact (@FV_sub1 (emb N) Nil Y Nil).
destruct (eq_dec n x) as [h|h]; simpl; destruct (in_dec n Y) as [h0|h0].
exact a.
intros u h1; right; exact (a u h1).
apply sub_nil.
intros u h1; left; elim h1; intro h2.
exact h2.
elim h2.
discriminate d.
discriminate d.
discriminate d.
unfold in_10; destruct (in_dec n (cons x (FV_l N))) as [h|h].
simpl.
set (y' := fresh (cons x (juxt (names_l t) (FV_l N)))).
set (d' := eq_trans (rename_l_skel_eq t n y') (skel_l_inj_abs d)).
assert (h0 := IHs (rename_l t n y') d' (cons y' Y)).
assert (h1 : kahrs' (emb t) (cons n Y)
                     (rename (emb t) n y' Nil) (cons y' Y)).
 assert (h1' : ~ In y' (names_l t)).
 intro h2.
 apply (fresh_not_in (cons x (juxt (names_l t) (FV_l N)))).
 fold y'.
 right; apply in_or_juxt; left; exact h2.
 rewrite names_l2s in h1'.
 exact (@kahrs_rename n y' (emb t) Y Nil (fun f => f) h1').
rewrite (juxt_nil_end (cons n Y)) in h1.
rewrite (juxt_nil_end (cons y' Y)) in h1.
assert (h2 := @kahrs_FV_eq (emb t) (rename (emb t) n y' Nil)
                           (cons n Y) (cons y' Y) Nil h1).
rewrite <- (FV_l2s t (cons n Y)).
rewrite h2.
rewrite <- rename_l2s.
rewrite FV_l2s.
exact h0.
exact (fun f => f).
simpl; apply IHs.
discriminate d.
discriminate d.
discriminate d.
fold skeleton_l.
intros u h0; apply in_or_juxt.
elim (in_juxt_or _ _ _ h0); intro h1.
elim (in_juxt_or _ _ _
  (IHs1 t1 (proj1 (skel_l_inj_ap d)) Y u h1)); intros h2.
left; apply in_or_juxt; left; exact h2.
right; exact h2.
elim (in_juxt_or _ _ _
  (IHs2 t2 (proj2 (skel_l_inj_ap d)) Y u h1)); intros h2.
left; apply in_or_juxt; right; exact h2.
right; exact h2.
Qed.

Lemma FV_subst_l_sub : forall (x : name) (M N : Lambda),
  sub (FV_l (lambda_subst M x N)) (juxt (FV_l M) (FV_l N)).
Proof.
intros x M N y h.
exact (@FV_lambda_subst_skel_rec_sub
  x N (skeleton_l M) M (eq_refl (skeleton_l M)) Nil y h).
Qed.

Lemma lambda_subst_skel_rec_not_in :
 forall (x : name) (N : Lambda) (s : skel_l) (M : Lambda)
   (d : skeleton_l M = s) (Z Y : stack),
  ~(In x Y)
   ->~(In x (FV (emb M) Y))
    ->(kahrs' (emb (lambda_subst_skel_rec M s x N d)) (juxt Y Z) (emb M) (juxt Y Z)).
Proof.
intros x N s; induction s; intros M d Z Y h;
 destruct M as [n | y M | M1 M2]; simpl.
destruct (in_dec n Y) as [h0|h0].
intro h1; clear h1.
destruct (eq_dec n x) as [h1|h1].
elim h; rewrite <- h1; exact h0.
apply kahrs_refl.
intro h1.
destruct (eq_dec n x) as [h2|h2].
elim h1; left; exact h2.
apply kahrs_refl.
discriminate d.
discriminate d.
discriminate d.
intro h0.
unfold in_10; destruct (in_dec y (cons x (FV_l N))) as [h1|h1]; simpl.
set (y' := fresh (cons x (juxt (names_l M) (FV_l N)))).
set (d' := eq_trans (rename_l_skel_eq M y y') (skel_l_inj_abs d)).
assert (h2 := fresh_not_in (cons x (juxt (names_l M) (FV_l N)))).
fold y' in h2.
simpl in h2; elim (dmx h2); clear h2; intros h2 h3.
elim (dmx (fun o => h3 (in_or_juxt _ _ _ o)));
 clear h3; intros h3 h4.
rewrite names_l2s in h3.
assert (h5 := @kahrs_rename y y' (emb M) (juxt Y Z) Nil
                            (fun z => z) h3).
simpl in h5.
assert (a1 : kahrs'
  (abs y' (emb (lambda_subst_skel_rec (rename_l M y y') s x N d')))
  (juxt Y Z) (abs y' (emb (rename_l M y y'))) (juxt Y Z)).
apply kahrs_abs.
apply (IHs (rename_l M y y') d' Z (cons y' Y)).
intro h6; elim h6; intro h7.
apply h2; symmetry; exact h7.
exact (h h7).
rewrite (@rename_l2s y y' M Nil (fun z => z)).
rewrite <- (@kahrs_FV_eq (emb M) (rename (emb M) y y' Nil)
                         (cons y Y) (cons y' Y) Z h5).
exact h0.
assert (a2 : kahrs' (abs y' (emb (rename_l M y y'))) (juxt Y Z)
                     (abs y (emb M)) (juxt Y Z)).
apply kahrs_abs.
apply kahrs_symm.
rewrite (@rename_l2s y y' M Nil (fun z => z)).
exact h5.
exact (kahrs_trans a1 a2).
apply kahrs_abs; apply (IHs M (skel_l_inj_abs d) Z (cons y Y)).
intro h2; elim h2; intro h3.
apply h1; left; symmetry; exact h3.
exact (h h3).
exact h0.
discriminate d.
discriminate d.
discriminate d.
fold skeleton_l. 
intro h0.
elim (dmx (fun o => h0 (in_or_juxt _ _ _ o))); intros h1 h2.
apply kahrs_ap.
exact (IHs1 M1 (proj1 (skel_l_inj_ap d)) Z Y h h1).
exact (IHs2 M2 (proj2 (skel_l_inj_ap d)) Z Y h h2).
Qed.

Lemma subst_l_not_in :
 forall (M N : Lambda) (x : name) (Y Z : stack),
  ~(In x Y)
   ->~(In x (FV (emb M) Y))
    ->(kahrs' (emb (lambda_subst M x N)) (juxt Y Z) (emb M) (juxt Y Z)).
Proof.
intros M N x Y Z h h0.
exact (@lambda_subst_skel_rec_not_in
  x N (skeleton_l M) M (eq_refl (skeleton_l M)) Z Y h h0).
Qed.

End lambda_calculus.
