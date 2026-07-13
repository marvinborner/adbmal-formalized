Require Export balancedness.
Require Export ars.

Set Implicit Arguments.

Local Arguments in_juxt_or {A l m a} _.
Local Arguments in_or_juxt {A l m a} _.
Local Arguments disjoint_juxt_and {A l l1 l2} _.

(** We define alpha equality in three ways: [kahrs], [church] and [schroer]
    and prove them equivalent. *)

Section Alpha.

Inductive kahrs' : Adbmal -> stack -> Adbmal -> stack -> Prop :=
| kahrs_var1 : forall (x : name), (kahrs' (var x) Nil (var x) Nil)
| kahrs_var2 : forall (x y : name) (X Y : stack), 
   (length X)=(length Y)->(kahrs' (var x)(cons x X)(var y)(cons y Y))
| kahrs_var3 : forall (x x' y y' : name) (X Y : stack), 
   ~(x=x') -> ~(y=y') -> (kahrs' (var x) X (var y) Y)
    -> (kahrs' (var x) (cons x' X) (var y) (cons y' Y))
| kahrs_abs : forall (x y : name) (M N : Adbmal) (X Y : stack), 
   (kahrs' M (cons x X) N (cons y Y))
    -> (kahrs' (abs x M) X (abs y N) Y)
| kahrs_eos1 : forall (x : name) (M N : Adbmal), 
   (kahrs' M Nil N Nil) -> (kahrs' (eos x M) Nil (eos x N) Nil)
| kahrs_eos2 : forall (x y : name) (M N : Adbmal) (X Y : stack), 
   (kahrs' M X N Y) -> (kahrs' (eos x M)(cons x X)(eos y N)(cons y Y))
| kahrs_eos3 : forall (x x' y y' : name) (M N : Adbmal) (X Y : stack), 
   ~(x=x') -> ~(y=y') -> (kahrs' (eos x M) X (eos y N) Y) 
    -> (kahrs' (eos x M)(cons x' X)(eos y N)(cons y' Y))
| kahrs_ap : forall (M1 M2 N1 N2 : Adbmal) (X Y : stack), 
   (kahrs' M1 X N1 Y) -> (kahrs' M2 X N2 Y) 
    -> (kahrs' (ap M1 M2) X (ap N1 N2) Y).

Definition kahrs := fun M N : Adbmal => kahrs' M Nil N Nil.

Inductive skel : Set :=
| var_skel : skel
| abs_skel : skel->skel
| eos_skel : skel->skel
| ap_skel  : skel->skel->skel.

Fixpoint skeleton (M : Adbmal) : skel :=
match M with
| var _   => var_skel
| abs _ m => abs_skel (skeleton m)
| eos _ m => eos_skel (skeleton m)
| ap m n  => ap_skel (skeleton m) (skeleton n)
end.

Lemma kahrs_skel : 
 forall (M N : Adbmal) (X Y : stack), (kahrs' M X N Y)->(skeleton M)=(skeleton N).
Proof.
intros M N X Y h; elim h; clear h M N X Y; simpl.
reflexivity.
reflexivity.
reflexivity.
intros x y M N X Y h ih; rewrite ih; reflexivity.
intros x M N h ih; rewrite ih; reflexivity.
intros x y M N X Y h ih; rewrite ih; reflexivity.
intros x x' y y' M N X Y h h0 h1 ih; rewrite ih; reflexivity.
intros M1 M2 N1 N2 X Y h1 ih1 h2 ih2; rewrite ih1; rewrite ih2; reflexivity.
Qed.

Lemma kahrs_list_length : 
 forall (M N : Adbmal) (X Y : stack), (kahrs' M X N Y)->(length X)=(length Y).
Proof.
induction 1; simpl.
reflexivity.
rewrite H; reflexivity.
rewrite IHkahrs'; reflexivity.
injection IHkahrs'; intro H0; exact H0.
reflexivity.
rewrite IHkahrs'; reflexivity.
rewrite IHkahrs'; reflexivity.
exact IHkahrs'1.
Qed.

(* scope-balancedness is closed under alpha-equivalence *)

Lemma kahrs_scb : 
 forall (M N : Adbmal) (X Y : stack), 
  (kahrs' M X N Y)
   ->(scb X M)
    ->(scb Y N).
Proof.
intros M N X Y h; elim h; clear h M N X Y; simpl.
exact (fun x h => h).
intros x y X Y h h0.
apply scb_var.
intros x x' y y' X Y e1 e2 a ih b.
apply scb_var.
intros x y M N X Y a ih b.
apply scb_abs.
apply ih.
exact (scb_abs_inv b).
intros x M N a ih b.
apply False_ind.
inversion b.
intros x y M N X Y a ih b.
apply scb_eos.
apply ih.
elim (scb_eos_inv b); intros e b'.
exact b'.
intros x x' y y' M N X Y e1 e2 a ih b.
apply False_ind.
apply e1.
elim (scb_eos_inv b); intros e3 b'.
exact e3.
intros M1 M2 N1 N2 X Y a1 ih1 a2 ih2 b.
elim (scb_ap_inv b); intros b1 b2.
apply scb_ap.
exact (ih1 b1).
exact (ih2 b2).
Qed.

Lemma kahrs_scope_balanced : 
 forall (M N : Adbmal), 
  (kahrs M N)
   ->(scope_balanced M)
    ->(scope_balanced N).
Proof.
intros M N a b; exact (kahrs_scb a b).
Qed.

Lemma kahrs_refl : forall (M : Adbmal) (X : stack), (kahrs' M X M X).
Proof.
simple induction M.
intros x X.
elim X.
apply kahrs_var1.
intros x' X' ih.
destruct (eq_dec x x') as [e|e].
rewrite e.
apply kahrs_var2.
reflexivity.
apply (kahrs_var3 e e ih).
intros x t ih X.
apply kahrs_abs.
apply ih.
intros x t ih X.
elim X.
apply kahrs_eos1.
apply ih.
intros x' X' a.
destruct (eq_dec x x') as [e|e].
rewrite e.
apply kahrs_eos2.
apply ih.
exact (kahrs_eos3 e e a).
intros t1 ih1 t2 ih2 X.
apply kahrs_ap.
apply ih1.
apply ih2.
Qed.

Lemma kahrs_symm : 
 forall (M N : Adbmal) (X Y : stack), (kahrs' M X N Y)->(kahrs' N Y M X).
Proof.
intros M N X Y h.
elim h; clear h M N X Y.
intro x.
apply kahrs_var1.
intros x y X Y h.
apply kahrs_var2.
symmetry; exact h.
intros x x' y y' X Y e1 e2 a ih.
exact (kahrs_var3 e2 e1 ih).
intros x y M N X Y a ih.
exact (kahrs_abs ih).
intros x M N a ih.
exact (kahrs_eos1 x ih).
intros x y M N X Y a ih.
exact (kahrs_eos2 y x ih).
intros x x' y y' M N X Y e1 e2 a ih.
exact (kahrs_eos3 e2 e1 ih).
intros M1 M2 N1 N2 X Y a1 ih1 a2 ih2.
exact (kahrs_ap ih1 ih2).
Qed.

Lemma kahrs_trans : 
 forall (M N : Adbmal) (X Y : stack), 
 (kahrs' M X N Y)
  ->forall (P : Adbmal) (Z : stack), (kahrs' N Y P Z)->(kahrs' M X P Z).
Proof.
intros M N X Y h.
elim h; clear h M X N Y.
exact (fun x P Z h => h).
intros x y X Y h P Z h0.
inversion_clear h0.
apply kahrs_var2.
transitivity (length Y); assumption.
apply False_ind.
apply H.
reflexivity.
intros x x' y y' X Y e1 e2 a1 ih P Z a2.
inversion a2.
apply False_ind.
apply e2.
assumption.
apply kahrs_var3.
exact e1.
assumption.
apply ih; assumption.
intros x y M N X Y a1 ih P Z a2.
inversion a2.
apply kahrs_abs.
apply ih; assumption.
intros x M N a1 ih P Z a2.
inversion a2.
apply kahrs_eos1.
apply ih; assumption.
intros x y M N X Y a1 ih P Z a2.
inversion a2.
apply kahrs_eos2.
apply ih; assumption.
apply False_ind.
apply H3.
reflexivity.
intros x x' y y' M N X Y e1 e2 a1 ih P Z a2.
inversion a2.
apply False_ind.
apply e2.
assumption.
apply kahrs_eos3.
exact e1.
assumption.
apply ih; assumption.
intros M1 M2 N1 N2 X Y a1 ih1 a2 ih2 P Z a3.
inversion a3.
apply kahrs_ap.
apply ih1; assumption.
apply ih2; assumption.
Qed.

Lemma kahrs_snoc1 :
 forall (M N : Adbmal) (X Y : stack) (z : name), 
  (kahrs' M X N Y)->(kahrs' M (snoc z X) N (snoc z Y)).
Proof.
intros M N X Y z h.
elim h; clear h M N X Y; simpl.
intro x. (* Apply kahrs_refl. *)
destruct (eq_dec x z) as [e|e].
rewrite e; apply kahrs_var2.
reflexivity.
exact (kahrs_var3 e e (kahrs_var1 x)).
intros x y X Y h.
apply kahrs_var2.
rewrite length_snoc.
rewrite length_snoc.
rewrite h.
reflexivity.
intros x x' y y' X Y e1 e2 a ih.
exact (kahrs_var3 e1 e2 ih).
intros x y M N X Y a ih.
exact (kahrs_abs ih).
intros x M N a ih.
destruct (eq_dec x z) as [e|e].
rewrite e.
exact (kahrs_eos2 z z a).
exact (kahrs_eos3 e e (kahrs_eos1 x a)).
intros x y M N X Y a ih.
exact (kahrs_eos2 x y ih).
intros x x' y y' M N X Y e1 e2 a ih.
exact (kahrs_eos3 e1 e2 ih).
intros M1 M2 N1 N2 X Y a1 ih1 a2 ih2.
exact (kahrs_ap ih1 ih2).
Qed.

Lemma kahrs_var_snoc2 :
 forall (x y z : name) (X Y : stack), 
  (kahrs' (var x)(snoc z X)(var y)(snoc z Y))
   ->(kahrs' (var x) X (var y) Y).
Proof.
induction X; destruct Y; simpl.
intro h; inversion h.
apply kahrs_var1.
assumption.
intro h.
assert (h0 := (kahrs_list_length h)).
simpl in h0; injection h0; rewrite length_snoc; intro h1; discriminate h1.
intro h.
assert (h0 := (kahrs_list_length h)).
simpl in h0; injection h0; rewrite length_snoc; intro h1; discriminate h1.
intro h; inversion_clear h.
apply kahrs_var2.
simpl in H; rewrite length_snoc in H; rewrite length_snoc in H;
injection H; exact (fun h => h).
apply kahrs_var3.
exact H.
exact H0.
apply IHX.
assumption.
Qed.

Lemma kahrs_eos_snoc2 :
 forall (M N : Adbmal) (x y z : name), 
  (forall (X Y : stack), 
   (kahrs' M (snoc z X) N (snoc z Y))->(kahrs' M X N Y))
   ->forall (X Y : stack), 
      (kahrs' (eos x M)(snoc z X)(eos y N)(snoc z Y))
       ->(kahrs' (eos x M) X (eos y N) Y).
Proof.
intros M N x y z ihM.
simple induction X.
simple destruct Y; simpl.
(* nil nil *)
intro h; inversion h.
apply kahrs_eos1.
assumption.
assumption.
(* nil cons *)
intros y' Y' h.
assert (h0 := (kahrs_list_length h)).
simpl in h0; rewrite length_snoc in h0; discriminate h0.
intros x' X' ihX.
simple destruct Y; simpl.
(* cons nil *)
intro h.
assert (h0 := (kahrs_list_length h)).
simpl in h0; rewrite length_snoc in h0; discriminate h0.
(* cons cons *)
intros y' Y' h.
inversion h.
apply kahrs_eos2.
apply ihM; assumption.
apply kahrs_eos3.
assumption.
assumption.
apply ihX; assumption.
Qed.

Lemma kahrs_snoc2 :
 forall (M N : Adbmal) (X Y : stack) (z : name), 
  (kahrs' M (snoc z X) N (snoc z Y))->(kahrs' M X N Y).
(* Messy *) Proof.
simple induction M.
intros x N X Y z h.
inversion h.
exact (snoc_not_nil z X _ H).
rewrite <- H2 in h; exact (kahrs_var_snoc2 z X Y h).
rewrite <- H4 in h; exact (kahrs_var_snoc2 z X Y h).
intros x t ih N X Y z h.
inversion_clear h.
apply kahrs_abs.
apply ih with (z := z).
exact H.
intros x t ih N X Y z h.
inversion h.
exact (snoc_not_nil z X _ H2).
destruct X as [|n0 X].
simpl in H2; injection H2; intros h1 h2.
destruct Y.
simpl in H4; injection H4; intros h3 h4.
rewrite h2; rewrite h4; apply kahrs_eos1.
rewrite h1 in H3; rewrite h3 in H3; exact H3.
simpl in H4; injection H4; intros h3 h4.
rewrite h1 in H3; rewrite h3 in H3.
assert (h5 := (kahrs_list_length H3)).
rewrite length_snoc in h5; discriminate h5.
simpl in H2; injection H2; intros h1 h2.
destruct Y.
simpl in H4; injection H4; intros h3 h4.
rewrite h1 in H3; rewrite h3 in H3.
assert (h5 := (kahrs_list_length H3)).
rewrite length_snoc in h5.
discriminate h5.
simpl in H4; injection H4; intros h3 h4.
rewrite h2; rewrite h4.
apply kahrs_eos2.
rewrite h1 in H3; rewrite h3 in H3.
apply (ih N0 X Y z); exact H3.
destruct X as [|n0 X]; simpl.
injection H1; intros h1 h2.
destruct Y; simpl.
injection H2; intros h3 h4.
rewrite h1 in H6; rewrite h3 in H6; exact H6.
simpl in H2; injection H2; intros h3 h4.
rewrite h1 in H6; rewrite h3 in H6.
assert (h5 := (kahrs_list_length H6)).
rewrite length_snoc in h5.
discriminate h5.
simpl in H1; injection H1; intros h1 h2.
destruct Y; simpl.
injection H2; intros h3 h4.
rewrite h1 in H6; rewrite h3 in H6.
assert (h5 := (kahrs_list_length H6)).
rewrite length_snoc in h5.
discriminate h5.
simpl in H2; injection H2; intros h3 h4.
rewrite h1 in H6; rewrite h3 in H6.
apply kahrs_eos3.
intro h5; apply H3; rewrite h2; exact h5.
intro h5; apply H5; rewrite h4; exact h5.
exact (kahrs_eos_snoc2 z (fun X Y => ih N0 X Y z) X Y H6).
intros t1 ih1 t2 ih2 N X Y z h.
inversion h.
apply kahrs_ap.
apply (ih1 N1 X Y z); exact H1.
apply (ih2 N2 X Y z); exact H5.
Qed.

Lemma kahrs_cxt_congr : 
 forall (c : Adbmal->Adbmal), 
  (cxt c) 
   ->forall (t t' : Adbmal), (kahrs t t')
                 ->(kahrs (c t)(c t')). 
Proof. 
intros c h; elim h; clear h c. 
exact (fun t t' h => h). 
exact (fun c d hc ihc hd ihd t t' a => ihc (d t) (d t') (ihd t t' a)). 
exact (fun x t t' a => kahrs_abs (kahrs_snoc1 x a)). 
exact (fun x t t' a => kahrs_eos1 x a). 
exact (fun u t t' a => kahrs_ap a (kahrs_refl u Nil)). 
exact (fun u t t' a => kahrs_ap (kahrs_refl u Nil) a). 
Qed.

Lemma kahrs_eos3_gen :
 forall (x y : name) (M N : Adbmal) (X' Y' X Y : stack), 
  ~(In x X')
   ->~(In y Y')
    ->(length X')=(length Y')
    ->(kahrs' (eos x M) X (eos y N) Y)
     ->(kahrs' (eos x M) (juxt X' X) (eos y N) (juxt Y' Y)).
Proof.
induction X' as [|a X' IHX']; destruct Y' as [|b Y']; simpl; intros X Y h h0 h1 h2.
exact h2.
discriminate h1.
discriminate h1.
elim (dmx h); intros h3 h4.
elim (dmx h0); intros h5 h6.
apply kahrs_eos3.
intro h7; apply h3; symmetry; exact h7.
intro h7; apply h5; symmetry; exact h7.
injection h1; clear h1; intro h1.
exact (IHX' Y' X Y h4 h6 h1 h2).
Qed.

(** Definition of renaming; write [M[x:=y,Z]] for  [(rename M x y Z)].*)

Fixpoint rename (M : Adbmal) (x y : name) (Z : stack) : Adbmal :=
match M with
| var z   =>
    match in_dec z Z with
    | left _ => var z
    | right _ =>
        match eq_dec z x with
        | left _ => var y
        | right _ => var z
        end
    end
| abs z m => abs z (rename m x y (cons z Z))
| eos z m =>
    let fix aux (l : stack) : Adbmal :=
      match l with
      | nil =>
          match eq_dec x z with
          | left _ => eos y m
          | right _ => eos z m
          end
      | cons z' l' =>
          match eq_dec z z' with
          | left _ => eos z (rename m x y l')
          | right _ => aux l'
          end
      end
    in aux Z
| ap m n => ap (rename m x y Z) (rename n x y Z)
end.

Lemma rename_eoss :
 forall (M : Adbmal) (X Y : stack) (x z : name), 
  (rename (eoss X M) x z (juxt X Y))
   =(eoss X (rename M  x z Y)).
Proof.
induction X; intros Y x z; simpl.
reflexivity.
destruct (eq_dec a a) as [h|h]; simpl.
rewrite IHX; reflexivity.
elim h; reflexivity.
Qed.

Lemma scb_rename : 
 forall (M : Adbmal) (x z : name) (X1 X2 : stack), 
  (scb (juxt X1 (cons x X2)) M)
   ->(scb (juxt X1 (cons z X2))(rename M x z X1)).
Proof.
induction M; intros x z X1 X2 h.
simpl.
destruct (in_dec n X1) as [h0|h0].
apply scb_var.
destruct (eq_dec n x) as [h1|h1]; apply scb_var.
simpl.
assert (h0 := (scb_abs_inv h)).
apply scb_abs.
exact (IHM x z (cons n X1) X2 h0).
induction X1; simpl in h; simpl.
elim (scb_eos_inv h); intros h1 h2.
destruct (eq_dec x n) as [h3|h3]; simpl.
apply scb_eos; exact h2.
elim h3; symmetry; exact h1.
elim (scb_eos_inv h); intros h1 h2.
destruct (eq_dec n a) as [h0|h0]; simpl.
rewrite h0.
apply scb_eos; apply IHM; exact h2.
elim (h0 h1).
elim (scb_ap_inv h); intros h1 h2.
simpl.
apply scb_ap.
apply IHM1; exact h1.
apply IHM2; exact h2.
Qed.

Fixpoint names (M : Adbmal) : stack :=
match M with
| var x   => cons x Nil
| abs x t => cons x (names t)
| eos x t => cons x (names t)
| ap t u  => juxt (names t) (names u)
end.

Lemma in_eoss :
forall (N : Adbmal) (Y : stack) (z : name), 
  (In z (names (eoss Y N)))
   ->(In z Y)\/(In z (names N)).
Proof.
intros N Y z h.
induction Y; simpl.
right; exact h.
simpl in h; elim h; intro h0.
left; left; exact h0.
elim (IHY h0); intro h1.
left; right; exact h1.
right; exact h1.
Qed.

Lemma in_eoss1 : 
 forall (M : Adbmal) (X : stack) (z : name), (In z X)->(In z (names (eoss X M))).
Proof.
intros M X z h.
induction X; simpl.
elim h.
elim h; intro h0.
left; exact h0.
right; exact (IHX h0).
Qed.

Lemma in_eoss2 : 
 forall (M : Adbmal) (X : stack) (z : name), (In z (names M))->(In z (names (eoss X M))).
Proof.
intros M X z h.
induction X; simpl.
exact h.
right; exact IHX.
Qed.

Lemma subst_eq_rename_bal :
 forall (M : Adbmal) (Z W : stack) (x y : name), 
  (bal (juxt Z (cons x W)) M)
   ->~(In y Z)
   ->~(In y (names M))
   ->(adbmal_subst (cons y Nil) Z M x (var y)) = (rename M x y Z).
Proof.
induction M; intros Z W x y b d1 d2.
elim (bal_var_inv b); intros Z' e.
destruct Z as [|n0 l]; simpl in e; injection e; intros e1 e2.
simpl.
destruct (in_dec n Nil) as [h|h]; [ elim h | clear h ].
rewrite e2; destruct (eq_dec n n) as [h|h];
[ clear h | elim h; reflexivity ].
reflexivity.
simpl.
rewrite e2.
simpl.
destruct (eq_dec n n) as [h|h].
reflexivity.
elim h; reflexivity.
simpl.
rewrite (IHM (cons n Z) W x y (bal_abs_inv b)).
reflexivity.
intro h; elim h; intro h0.
apply d2; left; exact h0.
exact (d1 h0).
intro h; apply d2; right; exact h.
destruct Z as [|n0 l].
simpl.
simpl in b.
elim (bal_eos_inv b); intros h h0.
rewrite h; destruct (eq_dec x x) as [h1|h1];
[ clear h1 | elim h1; reflexivity ].
reflexivity.
simpl in b; elim (bal_eos_inv b); intros h h0.
simpl.
rewrite h; destruct (eq_dec n0 n0) as [h1|h1];
[ clear h1 | elim h1; reflexivity ].
rewrite (IHM l W x y h0).
reflexivity.
intro h1; apply d1; right; exact h1.
intro h1; apply d2; right; exact h1.
elim (bal_ap_inv b); intros b1 b2.
assert (h1 : ~(In y (names M1))).
intro h; apply d2; simpl; apply in_or_juxt; left; exact h.
assert (h2 : ~(In y (names M2))).
intro h; apply d2; simpl; apply in_or_juxt; right; exact h.
simpl.
rewrite (IHM1 Z W x y b1 d1 h1); rewrite (IHM2 Z W x y b2 d1 h2);
reflexivity.
Qed.

Lemma not_in_subst : 
 forall (M N : Adbmal) (X Y : stack) (x z : name), 
  ~(In z (names M))
   ->~(In z (names N))
    ->~(In z X)
     ->~(In z Y)
       ->~(In z (names (adbmal_subst X Y M x N))).
Proof.
induction M; intros N X Y x z h h0 h1 h2.
simpl.
destruct (in_dec n Y) as [h3|h3].
exact h.
destruct (eq_dec x n) as [h4|h4].
intro h5; apply h0.
elim (in_eoss N Y z h5); intro h6.
elim (h2 h6).
exact h6.
intro h5; elim (in_eoss (eoss X (var n)) Y z h5); intro h6.
exact (h2 h6).
elim (in_eoss (var n) X z h6); intro h7.
exact (h1 h7).
exact (h h7).
intro h3; elim h3; intro h4.
apply h; left; exact h4.
apply (IHM N X (cons n Y) x z); [ | exact h0 | exact h1 | | exact h4 ].
intro h5; apply h; right; exact h5.
intro h5; elim h5; intro h6.
apply h; left; exact h6.
exact (h2 h6).
destruct (in_dec n Y) as [h3|h3].
elim (in_split eq_dec n Y h3); intros Y1 h4; elim h4; intros Y2 h5;
elim h5; clear h4 h5; intros h4 h5.
rewrite h4.
rewrite (adbmal_subst_eos_clause1 M N x n X Y1 Y2 h5).
intro h6; elim h6; intro h7.
apply h; left; exact h7.
apply (IHM N X Y2 x z); [ | | | | exact h7 ].
intro h8; apply h; right; exact h8.
exact h0.
exact h1.
intro h8; apply h2; rewrite h4; apply in_or_juxt; right; right;
exact h8.
destruct (eq_dec x n) as [h4|h4].
rewrite (adbmal_subst_eos_clause2 M N X Y h4 h3).
intro h5; elim (in_eoss (eoss X M) Y z h5); intro h6.
exact (h2 h6).
elim (in_eoss M X z h6); intro h7.
exact (h1 h7).
apply h; right; exact h7.
rewrite (adbmal_subst_eos_clause3 M N X Y h4 h3).
intro h5; elim (in_eoss (eoss X (eos n M)) Y z h5); intro h6.
exact (h2 h6).
elim (in_eoss (eos n M) X z h6); intro h7.
exact (h1 h7).
exact (h h7).
simpl; intro h3; elim (in_juxt_or h3); [ apply IHM1 | apply IHM2 ]; auto;
 intro h4; apply h; simpl; apply in_or_juxt; [ left | right ]; exact h4.
Qed.

Lemma not_in_beta : 
 forall (M N : Adbmal) (z : name), ~(In z (names M))->(adbmal_beta M N)->~(In z (names N)).
Proof.
induction M; intros N z h h0.
inversion h0.
inversion_clear h0.
intro h0; elim h0; intro h1.
apply h; left; exact h1.
apply (IHM N0 z); [ | exact H | exact h1 ].
intro h2; apply h; right; exact h2.
inversion_clear h0.
intro h0; elim h0; intro h1.
apply h; left; exact h1.
apply (IHM N0 z); [ | exact H | exact h1 ].
intro h2; apply h; right; exact h2.
inversion h0.
simpl; intro h1; elim (in_juxt_or h1); intro h2.
apply (IHM1 M' z); [ | exact H2 | exact h2 ].
intro h3; apply h; simpl; apply in_or_juxt; left; exact h3.
apply h; simpl; apply in_or_juxt; right; exact h2.
simpl; intro h1; elim (in_juxt_or h1); intro h2.
apply h; simpl; apply in_or_juxt; left; exact h2.
apply (IHM2 M' z); [ | exact H2 | exact h2 ].
intro h3; apply h; simpl; apply in_or_juxt; right; exact h3.
rewrite <- H0 in h.
assert (h1 : ~(In z X)).
intro h1; apply h; simpl; apply in_or_juxt; left; 
 apply in_eoss1; exact h1.
assert (h2 : ~(In z (names M))).
intro h2; apply h; simpl; apply in_or_juxt; left; 
 apply in_eoss2; right; exact h2.
assert (h3 : ~(In z (names M2))).
intro h3; apply h; simpl; apply in_or_juxt; right; exact h3.
assert (h4 : ~(In z Nil)).
exact (fun h => h).
exact (not_in_subst M M2 X Nil x z h2 h3 h1 h4).
Qed.

Lemma rename_subst_commute_closed :
 forall (M N : Adbmal) (X0 X1 X2 Z : stack) (x y z : name), 
  (scb (juxt X0 (cons y Z)) M)
   ->(scb (juxt X1 (cons x (juxt X2 Z))) N)
    ->(rename (adbmal_subst (juxt X1 (cons x X2)) X0 M y N) x z (juxt X0 X1))
       =(adbmal_subst (juxt X1 (cons z X2)) X0 M y (rename N x z X1)).
Proof.
induction M; simpl; intros N X0 X1 X2 Z x y z sm sn.
destruct (in_dec n X0) as [h|h]; simpl.
destruct (in_dec n (juxt X0 X1)) as [h0|h0]; simpl.
reflexivity.
elim h0; apply in_or_juxt; left; exact h.
destruct (eq_dec y n) as [h0|h0]; simpl.
rewrite rename_eoss; reflexivity.
rewrite rename_eoss.
rewrite eoss_juxt.
simpl.
pattern X1 at 2; rewrite (juxt_nil_end X1).
rewrite rename_eoss.
simpl.
destruct (eq_dec x x) as [h1|h1]; simpl.
rewrite eoss_juxt.
reflexivity.
elim h1; reflexivity.
replace (cons n (juxt X0 X1)) with (juxt (cons n X0) X1);
[ rewrite (IHM N (cons n X0) X1 X2 Z x y z (scb_abs_inv sm) sn) 
 | reflexivity ].
reflexivity.
induction X0.
simpl in sm.
elim (scb_eos_inv sm); intros h h0.
destruct (eq_dec y n) as [h1|h1]; simpl.
rewrite eoss_juxt.
rewrite eoss_juxt.
pattern X1 at 2; rewrite (juxt_nil_end X1).
rewrite rename_eoss.
simpl.
destruct (eq_dec x x) as [h2|h2]; simpl.
reflexivity.
elim h2; reflexivity.
elim h1; symmetry; exact h.
elim (scb_eos_inv sm); intros h3 h4.
destruct (eq_dec n a) as [h|h]; simpl.
destruct (eq_dec n a) as [h0|h0]; simpl.
clear IHX0.
rewrite (IHM N X0 X1 X2 Z x y z).
reflexivity.
exact h4.
exact sn.
elim (h0 h).
elim (h h3).
elim (scb_ap_inv sm); intros sm1 sm2.
rewrite (IHM1 N X0 X1 X2 Z x y z sm1 sn);
rewrite (IHM2 N X0 X1 X2 Z x y z sm2 sn); reflexivity.
Qed.

Lemma rename_subst_commute_open :
 forall (M N : Adbmal) (X0 X1 X2 X3 : stack) (x y z : name), 
  ~(In z (names M))
    ->~(In z X0)
      ->~z=y
       ->(scb (juxt X0 (cons y (juxt X2 (cons x X3)))) M)
        ->(scb (juxt X1 (juxt X2 (cons x X3))) N)
         ->(rename (adbmal_subst X1 X0 M y N) x z (juxt X0 (juxt X1 X2)))
           =(adbmal_subst X1 X0 (rename M x z (juxt X0 (cons y X2))) 
                  y (rename N x z (juxt X1 X2))).
Proof.
induction M; intros N X0 X1 X2 X3 x y z h h1 h3 h4 h5; simpl.
(* var n *)
destruct (in_dec n (juxt X0 (cons y X2))) as [h6|h6]; simpl.
destruct (in_dec n X0) as [h7|h7]; simpl.
destruct (in_dec n (juxt X0 (juxt X1 X2))) as [h8|h8]; simpl.
reflexivity.
elim h8; apply in_or_juxt; left; exact h7.
destruct (eq_dec y n) as [h8|h8]; simpl.
rewrite rename_eoss.
reflexivity.
rewrite rename_eoss.
rewrite rename_eoss.
simpl.
destruct (in_dec n X2) as [h9|h9]; simpl.
reflexivity.
elim (in_juxt_or h6); intro h10.
elim (h7 h10).
elim h10; intro h11.
elim (h8 h11).
elim (h9 h11).
destruct (eq_dec n x) as [h7|h7]; simpl.
destruct (in_dec z X0) as [h8|h8].
elim (h1 h8).
destruct (eq_dec y z) as [h9|h9].
elim h3; symmetry; exact h9.
destruct (in_dec n X0) as [h10|h10]; simpl.
elim h6; apply in_or_juxt; left; exact h10.
destruct (eq_dec y n) as [h11|h11].
elim h6; rewrite h11; apply in_or_juxt; right; left; reflexivity.
rewrite rename_eoss.
rewrite rename_eoss.
simpl.
destruct (in_dec n X2) as [h12|h12].
elim h6; apply in_or_juxt; right; right; exact h12.
destruct (eq_dec n x) as [h13|h13].
reflexivity.
elim (h13 h7).
destruct (in_dec n X0) as [h8|h8]; simpl.
elim h6; apply in_or_juxt; left; exact h8.
destruct (eq_dec y n) as [h9|h9].
rewrite rename_eoss.
reflexivity.
rewrite rename_eoss.
rewrite rename_eoss.
simpl.
destruct (in_dec n X2) as [h10|h10].
elim h6; apply in_or_juxt; right; right; exact h10.
destruct (eq_dec n x) as [h11|h11].
elim (h7 h11).
reflexivity.
(* abs n M *)
assert (h6 : ~(In z (cons n X0))).
intro h6; elim h6; intro h7.
apply h; left; exact h7.
exact (h1 h7).
assert (h7 := (scb_abs_inv h4)).
assert (h8 : ~(In z (names M))).
intro h8; apply h; right; exact h8.
replace (cons n (juxt X0 (cons y X2)))
 with (juxt (cons n X0) (cons y X2)).
replace (cons n (juxt X0 (juxt X1 X2)))
 with (juxt (cons n X0) (juxt X1 X2)).
rewrite (IHM N (cons n X0) X1 X2 X3 x y z h8 h6 h3 h7 h5).
reflexivity.
reflexivity.
reflexivity.
(* eos n M *)
destruct X0 as [|n0 X0]; simpl; simpl in h4.
elim (scb_eos_inv h4); intros h6 h7.
destruct (eq_dec n y) as [h8|h8].
destruct (eq_dec y n) as [h9|h9]; simpl.
destruct (eq_dec y n) as [h10|h10].
rewrite rename_eoss.
reflexivity.
elim (h10 h9).
elim h9; symmetry; exact h8.
elim (h8 h6).
elim (scb_eos_inv h4); intros h6 h7.
destruct (eq_dec n n0) as [h8|h8]; simpl.
destruct (eq_dec n n0) as [h9|h9]; simpl.
rewrite (IHM N X0 X1 X2 X3 x y z).
reflexivity.
intro h10; apply h; right; exact h10.
intro h10; apply h1; right; exact h10.
exact h3.
exact h7.
exact h5.
elim (h9 h8).
elim (h8 h6).
(* ap M1 M2  *)
elim (scb_ap_inv h4); intros h6 h7.
simpl in h.
rewrite (IHM1 N X0 X1 X2 X3 x y z).
rewrite (IHM2 N X0 X1 X2 X3 x y z).
reflexivity.
intro h8; apply h; apply in_or_juxt; right; exact h8.
exact h1.
exact h3.
exact h7.
exact h5.
intro h8; apply h; apply in_or_juxt; left; exact h8.
exact h1.
exact h3.
exact h6.
exact h5.
Qed.

Lemma subst_rename_commute_open :
 forall (M N : Adbmal) (X Y X0 W : stack) (x y z : name), 
  ~(In z (names M))
   ->(scb (juxt X0 (cons y (juxt Y (cons x W)))) M)
    ->(rename (adbmal_subst X (juxt X0 (cons y Y)) M x N) y z X0)
       =(adbmal_subst X (juxt X0 (cons z Y))(rename M y z X0) x N).
Proof.
induction M; intros N X Y X0 W x y z d b.
simpl.
destruct (in_dec n X0); simpl.
destruct (in_dec n (juxt X0 (cons y Y))); simpl.
destruct (in_dec n X0); simpl.
destruct (in_dec n (juxt X0 (cons z Y))); simpl.
reflexivity.
elim n0; apply in_or_juxt; left; exact i.
elim n0; exact i.
elim n0; apply in_or_juxt; left; exact i.
destruct (in_dec n (juxt X0 (cons y Y))); simpl.
destruct (in_dec n X0); simpl.
elim (n0 i0).
destruct (eq_dec n y); simpl.
destruct (in_dec z (juxt X0 (cons z Y))); simpl.
reflexivity.
elim n2; apply in_or_juxt; right; left; reflexivity.
destruct (in_dec n (juxt X0 (cons z Y))); simpl.
reflexivity.
elim n3; apply in_or_juxt; right; right.
elim (in_juxt_or i); intro h.
elim (n0 h).
elim h; intro h0.
elim n2; symmetry; exact h0.
exact h0.
destruct (eq_dec x n); simpl.
destruct (eq_dec n y); simpl.
elim n1; apply in_or_juxt; right; left; symmetry; exact e0.
destruct (in_dec n (juxt X0 (cons z Y))); simpl.
elim (in_juxt_or i); intro h.
elim (n0 h).
elim h; intro h0.
elim d; left; symmetry; exact h0.
elim n1; apply in_or_juxt; right; right; exact h0.
destruct (eq_dec x n); simpl.
pattern X0 at 2; rewrite (juxt_nil_end X0).
rewrite eoss_juxt; rewrite rename_eoss.
simpl.
destruct (eq_dec y y).
rewrite eoss_juxt; reflexivity.
elim n4; reflexivity.
elim (n4 e).
simpl.
pattern X0 at 2; rewrite (juxt_nil_end X0).
rewrite eoss_juxt; rewrite rename_eoss.
simpl.
destruct (eq_dec y y).
destruct (eq_dec n y).
elim n1; apply in_or_juxt; right; left; symmetry; exact e0.
simpl.
destruct (in_dec n (juxt X0 (cons z Y))); simpl.
elim (in_juxt_or i); intro h.
elim (n0 h).
elim h; intro h0.
elim d; left; symmetry; exact h0.
elim n1; apply in_or_juxt; right; right; exact h0.
destruct (eq_dec x n); simpl.
elim (n2 e0).
rewrite eoss_juxt; reflexivity.
elim n3; reflexivity.
(* abs *)
simpl.
assert (h : ~(In z (names M))).
intro h; apply d; right; exact h.
apply f_equal.
exact (IHM N X Y (cons n X0) W x y z h (scb_abs_inv b)).
(* eos *)
elim (scb_eos_inv2 b); intros U h; elim h; clear h; intros h0 h1.
destruct X0 as [|n0 X0]; simpl; simpl in h0; injection h0; intros h2 h3.
destruct (eq_dec n y); simpl.
destruct (eq_dec y n); simpl.
destruct (eq_dec z z).
reflexivity.
elim n0; reflexivity.
elim (n0 h3).
elim n0; symmetry; exact h3.
destruct (eq_dec n n0); simpl.
destruct (eq_dec n n0); simpl.
rewrite <- h2 in h1.
rewrite (IHM N X Y X0 W x y z).
reflexivity.
intro h4; apply d; right; exact h4.
exact h1.
elim (n1 e).
elim n1; symmetry; exact h3.
(* ap *)
elim (scb_ap_inv b); intros b1 b2.
simpl.
rewrite (IHM1 N X Y X0 W x y z).
rewrite (IHM2 N X Y X0 W x y z).
reflexivity.
intro h; apply d; simpl; apply in_or_juxt; right; exact h.
exact b2.
intro h; apply d; simpl; apply in_or_juxt; left; exact h.
exact b1.
Qed.

(* alpha conversion *)

Inductive alpha_conv : Adbmal->Adbmal->Prop :=
| alpha_conv_rule : forall (M : Adbmal) (x y : name), 
    ~(In y (names M))->(alpha_conv (abs x M)(abs y (rename M x y Nil)))
| alpha_conv_abs : forall (M N : Adbmal) (x : name), 
    (alpha_conv M N)->(alpha_conv (abs x M)(abs x N))
| alpha_conv_eos : forall (M N : Adbmal) (x : name), 
    (alpha_conv M N)->(alpha_conv (eos x M)(eos x N))
| alpha_conv_apl : forall (M M' N : Adbmal), 
    (alpha_conv M M')->(alpha_conv (ap M N)(ap M' N))
| alpha_conv_apr : forall (M M' N : Adbmal), 
    (alpha_conv M M')->(alpha_conv (ap N M)(ap N M')).

(* equivalence closure of alpha_conv *)

Definition church := (Rhat alpha_conv).

Lemma alpha_conv_cxt_congr :
 forall (c : Adbmal->Adbmal), (cxt c)
   ->forall (t t' : Adbmal), (alpha_conv t t')->(alpha_conv (c t)(c t')).
Proof.
induction 1.
intros; assumption.
intros; apply IHcxt1; apply IHcxt2; assumption.
intros; apply alpha_conv_abs; assumption.
intros; apply alpha_conv_eos; assumption.
intros; apply alpha_conv_apl; assumption.
intros; apply alpha_conv_apr; assumption.
Qed.

Lemma church_cxt_congr :
 forall (c : Adbmal->Adbmal), (cxt c)
   ->forall (t t' : Adbmal), (church t t')->(church (c t)(c t')).
Proof.
induction 2; red.
apply Rhat_ext; apply alpha_conv_cxt_congr; assumption.
apply Rhat_refl.
apply Rhat_symm; assumption.
exact (Rhat_trans IHRhat1 IHRhat2).
Qed.

Lemma alpha_conv_rule_to_kahrs' :
 forall (M : Adbmal) (x y : name) (Z : stack), 
  ~(In y (names M))
   ->~(In y Z)
     ->(kahrs' M (snoc x Z) (rename M x y Z) (snoc y Z)).
Proof.
simple induction M; simpl.
intros z x y Z h.
assert (h0 : ~z=y).
intro h0; apply h; left; exact h0.
destruct (eq_dec z x) as [h1|h1]; simpl.
induction Z; simpl.
destruct (in_dec z Nil) as [h2|h2]; simpl.
elim h2.
intro h3; clear h2 h3.
rewrite h1; apply kahrs_var2; reflexivity.
intro h2.
generalize IHZ; clear IHZ.
destruct (in_dec z Z) as [h3|h3]; simpl.
intro ih.
destruct (in_dec z (cons a Z)) as [h4|h4]; simpl.
destruct (eq_dec z a) as [h5|h5].
subst a.
destruct (eq_dec z z) as [h5'|h5']; simpl.
apply kahrs_var2.
rewrite length_snoc; rewrite length_snoc; reflexivity.
elim h5'; reflexivity.
destruct (eq_dec a z) as [h5'|h5']; simpl.
elim h5; symmetry; exact h5'.
apply kahrs_var3.
exact h5.
exact h5.
apply ih.
intro h6; apply h2; right; exact h6.
elim h4; right; exact h3.
destruct (in_dec z (cons a Z)) as [h4|h4]; simpl.
elim h4; intro h5.
subst a.
intro ih.
destruct (eq_dec z z) as [h5'|h5']; simpl.
apply kahrs_var2.
rewrite length_snoc; rewrite length_snoc; reflexivity.
elim h5'; reflexivity.
elim h3; exact h5.
assert (h6 : ~z=a).
intro h5; apply h4; left; symmetry; exact h5.
intro ih.
destruct (eq_dec a z) as [h5'|h5']; simpl.
elim h6; symmetry; exact h5'.
apply kahrs_var3.
exact h6.
intro h5; apply h2; left; symmetry; exact h5.
apply ih.
intro h5; apply h2; right; exact h5.
induction Z; simpl.
destruct (in_dec z Nil) as [h2|h2].
elim h2.
intro h3; clear h2 h3.
apply kahrs_var3.
exact h1.
exact h0.
apply kahrs_var1.
intro h2.
assert (h3 : ~(In y Z)).
intro h3; apply h2; right; exact h3.
generalize (IHZ h3); clear IHZ.
destruct (in_dec z Z) as [h4|h4].
destruct (in_dec z (cons a Z)) as [h5|h5].
intro ih.
destruct (eq_dec z a) as [h6|h6].
subst a.
destruct (eq_dec z z) as [h6'|h6']; simpl.
apply kahrs_var2.
rewrite length_snoc; rewrite length_snoc; reflexivity.
elim h6'; reflexivity.
destruct (eq_dec a z) as [h6'|h6']; simpl.
elim h6; symmetry; exact h6'.
apply kahrs_var3.
exact h6.
exact h6.
exact ih.
elim h5; right; exact h4.
destruct (in_dec z (cons a Z)) as [h5|h5].
intro ih.
destruct (eq_dec z a) as [h6|h6].
subst a.
destruct (eq_dec z z) as [h6'|h6']; simpl.
apply kahrs_var2.
rewrite length_snoc; rewrite length_snoc; reflexivity.
elim h6'; reflexivity.
elim h5; intro h7.
elim h6; symmetry; exact h7.
elim h4; exact h7.
assert (h6 : ~z=a).
intro h6; apply h5; left; symmetry; exact h6.
intro ih.
destruct (eq_dec a z) as [h6'|h6']; simpl.
elim h6; symmetry; exact h6'.
apply kahrs_var3.
exact h6.
exact h6.
exact ih.
intros z t ih x y Z h h0.
apply kahrs_abs.
assert (h1 : ~z=y).
intro h2; apply h; left; exact h2.
assert (h2 : ~(In y (names t))).
intro h2; apply h; right; exact h2.
assert (h3 : ~(In y (cons z Z))).
intro h3; elim h3; intro h4.
exact (h1 h4).
exact (h0 h4).
exact (ih x y (cons z Z) h2 h3).
simpl; intros z t ih x y Z h.
assert (h1 : ~(In y (names t))).
intro h2; apply h; right; exact h2.
assert (h2 : ~z=y).
intro h2; apply h; left; exact h2.
elim Z; simpl.
intro h3; clear h3.
destruct (eq_dec x z) as [h3|h3].
rewrite h3.
apply kahrs_eos2.
apply kahrs_refl.
apply kahrs_eos3.
intro h4; apply h3; symmetry; exact h4.
exact h2.
apply kahrs_refl.
intros z' Z'.
pose (eos_y_z :=
  (let fix aux (l : stack) : Adbmal :=
     match l with
     | nil =>
         match eq_dec x z with
         | left _ => eos y t
         | right _ => eos z t
         end
     | cons z'0 l' =>
         match eq_dec z z'0 with
         | left _ => eos z (rename t x y l')
         | right _ => aux l'
         end
     end
   in aux Z')).
intros ihZ' h3.
assert (h4 := fun e => h3 (or_introl e)).
assert (h5 := fun i => h3 (or_intror i)).
destruct (eq_dec z z') as [h6|h6].
rewrite h6.
apply kahrs_eos2.
exact (ih x y Z' h1 h5).
(* M = (eos z t); Z = Z'z'; ~z=z' *)
cut (exists t' : Adbmal,  eos_y_z=(eos y t')\/eos_y_z=(eos z t')).
intro c; elim c; intros t' h7; elim h7; intro h8; fold eos_y_z in ihZ' |- *; rewrite h8; 
 rewrite h8 in ihZ'.
apply kahrs_eos3.
exact h6.
intro h9; apply h4; symmetry; exact h9.
exact (ihZ' h5).
exact (kahrs_eos3 h6 h6 (ihZ' h5)).
lazy delta.
clear h6 h5 h4 h3 ihZ'.
induction Z' as [|a Z' HrecZ'].
destruct (eq_dec x z) as [h3|h3].
exists t; left; reflexivity.
exists t; right; reflexivity.
simpl.
destruct (eq_dec z a) as [e|ne].
exists (rename t x y Z'); right; reflexivity.
elim HrecZ'; intros t' H.
exists t'.
elim H; intro H0.
left; exact H0.
right; exact H0.
simpl; intros t1 ih1 t2 ih2 x y Z h h0.
assert (h1 : ~(In y (names t1))/\~(In y (names t2))).
split; intro h1; apply h.
apply in_or_juxt; left; exact h1.
apply in_or_juxt; right; exact h1.
elim h1; clear h1; intros h1 h2.
apply kahrs_ap.
exact (ih1 x y Z h1 h0).
exact (ih2 x y Z h2 h0).
Qed.

Lemma alpha_conv_rule_to_kahrs :
   forall (M : Adbmal) (x y : name), 
    ~(In y (names M))
    ->(kahrs (abs x M) (abs y (rename M x y Nil))).
Proof.
intros M x y h.
red; apply kahrs_abs.
assert (h0 : ~(In y Nil)). 
exact (fun h' => h').
exact (alpha_conv_rule_to_kahrs' M x y Nil h h0).
Qed.  

Lemma alpha_conv_to_kahrs : forall (t u : Adbmal), (alpha_conv t u)->(kahrs t u).
Proof.
intros t u h; red; elim h; clear h t u.
exact alpha_conv_rule_to_kahrs.
intros M N x h ih.
apply kahrs_abs.
exact (kahrs_snoc1 x ih).
intros M N x h ih.
apply kahrs_eos1.
exact ih.
intros M M' N h ih.
apply kahrs_ap.
exact ih.
apply kahrs_refl.
intros M M' N h ih.
apply kahrs_ap.
apply kahrs_refl.
exact ih.
Qed.

Lemma church_to_kahrs : 
 forall (t u : Adbmal), (church t u)->(kahrs t u).
Proof.
intros t u h; elim h.
exact alpha_conv_to_kahrs.
exact (fun x => kahrs_refl x Nil).
exact (fun x y _ h => kahrs_symm h).
exact (fun x y z _ h1 _ h2 => kahrs_trans h1 h2).
Qed.

Lemma rename_skel_eq : 
 forall (x y : name) (M : Adbmal) (Z : stack), (skeleton M)=(skeleton (rename M x y Z)).
Proof.
induction M; intro Z; simpl.
destruct (eq_dec n x); destruct (in_dec n Z); reflexivity.
rewrite (IHM (cons n Z)); reflexivity.
destruct (eq_dec x n) as [h|h]; simpl; induction Z.
reflexivity.
destruct (eq_dec n a) as [h0|h0]; simpl.
rewrite (IHM Z); reflexivity.
exact IHZ.
reflexivity.
destruct (eq_dec n a) as [h0|h0]; simpl.
rewrite (IHM Z); reflexivity.
exact IHZ.
rewrite (IHM1 Z); rewrite (IHM2 Z); reflexivity.
Qed.

Lemma kahrs_to_church_skel_ind :
 forall (s : skel) (t u : Adbmal), 
  (skeleton t)=s
   ->(kahrs t u)
    ->(church t u).
Proof. (* by induction on skeleton of t; use rename_skel_eq *)
red. simple induction s.
(* var_skel *)
simple destruct t.
intros x u p h; inversion h; apply Rhat_refl.
intros n t' u p; discriminate p.
intros n t' u p; discriminate p.
intros t1 t2 u p; discriminate p.
(* abs_skel *)
intros s' ih; simple destruct t.
intros x u p; discriminate p.
intros x t' u p h.
inversion h.
rewrite <- H2 in h.
rewrite <- H1.
rewrite <- H1 in p.
rewrite <- H1 in h.
rewrite <- H1 in H4.
simpl in p; injection p; intro p'.
pose (z := fresh (names (ap M N))).
assert (h0 := (fresh_not_in (names (ap M N)))).
assert (h1 : ~(In z (names M))/\~(In z (names N))).
split; intro h1; apply h0; simpl; apply in_or_juxt.
left; exact h1.
right; exact h1.
elim h1; clear h1; intros h1 h2.
assert (h3 : (church (abs z (rename M x z Nil)) (abs x M))).
   red; apply Rhat_symm; apply Rhat_ext; apply alpha_conv_rule; exact h1.
assert (h4 : (church (abs y N) (abs z (rename N y z Nil)))).
   red; apply Rhat_ext; apply alpha_conv_rule; exact h2.
assert (h5 := (kahrs_trans (church_to_kahrs h3) 
  (kahrs_trans h (church_to_kahrs h4)))).
apply Rhat_trans with (y := abs z (rename M x z Nil)).
apply Rhat_symm; exact h3.
apply Rhat_trans with (y := abs z (rename N y z Nil)).
assert (h6 : (church (rename M x z Nil)(rename N y z Nil))).
apply ih.
rewrite <- rename_skel_eq.
exact p'.
inversion_clear h5.
assert (h5 : (cons z Nil)=(snoc z Nil));
[ reflexivity | rewrite h5 in H5 ].
exact (kahrs_snoc2 Nil Nil z H5).
exact (church_cxt_congr (cxt_abs z) h6).
apply Rhat_symm; exact h4.
intros x t' u p; discriminate p.
intros t1 t2 u p; discriminate p.
(* eos_skel *)
intros s' ih.
simple destruct t.
intros x u p; discriminate p.
intros x t' u p; discriminate p.
intros x t' u p h; injection p; fold skeleton; intro p'.
inversion_clear h.
apply (church_cxt_congr (cxt_eos x)).
exact (ih t' N p' H).
intros t1 t2 u p; discriminate p.
(* ap_skel *)
intros s1 ih1 s2 ih2; simple destruct t.
intros x u p; discriminate p.
intros x t' u p; discriminate p.
intros x t' u p; discriminate p.
intros t1 t2 u p; injection p; fold skeleton; intros p2 p1 h.
inversion_clear h.
exact (Rhat_trans
        (church_cxt_congr (cxt_apl t2) (ih1 t1 N1 p1 H))
        (church_cxt_congr (cxt_apr N1) (ih2 t2 N2 p2 H0))).
Qed.

Lemma kahrs_to_church : forall (t u : Adbmal), (kahrs t u)->(church t u).
Proof.
intros t u h.
exact (kahrs_to_church_skel_ind (eq_refl (skeleton t)) h).
Qed.

Lemma same_kahrs_church : (same_rel kahrs church).
Proof.
split; unfold incl_rel; intros x y H.
exact (kahrs_to_church H).
exact (church_to_kahrs H).
Qed.

Fixpoint FV (t : Adbmal) (X : stack) : stack :=
match t with
| var x =>
    match in_dec x X with
    | left _ => Nil
    | right _ => cons x Nil
    end
| abs x t' => FV t' (cons x X)
| eos x t' =>
    let fix FV_aux (l : stack) : stack :=
      match l with
      | nil => FV t' Nil
      | cons x' l' =>
          match eq_dec x x' with
          | left _ => FV t' l'
          | right _ => FV_aux l'
          end
      end
    in FV_aux X
| ap t1 t2 => juxt (FV t1 X) (FV t2 X)
end.

Lemma FV_eos_jump :
 forall (M : Adbmal) (x : name) (Y X : stack), 
  ~(In x X)
   ->(FV (eos x M) (juxt X Y)) = (FV (eos x M) Y).
Proof.
induction X; simpl; intro h.
reflexivity.
elim (dmx h); intros h0 h1.
destruct (eq_dec x a) as [h2|h2].
elim h0; symmetry; exact h2.
exact (IHX h1).
Qed.

Lemma bal_fv_nil : forall (M : Adbmal) (X : stack), (bal X M)->(FV M X)=Nil.
Proof.
induction M; intros X b; simpl.
elim (bal_var_inv b); intros X' e; rewrite e.
destruct (in_dec n (cons n X')) as [h|h].
reflexivity.
elim h; left; reflexivity.
exact (IHM (cons n X) (bal_abs_inv b)).
elim (bal_eos_inv2 b); intros X' h; elim h; clear h; intros e b'.
rewrite e.
destruct (eq_dec n n) as [h|h].
exact (IHM X' b').
elim h; reflexivity.
elim (bal_ap_inv b); intros b1 b2.
rewrite (IHM1 X b1); exact (IHM2 X b2).
Qed.

Lemma FV_sub1 :
 forall (M : Adbmal) (X Y Z : stack), (sub (FV M (juxt X (juxt Y Z))) (FV M (juxt X Z))).
Proof.
induction M; intros X Y Z; simpl.
(* var n *)
destruct (in_dec n (juxt X Z)) as [h|h]; destruct (in_dec n (juxt X (juxt Y Z))) as [h0|h0].
apply sub_nil.
elim h0; apply in_or_juxt; elim (in_juxt_or h); intro h1.
left; exact h1.
right; apply in_or_juxt; right; exact h1.
apply sub_nil.
apply sub_refl.
(* abs n M *)
exact (IHM (cons n X) Y Z).
(* eos n M *)
induction X.
induction Y.
apply sub_refl.
simpl; destruct (eq_dec n a) as [h|h].
clear IHY; induction Z.
exact (IHM Nil Y Nil).
destruct (eq_dec n a0) as [h0|h0].
rewrite juxt_snoc.
exact (IHM Nil (snoc a0 Y) Z).
apply sub_trans with (l2 := FV M (juxt Y Z)).
exact (IHM Y (cons a0 Nil) Z).
exact IHZ.
exact IHY.
simpl; destruct (eq_dec n a) as [h|h].
apply IHM.
exact IHX.
(* ap M1 M2 *)
simpl; apply sub_juxt; [ apply IHM1 | apply IHM2 ].
Qed.

Fixpoint eos_skel_free (s : skel) : Prop :=
match s with
| var_skel       => True
| abs_skel s'    => eos_skel_free s'
| eos_skel _     => False
| ap_skel s1 s2  => eos_skel_free s1 /\ eos_skel_free s2
end.

Definition eos_free := fun t : Adbmal => eos_skel_free (skeleton t).

Lemma eos_free_scb :
 forall (M : Adbmal) (X : stack), 
 (eos_free M)
  ->(scb X M).
induction M; intros X h.
apply scb_var.
apply scb_abs; apply IHM; exact h.
elim h.
elim h; intros h1 h2.
apply scb_ap; [ exact (IHM1 X h1) | exact (IHM2 X h2) ].
Qed.

Lemma rename_eos_free_in_stack :
 forall (x y : name) (M : Adbmal) (X : stack), 
  (eos_free M)
   ->(In x X)
    ->(rename M x y X)=M.
Proof.
induction M; intros X h h0; simpl.
destruct (in_dec n X) as [h1|h1].
reflexivity.
destruct (eq_dec n x) as [h2|h2].
elim h1; rewrite h2; exact h0.
reflexivity.
rewrite IHM.
reflexivity.
exact h.
right; exact h0.
elim h.
elim h; intros h1 h2.
rewrite (IHM1 X h1 h0); rewrite (IHM2 X h2 h0); reflexivity.
Qed.

Lemma FV_sub2 :
 forall (M : Adbmal), (eos_free M)->
  forall (X Y Z : stack), 
   (disjoint Y (FV M X))
    ->(sub (FV M (juxt X Z))(FV M (juxt X (juxt Y Z)))).
Proof.
induction M; intros h X Y Z.
clear h.
simpl.
destruct (in_dec n X) as [h|h].
intro h0; clear h0.
destruct (in_dec n (juxt X Z)) as [h0|h0].
apply sub_nil.
elim h0; apply in_or_juxt; left; exact h.
destruct (in_dec n (juxt X Z)) as [h0|h0].
intro h1; apply sub_nil.
intro h1.
destruct (in_dec n (juxt X (juxt Y Z))) as [h2|h2].
assert (h3 : ~(In n Y)).
intro h3; apply (h1 n h3); left; reflexivity.
elim (in_juxt_or h2); intro h4.
elim (h h4).
elim (in_juxt_or h4); intro h5.
elim (h3 h5).
elim h0; apply in_or_juxt; right; exact h5.
apply sub_refl.
intro h0.
exact (IHM h (cons n X) Y Z h0).
elim h.
elim h; intros h0 h1 h2.
simpl in h2; elim (disjoint_juxt_and h2); intros h3 h4.
exact (sub_juxt (IHM1 h0 X Y Z h3) (IHM2 h1 X Y Z h4)).
Qed.

Lemma FV_sub3 :
 forall (M : Adbmal) (X Y : stack), 
  (scb (juxt X Y) M) (* this ass nec? *)
   ->(sub (FV M X) (juxt Y (FV M (juxt X Y)))).
Proof.
induction M; intros X Y b.
simpl.
destruct (in_dec n X) as [h|h].
apply sub_nil.
intros u h1; elim h1; intro h2; [ rewrite <- h2; clear h1 h2 u | elim h2 ].
destruct (in_dec n (juxt X Y)) as [h0|h0].
apply in_or_juxt.
elim (in_juxt_or h0); intro h1.
right; exact (h h1).
left; exact h1.
apply in_or_juxt; right; left; reflexivity.
exact (IHM (cons n X) Y (scb_abs_inv b)).
elim (scb_eos_inv2 b); intros X' h; elim h; clear h; intros e b'.
rewrite e.
destruct X; simpl.
destruct (eq_dec n n) as [h|h]; [ clear h | elim h; reflexivity ].
simpl in e; rewrite e; intros u h; simpl; right;
exact (IHM Nil X' b' u h).
simpl in e; injection e; intros e1 e2.
rewrite e2.
destruct (eq_dec n n) as [h|h]; [ clear h | elim h; reflexivity ].
rewrite <- e1.
rewrite <- e1 in b'.
exact (IHM X Y b').
elim (scb_ap_inv b); intros b1 b2.
simpl.
intros u h; apply in_or_juxt; elim (in_juxt_or h); intro h0.
elim (in_juxt_or (IHM1 X Y b1 u h0)); intro h1.
left; exact h1.
right; apply in_or_juxt; left; exact h1.
elim (in_juxt_or (IHM2 X Y b2 u h0)); intro h1.
left; exact h1.
right; apply in_or_juxt; right; exact h1.
Qed.

Lemma kahrs_eos_free : 
forall (M N : Adbmal) (X Y : stack), (kahrs' M X N Y)->(eos_free M)->(eos_free N).
Proof.
intros M N X Y h.
unfold eos_free; rewrite (kahrs_skel h).
exact (fun d => d).
Qed.

Lemma kahrs_var_repl_tails : 
 forall (x y : name) (U V U' V' X Y : stack), 
  (In x X)
   ->(length X)=(length Y)
    ->(length U')=(length V')
     ->(kahrs' (var x) (juxt X U) (var y) (juxt Y V))
      ->(kahrs' (var x) (juxt X U') (var y) (juxt Y V')).
Proof.
induction X; intros Y h.
elim h.
destruct Y; simpl; intros h0 h1 h2.
discriminate h0.
injection h0; clear h0; intro h0.
inversion_clear h2.
apply kahrs_var2.
rewrite length_juxt in H; rewrite length_juxt in H; 
rewrite length_juxt; rewrite length_juxt; rewrite h0; rewrite h1; reflexivity.
assert (h2 : (In x X)).
elim h; intro h3.
elim H; symmetry; exact h3.
exact h3.
exact (kahrs_var3 H H0 (IHX Y h2 h0 h1 H1)).
Qed.

Lemma kahrs_var_top : 
 forall (x y : name) (X1 X2 Y1 Y2 : stack), 
  (length X1)=(length Y1)
   ->~(In x X1)
    ->~(In y Y1)
     ->(kahrs' (var x) (juxt X1 X2) (var y) (juxt Y1 Y2))
        <->(kahrs' (var x) X2 (var y) Y2).
Proof.
induction X1; destruct Y1; simpl; intros Y2 h h0 h1.
split; exact (fun d => d).
discriminate h.
discriminate h.
injection h; clear h; intro h.
elim (dmx h0); intros h2 h3.
elim (dmx h1); intros h4 h5.
split; intro h6.
inversion h6.
elim h2; symmetry; assumption.
exact (proj1 (IHX1 X2 Y1 Y2 h h3 h5) H7).
apply kahrs_var3.
intro h7; apply h2; symmetry; exact h7.
intro h7; apply h4; symmetry; exact h7.
exact (proj2 (IHX1 X2 Y1 Y2 h h3 h5) h6).
Qed.

Lemma kahrs_var_in_in : 
 forall (x y : name) (X1 X2 Y1 Y2 : stack), 
  (kahrs' (var x) (juxt X1 X2) (var y) (juxt Y1 Y2))
   ->(length X1)=(length Y1)
    ->(In x X1)
     ->(In y Y1).
Proof.
induction X1.
intros X2 Y1 Y2 h h0 h1; elim h1.
destruct Y1; simpl; intros Y2 h h0 h1.
discriminate h0.
injection h0; clear h0; intro h0.
inversion_clear h.
left; reflexivity.
right.
apply (IHX1 X2 Y1 Y2 H1 h0).
elim h1; intro h2.
elim H; symmetry; exact h2.
exact h2.
Qed.

Lemma kahrs_var_rm_top : 
 forall (x y : name) (X1 X2 Y1 Y2 : stack), 
  (length X1)=(length Y1)
   ->~(In x X1)
 (*   ->~(In y Y1) *) 
     ->(kahrs' (var x) (juxt X1 X2) (var y) (juxt Y1 Y2))
        ->(kahrs' (var x) X2 (var y) Y2).
Proof.
intros x y X1 X2 Y1 Y2 h h0 h1.
exact (proj1
  (kahrs_var_top x y X1 X2 Y1 Y2 h h0
    (fun d => h0 (kahrs_var_in_in Y1 Y2 X1 X2 (kahrs_symm h1) (eq_sym h) d)))
  h1).
Qed.
  
Lemma kahrs_var_weak : 
 forall (x y : name) (X1 X2 Y1 Y2 : stack), 
  (length X1)=(length Y1)
   ->~(In x X1)
    ->~(In y Y1)
     ->(kahrs' (var x) X2 (var y) Y2)
      ->(kahrs' (var x) (juxt X1 X2) (var y) (juxt Y1 Y2)).
Proof.
intros x y X1 X2 Y1 Y2 h h0 h1 h2.
exact (proj2 (kahrs_var_top x y X1 X2 Y1 Y2 h h0 h1) h2).
Qed.

Lemma kahrs_var_inj :
 forall (x y : name) (X : stack), 
  (kahrs' (var x) X (var y) X)
   ->x=y.
Proof.
induction X; simpl; intro h.
inversion h; reflexivity.
inversion_clear h.
reflexivity.
apply IHX; assumption.
Qed.

Lemma kahrs_eoss2 : 
 forall (M N : Adbmal) (X Y V W : stack), 
  (length X)=(length Y)
   ->(kahrs' M V N W)
    ->(kahrs' (eoss X M) (juxt X V) (eoss Y N) (juxt Y W)).
Proof.
induction X; destruct Y; simpl; intros V W h.
exact (fun d => d).
discriminate h.
discriminate h.
injection h; clear h; intros h h0.
apply kahrs_eos2.
exact (IHX Y V W h h0).
Qed.

Lemma kahrs_eoss2_inv : 
 forall (M N : Adbmal) (X Y V W : stack), 
  (length X)=(length Y)
   ->(kahrs' (eoss X M) (juxt X V) (eoss Y N) (juxt Y W))
    ->(kahrs' M V N W).
Proof.
induction X; destruct Y; simpl; intros V W h.
exact (fun d => d).
discriminate h.
discriminate h.
injection h; clear h; intros h h0.
inversion_clear h0.
exact (IHX Y V W h H).
elim H; reflexivity.
Qed.

Lemma kahrs_FV_eq' : 
 forall (M N : Adbmal), 
  (skeleton M)=(skeleton N) (* for proof convenience only *)
   ->forall (X1 X2 X : stack), 
      (length X1)=(length X2)
       ->(kahrs' M (juxt X1 X) N (juxt X2 X))
        ->(FV M X1)=(FV N X2).
Proof.
induction M; destruct N; intro h.
intros X1 X2 X d h0.
simpl; destruct (in_dec n X1) as [h1|h1]; destruct (in_dec n0 X2) as [h2|h2].
reflexivity.
elim h2; exact (kahrs_var_in_in X1 X X2 X h0 d h1).
elim h1; exact (kahrs_var_in_in X2 X X1 X (kahrs_symm h0)(eq_sym d) h2).
rewrite (kahrs_var_inj (kahrs_var_rm_top X1 X X2 X d h1 h0)); reflexivity.
discriminate h.
discriminate h.
discriminate h.
discriminate h.
simpl in h; injection h; clear h; intro h.
intros X1 X2 X d h0.
inversion_clear h0.
exact (IHM N h (cons n X1) (cons n0 X2) X (f_equal S d) H).
discriminate h.
discriminate h.
discriminate h.
discriminate h.
simpl in h; injection h; clear h; intro h.
induction X1; destruct X2; intros X h0.
clear h0.
simpl; induction X; intro h0; inversion_clear h0.
exact (IHM N h Nil Nil Nil eq_refl H). 
exact (IHM N h Nil Nil X eq_refl H).
exact (IHX H1).
discriminate h0.
discriminate h0.
simpl in h0; injection h0; clear h0; intro h0.
intro h1; simpl in h1; inversion_clear h1.
simpl; destruct (eq_dec a a) as [h1|h1].
destruct (eq_dec n1 n1) as [h2|h2].
exact (IHM N h X1 X2 X h0 H).
elim h2; reflexivity.
elim h1; reflexivity.
simpl; destruct (eq_dec n a) as [h1|h1].
elim (H h1).
destruct (eq_dec n0 n1) as [h2|h2].
elim (H0 h2).
exact (IHX1 X2 X h0 H1).
discriminate h.
discriminate h.
discriminate h.
discriminate h.
simpl in h; injection h; clear h; intros h h0.
intros X1 X2 X h1 h2.
inversion_clear h2.
simpl; rewrite (IHM1 N1 h0 X1 X2 X h1 H); rewrite (IHM2 N2 h X1 X2 X h1 H0); reflexivity.
Qed.

Lemma kahrs_FV_eq : 
 forall (M N : Adbmal) (X Y Z : stack), 
  (kahrs' M (juxt X Z) N (juxt Y Z))
   ->(FV M X)=(FV N Y).
Proof.
intros M N X Y Z h.
assert (h0 := (kahrs_list_length h)).
rewrite length_juxt in h0; rewrite length_juxt in h0.
assert (h1 := (simpl_plus_r (length Z) (length X) (length Y) h0)).
exact (kahrs_FV_eq' (kahrs_skel h) X Y Z h1 h).
Qed.

Lemma kahrs_FV_eq1 : 
 forall (M N : Adbmal) (X Y : stack), (kahrs' M X N Y)->(FV M X)=(FV N Y).
Proof.
intros M N X Y h.
rewrite (juxt_nil_end X) in h; rewrite (juxt_nil_end Y) in h.
exact (kahrs_FV_eq X Y Nil h).
Qed.

Lemma kahrs_FV_eq2 : 
 forall (M N : Adbmal) (X : stack), (kahrs' M X N X)->(FV M Nil)=(FV N Nil).
Proof.
intros M N X h; exact (kahrs_FV_eq Nil Nil X h).
Qed.

Fixpoint jump_min (Y X : stack) : stack :=
match Y with
| nil => Nil
| cons y ys as Y' =>
    match X with
    | nil => Y'
    | cons x xs =>
        match eq_dec x y with
        | left _ => jump_min ys xs
        | right _ => jump_min ys X
        end
    end
end.

Lemma FV_jump_min : forall (M : Adbmal) (Y X : stack), (FV (eoss X M) Y) = (FV M (jump_min Y X)).
Proof.
induction Y.
simpl.
induction X; auto.
induction X; simpl.
reflexivity.
destruct (eq_dec a0 a) as [h|h].
apply IHY.
exact (IHY (cons a0 X)).
Qed.

Lemma jump_min_emp : forall (X : stack), (jump_min X X)=Nil.
Proof.
induction X.
reflexivity.
simpl; destruct (eq_dec a a) as [h|h].
exact IHX.
elim h; reflexivity.
Qed.

Lemma FV_eoss_rm_top_stack :
 forall (M : Adbmal) (Y Z : stack), 
  (FV (eoss Z M) (juxt Z Y))=(FV M Y).
Proof.
induction Z; simpl.
reflexivity.
destruct (eq_dec a a) as [h|h].
exact IHZ.
elim h; reflexivity.
Qed.

Lemma FV_eoss_nil : forall (M : Adbmal) (X : stack), (FV (eoss X M) Nil)=(FV M Nil).
Proof.
induction X.
reflexivity.
exact IHX.
Qed.

Lemma subst_FV_sub :
 forall (M N : Adbmal) (x : name) (Z X Y : stack), 
   (sub (FV (adbmal_subst X Z M x N) (juxt Z Y))
     (juxt (FV M (juxt Z (cons x (jump_min Y X)))) (FV N Y))).
Proof. 
induction M; intros N x Z X Y.
(* var *)
simpl.
destruct (in_dec n Z) as [h|h]; simpl.
destruct (in_dec n (juxt Z Y)) as [h0|h0].
apply sub_nil.
elim h0; apply in_or_juxt; left; exact h.
destruct (eq_dec n x) as [h0|h0]; destruct (eq_dec x n) as [h1|h1].
rewrite FV_eoss_rm_top_stack.
intros a h2; apply in_or_juxt; right; exact h2.
elim h1; symmetry; exact h0.
elim h0; symmetry; exact h1.
rewrite FV_eoss_rm_top_stack.
rewrite FV_jump_min.
simpl.
destruct (in_dec n (jump_min Y X)) as [h2|h2].
apply sub_nil.
destruct (in_dec n (juxt Z (cons x (jump_min Y X)))) as [h3|h3].
apply False_ind; elim (in_juxt_or h3); intro h4.
exact (h h4).
elim h4; [ exact h1 | exact h2 ].
intros a h4; apply in_or_juxt; left; exact h4.
(* abs *)
exact (IHM N x (cons n Z) X Y).
(* eos *)
destruct (in_dec n Z) as [h|h].
elim (in_split eq_dec n Z h); intros Z1 h0; elim h0; intros Z2 h1; elim h1;
clear h0 h1; intros h0 h1.
rewrite h0.
rewrite (adbmal_subst_eos_clause1 M N x n X Z1 Z2 h1).
rewrite juxt_ass; rewrite juxt_ass.
rewrite (FV_eos_jump M n (juxt (cons n Z2) (cons x (jump_min Y X))) Z1 h1).
rewrite (FV_eos_jump (adbmal_subst X Z2 M x N) n (juxt (cons n Z2) Y) Z1 h1).
simpl; destruct (eq_dec n n) as [h2|h2]; [ apply IHM | elim h2; reflexivity ].
rewrite (FV_eos_jump M n (cons x (jump_min Y X)) Z h).
destruct (eq_dec x n) as [h0|h0].
rewrite (adbmal_subst_eos_clause2 M N X Z h0 h).
simpl; destruct (eq_dec n x) as [h1|h1].
rewrite FV_eoss_rm_top_stack.
intros a h2; apply in_or_juxt; left.
rewrite <- FV_jump_min; exact h2.
elim h1; symmetry; exact h0.
rewrite (adbmal_subst_eos_clause3 M N X Z h0 h).
rewrite FV_eoss_rm_top_stack.
simpl; destruct (eq_dec n x) as [h1|h1].
elim h0; symmetry; exact h1.
intros a h2; apply in_or_juxt; left.
fold (FV (eos n M) (jump_min Y X)).
rewrite (FV_jump_min (eos n M) Y X) in h2.
exact h2.
(* ap *)
simpl.
intros a h.
apply in_or_juxt.
elim (in_juxt_or h); intro h0.
elim (in_juxt_or (IHM1 N x Z X Y a h0)); intro h1.
left; apply in_or_juxt; left; exact h1.
right; exact h1.
elim (in_juxt_or (IHM2 N x Z X Y a h0)); intro h1.
left; apply in_or_juxt; right; exact h1.
right; exact h1.
Qed.

Lemma beta_FV_sub : forall (M N : Adbmal), (adbmal_beta M N)->forall (Y : stack), (sub (FV N Y)(FV M Y)).
Proof.
induction 1; intro Y.
exact (IHadbmal_beta (cons x Y)).
induction Y; simpl.
exact (IHadbmal_beta Nil).
destruct (eq_dec x a) as [h|h].
exact (IHadbmal_beta Y).
exact IHY.
simpl.
apply sub_juxt.
apply IHadbmal_beta.
apply sub_refl.
simpl; apply sub_juxt.
apply sub_refl.
apply IHadbmal_beta.
simpl.
rewrite FV_jump_min.
exact (subst_FV_sub M N x Nil X Y).
Qed.

Lemma not_in_renamed_term : 
 forall (x z z' : name) (M : Adbmal), 
  ~z'=z
   ->~(In z (names M))
    ->forall (Y : stack), ~(In z (names (rename M x z' Y))).
Proof.
intros x z z' M h.
induction M; simpl.
intros h0 Y.
destruct (eq_dec n x) as [h1|h1]; destruct (in_dec n Y) as [h2|h2].
exact h0.
simpl; intro h3; elim h3; intro h4.
exact (h h4).
exact h4.
exact h0.
exact h0.
intros h0 Y h1.
apply IHM with (Y := cons n Y).
intro h2; apply h0; right; exact h2.
elim h1; intro h2.
elim h0; left; exact h2.
exact h2.
intros h0 Y.
destruct (eq_dec x n) as [h1|h1].
elim Y; simpl.
intro h2; elim h2; intro h3.
exact (h h3).
apply h0; right; exact h3.
intros m Y' IHY.
destruct (eq_dec n m) as [h2|h2].
simpl; intro h3.
apply IHM with (Y := Y').
intro h4; apply h0; right; exact h4.
elim h3; intro h4.
elim h0; left; exact h4.
exact h4.
exact IHY.
elim Y; simpl.
exact h0.
intros m Y' IHY.
destruct (eq_dec n m) as [h2|h2].
simpl; intro h3.
apply IHM with (Y := Y').
intro h4; apply h0; right; exact h4.
elim h3; intro h4.
elim h0; left; exact h4.
exact h4.
exact IHY.
simpl; intros h0 Y h1.
elim (in_juxt_or h1); intro h2.
assert (d1 : ~(In z (names M1))).
intro h3; apply h0; apply in_or_juxt; left; exact h3.
exact (IHM1 d1 Y h2).
assert (d2 : ~(In z (names M2))).
intro h3; apply h0; apply in_or_juxt; right; exact h3.
exact (IHM2 d2 Y h2).
Qed.

Lemma in_not_in : 
 forall (M : Adbmal) (x y : name), (In x (names M))->~(In y (names M))->~x=y.
Proof.
intros M x y h h0 h1; apply h0; rewrite <- h1; exact h.
Qed.

Lemma rename_eos_not_in : 
 forall (x y z : name) (M : Adbmal) (X Y : stack), 
  ~(In y X)
   ->(rename (eos y M) x z (juxt X Y))
      =(rename (eos y M) x z Y).
Proof.
induction X.
reflexivity.
intros Y h.
assert (h0 : ~(In y X)).
intro h0; apply h; right; exact h0.
simpl.
destruct (eq_dec y a) as [h1|h1]; simpl.
elim h; left; symmetry; exact h1.
exact (IHX Y h0).
Qed.

Lemma kahrs_rename :
 forall (x y : name) (M : Adbmal) (X Y : stack), 
  ~(In y Y)
   ->~(In y (names M))
   ->(kahrs' M (juxt Y (cons x X)) (rename M x y Y) (juxt Y (cons y X))).
Proof.
induction M; intros X Y h h0.
(* var *)
simpl; destruct (in_dec n Y) as [h1|h1].
apply (kahrs_var_repl_tails X X (cons x X) (cons y X) Y Y h1).
reflexivity.
reflexivity.
apply kahrs_refl.
destruct (eq_dec n x) as [h2|h2].
apply (kahrs_var_weak Y Y).
reflexivity.
exact h1.
exact h.
rewrite h2; apply kahrs_var2.
reflexivity.
apply (kahrs_var_weak Y Y).
reflexivity.
exact h1.
exact h1.
apply kahrs_var3.
exact h2.
intro h3; apply h0; left; exact h3.
apply kahrs_refl.
(* abs *)
simpl; apply kahrs_abs.
apply (IHM X (cons n Y)).
intro h1; elim h1; intro h2.
apply h0; left; exact h2.
exact (h h2).
intro h1; apply h0; right; exact h1.
(* eos *)
destruct (in_dec n Y) as [h1|h1].
elim (in_split eq_dec n Y h1); intros Y1 h2; elim h2; clear h2; intros
  Y2 h2; elim h2; clear h2; intros h3 h4.
rewrite h3.
rewrite (rename_eos_not_in x n y M Y1 (cons n Y2) h4).
simpl.
destruct (eq_dec n n) as [h5|h5].
rewrite juxt_ass.
rewrite juxt_ass.
apply kahrs_eos3_gen.
exact h4.
exact h4.
reflexivity.
simpl.
apply kahrs_eos2.
apply IHM.
intro h6; apply h; rewrite h3; apply in_or_juxt; right; right; exact h6.
intro h6; apply h0; right; exact h6.
elim h5; reflexivity.
pattern Y at 2; rewrite (juxt_nil_end Y);
rewrite (rename_eos_not_in x n y M Y Nil h1).
simpl.
destruct (eq_dec x n) as [h2|h2].
apply kahrs_eos3_gen.
exact h1.
exact h.
reflexivity.
rewrite h2.
apply kahrs_eos2.
apply kahrs_refl.
apply kahrs_eos3_gen.
exact h1.
exact h1.
reflexivity.
apply kahrs_eos3.
intro h3; apply h2; symmetry; exact h3.
intro h3; apply h0; left; exact h3.
apply kahrs_refl.
simpl in h0.
simpl; apply kahrs_ap.
apply IHM1.
exact h.
intro h1; apply h0; apply in_or_juxt; left; exact h1.
apply IHM2.
exact h.
intro h1; apply h0; apply in_or_juxt; right; exact h1.
Qed.

Lemma scb_rename2 : 
 forall (M : Adbmal) (x z : name) (X1 X2 : stack), 
  ~(In z (names M))
   ->~(In z X1)
    ->(scb (juxt X1 (cons z X2))(rename M x z X1))
     ->(scb (juxt X1 (cons x X2)) M).
Proof.
induction M; intros x z X1 X2 d1 d2.
intro h; apply scb_var.
simpl; intro h; apply scb_abs.
assert (h0 := (scb_abs_inv h)).
assert (d1' : ~(In z (names M))).
intro h1; apply d1; right; exact h1.
assert (d2' : ~(In z (cons n X1))).
intro h1; elim h1; intro h2.
apply d1; simpl; left; exact h2.
exact (d2 h2).
exact (IHM x z (cons n X1) X2 d1' d2' h0).
(*!*)destruct (in_dec n X1) as [h|h].
elim (in_split eq_dec n X1 h); intros Y1 h0; elim h0; clear h0; intros Y2 h0;
 elim h0; clear h0; intros h0 h1.
rewrite h0.
rewrite (rename_eos_not_in x n z M Y1 (cons n Y2) h1).
simpl.
destruct (eq_dec n n) as [h2|h2]; simpl.
rewrite juxt_ass.
rewrite juxt_ass.
simpl.
destruct Y1; simpl; intro h3.
apply scb_eos.
elim (scb_eos_inv h3); intros h4 h5.
apply (IHM x z Y2 X2).
intro h6; apply d1; right; exact h6.
simpl in h0; rewrite h0 in d2.
intro h6; apply d2; right; exact h6.
exact h5.
elim (scb_eos_inv h3); intros h4 h5.
elim h1; left; symmetry; exact h4.
elim h2; reflexivity.
pattern X1 at 2; rewrite (juxt_nil_end X1).
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec x n) as [h0|h0].
destruct X1; simpl.
intro h1.
elim (scb_eos_inv h1); intros h2 h3.
rewrite h0; apply scb_eos; exact h3.
intro h1; elim (scb_eos_inv h1); intros h2 h3.
elim d2; left; symmetry; exact h2.
destruct X1; simpl.
intro h1.
elim (scb_eos_inv h1); intros h2 h3.
elim d1; left; exact h2.
intro h1; elim (scb_eos_inv h1); intros h2 h3.
elim h; left; symmetry; exact h2.
exact h.
simpl.
intro h.
elim (scb_ap_inv h); intros h0 h1.
apply scb_ap.
apply (IHM1 x z).
intro h2; apply d1; simpl; apply in_or_juxt; left; exact h2.
exact d2.
exact h0.
apply (IHM2 x z).
intro h2; apply d1; simpl; apply in_or_juxt; right; exact h2.
exact d2.
exact h1.
Qed.

(** [M[x:=z,XyY][y:=z',X] = M[y:=z',X][x:z,Xz'Y]] *)

Lemma rename_commutes :
 forall (x y z z' : name), 
 ~z=y
  ->forall (M : Adbmal), 
     ~(In z (names M))
      ->~(In z' (names M))
       ->forall (X Y : stack), 
          ~(In z' X)
            ->~(In z X)
             -> (rename (rename M x z (juxt X (cons y Y))) y z' X)
                 =(rename (rename M y z' X) x z (juxt X (cons z' Y))).
Proof.
intros x y z z' h0 M h2 h3.
induction M; intros X Y H H5.
(* var *)
simpl.
destruct (in_dec n X) as [h4|h4]; simpl.
destruct (in_dec n (juxt X (cons y Y))) as [h5|h5]; simpl.
destruct (in_dec n X) as [h6|h6]; simpl.
destruct (in_dec n (juxt X (cons z' Y))) as [h7|h7]; simpl.
reflexivity.
elim h7; apply in_or_juxt; left; exact h6.
elim h6; exact h4.
elim h5; apply in_or_juxt; left; exact h4.
destruct (in_dec n (juxt X (cons y Y))) as [h5|h5]; simpl.
destruct (in_dec n X) as [h6|h6]; simpl.
elim h4; exact h6.
elim (in_juxt_or h5); intro h7.
elim h6; exact h7.
destruct (eq_dec n y) as [h8|h8]; simpl.
destruct (in_dec z' (juxt X (cons z' Y))) as [h9|h9]; simpl.
reflexivity.
elim h9; apply in_or_juxt; right; left; reflexivity.
elim h7; intro h9.
elim h8; symmetry; exact h9.
destruct (in_dec n (juxt X (cons z' Y))) as [h10|h10]; simpl.
reflexivity.
elim h10; apply in_or_juxt; right; right; exact h9.
destruct (eq_dec n x) as [h6|h6]; simpl.
destruct (in_dec z X) as [h7|h7]; simpl.
destruct (eq_dec n y) as [h8|h8]; simpl.
elim h5; apply in_or_juxt; right; left; symmetry; exact h8.
destruct (in_dec n (juxt X (cons z' Y))) as [h9|h9]; simpl.
elim (in_juxt_or h9); intro h10.
elim h4; exact h10.
elim h10; intro h11.
elim h3; left; symmetry; exact h11.
elim h5; apply in_or_juxt; right; right; exact h11.
destruct (eq_dec n x) as [h10|h10]; simpl.
reflexivity.
elim h10; exact h6.
destruct (eq_dec z y) as [h8|h8]; simpl.
elim h0; exact h8.
destruct (eq_dec n y) as [h9|h9]; simpl.
elim h5; apply in_or_juxt; right; left; symmetry; exact h9.
destruct (in_dec n (juxt X (cons z' Y))) as [h10|h10]; simpl.
elim (in_juxt_or h10); intro h11.
elim h4; exact h11.
elim h11; intro h12.
elim h3; left; symmetry; exact h12.
elim h5; apply in_or_juxt; right; right; exact h12.
destruct (eq_dec n x) as [h11|h11]; simpl.
reflexivity.
elim h11; exact h6.
destruct (in_dec n X) as [h7|h7]; simpl.
elim h4; exact h7.
destruct (eq_dec n y) as [h8|h8]; simpl.
destruct (in_dec z' (juxt X (cons z' Y))) as [h9|h9]; simpl.
reflexivity.
elim h9; apply in_or_juxt; right; left; reflexivity.
destruct (in_dec n (juxt X (cons z' Y))) as [h9|h9]; simpl.
reflexivity.
destruct (eq_dec n x) as [h10|h10]; simpl.
elim h6; exact h10.
reflexivity.
(* abs *)
simpl.
assert (h4 : ~(In z (names M))).
intro h4; apply h2; right; exact h4.
assert (h5 : ~(In z' (names M))).
intro h5; apply h3; right; exact h5.
apply f_equal.
assert (H0 : ~(In z' (cons n X))).
intro H1; elim H1; intro H2.
apply h3; left; exact H2.
exact (H H2).
assert (H6 : ~(In z (cons n X))).
intro H6; elim H6; intro H7.
apply h2; left; exact H7.
exact (H5 H7).
exact (IHM h4 h5 (cons n X) Y H0 H6).
(* eos *) 
assert (h4 : ~(In z (names M))).
intro h4; apply h2; right; exact h4.
assert (h5 : ~(In z' (names M))).
intro h5; apply h3; right; exact h5.
destruct (in_dec n X) as [h6|h6].
(* (In n X) *)
elim (in_split eq_dec n X h6); intros X1 h7; elim h7; clear h7; 
 intros X2 h7; elim h7; clear h7; intros h7 h8.
assert (H0 : ~(In z' X2)).
intro h9; apply H; rewrite h7; apply in_or_juxt; right; right; exact h9.
assert (H6 : ~(In z X2)).
intro h9; apply H5; rewrite h7; apply in_or_juxt; right; right; exact h9.
rewrite h7.
rewrite juxt_ass.
rewrite juxt_ass.
rewrite (rename_eos_not_in x n z M X1 (juxt (cons n X2) (cons y Y)) h8).
rewrite (rename_eos_not_in y n z' M X1 (cons n X2) h8).
simpl.
destruct (eq_dec n n) as [h9|h9].
rewrite rename_eos_not_in.
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec n n) as [h10|h10].
rewrite (IHM h4 h5 X2 Y H0 H6); reflexivity.
elim h10; reflexivity.
exact h8.
exact h8.
elim h9; reflexivity.
(* ~(In n X) *)
rewrite rename_eos_not_in.
pattern X at 2; rewrite (juxt_nil_end X); rewrite rename_eos_not_in.
simpl.
destruct (eq_dec n y) as [h7|h7].
pattern X at 1; rewrite (juxt_nil_end X).
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec y n) as [h8|h8].
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec z' z') as [h9|h9]; simpl.
reflexivity.
elim h9; reflexivity.
exact H.
elim h8; symmetry; exact h7.
exact h6.
destruct (eq_dec x n) as [h8|h8]; simpl.
destruct (eq_dec y n) as [h9|h9].
elim h7; symmetry; exact h9.
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec n z') as [h10|h10].
elim h3; left; exact h10.
destruct (eq_dec x n) as [h11|h11]; simpl.
induction Y.
pattern X; rewrite (juxt_nil_end X); rewrite rename_eos_not_in.
simpl.
destruct (eq_dec y z) as [h12|h12].
elim h0; symmetry; exact h12.
reflexivity.
exact H5.
destruct (eq_dec n a) as [h12|h12].
pattern X; rewrite (juxt_nil_end X); rewrite rename_eos_not_in.
simpl.
destruct (eq_dec y n) as [h13|h13].
elim (h9 h13).
reflexivity.
exact h6.
exact IHY.
elim (h11 h8).
exact h6.
destruct (eq_dec y n) as [h9|h9].
elim h7; symmetry; exact h9.
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec n z') as [h10|h10]; simpl.
elim h3; left; exact h10.
destruct (eq_dec x n) as [h11|h11]; simpl.
elim (h8 h11).
induction Y.
pattern X; rewrite (juxt_nil_end X); rewrite rename_eos_not_in.
simpl.
destruct (eq_dec y n) as [h12|h12]; simpl.
elim (h9 h12).
reflexivity.
exact h6.
destruct (eq_dec n a) as [h12|h12].
pattern X; rewrite (juxt_nil_end X); rewrite rename_eos_not_in.
simpl.
destruct (eq_dec y n) as [h13|h13].
elim (h9 h13).
reflexivity.
exact h6.
exact IHY.
exact h6.
exact h6.
exact h6.
(* ap *)
assert (h4 : ~(In z (names M1))/\~(In z (names M2))).
split; intro h4; apply h2; simpl.
apply in_or_juxt; left; exact h4.
apply in_or_juxt; right; exact h4.
elim h4; clear h4; intros h4 h5.
assert (h6 : ~(In z' (names M1))/\~(In z' (names M2))).
split; intro h6; apply h3; simpl.
apply in_or_juxt; left; exact h6.
apply in_or_juxt; right; exact h6.
elim h6; clear h6; intros h6 h7.
simpl.
rewrite (IHM1 h4 h6 X Y H H5).
rewrite (IHM2 h5 h7 X Y H H5).
reflexivity.
Qed.

Lemma rename_trans : 
 forall (x z z' : name) (M : Adbmal) (X : stack), 
  ~(In z (names M))
   ->~(In z X)
    ->(rename (rename M x z X) z z' X)
       =(rename M x z' X).
Proof.
induction M.
(* var *)
simpl.
intros X h h0.
destruct (in_dec n X) as [h1|h1]; simpl.
destruct (in_dec n X) as [h2|h2]; simpl.
reflexivity.
elim h2; exact h1.
destruct (eq_dec n x) as [h2|h2]; simpl.
destruct (in_dec z X) as [h3|h3]; simpl.
elim h0; exact h3.
destruct (eq_dec z z) as [h4|h4]; simpl.
reflexivity.
elim h4; reflexivity.
destruct (in_dec n X) as [h3|h3]; simpl.
elim h1; exact h3. (*Reflexivity.*)
destruct (eq_dec n z) as [h4|h4]; simpl.
elim h; left; exact h4.
reflexivity.
(* abs *)
simpl.
intros X h h0.
rewrite IHM.
reflexivity.
intro h1; apply h; right; exact h1.
intro h1; elim h1; intro h2.
apply h; left; exact h2.
exact (h0 h2).
(* eos *)
intros X h h0.
destruct (in_dec n X) as [h1|h1].
elim (in_split eq_dec n X h1); intros X1 h2; elim h2; clear h2; 
 intros X2 h2; elim h2; clear h2; intros h2 h3.
rewrite h2.
rewrite rename_eos_not_in.
rewrite rename_eos_not_in.
assert (h4 : ~(In z X1)).
intro h4; apply h0; rewrite h2; apply in_or_juxt; left; exact h4.
simpl.
destruct (eq_dec n n) as [h5|h5].
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec n n) as [h6|h6].
rewrite IHM.
reflexivity.
intro h7; apply h; right; exact h7.
intro h7; apply h0; rewrite h2; apply in_or_juxt; right; right;
exact h7.
elim h6; reflexivity.
exact h3.
elim h5; reflexivity.
exact h3.
exact h3.
pattern X; rewrite (juxt_nil_end X).
rewrite rename_eos_not_in.
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec x n) as [h2|h2].
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec z z) as [h3|h3].
reflexivity.
elim h3; reflexivity.
exact h0.
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec z n) as [h3|h3].
elim h; left; symmetry; exact h3.
reflexivity.
exact h1.
exact h1.
exact h1.
(* ap *)
intros X h h0.
simpl.
rewrite IHM1.
rewrite IHM2.
reflexivity.
intro h1; apply h; simpl; apply in_or_juxt; right; exact h1.
exact h0.
intro h1; apply h; simpl; apply in_or_juxt; left; exact h1.
exact h0.
Qed.

Inductive schroer' : Adbmal->Adbmal->stack->Prop :=
| schroer_rule : forall (M N : Adbmal) (x y z : name) (Z : stack), 
                    ~(In z (names M))
                     ->~(In z (names N))
                      ->~(In z Z)
                       ->(schroer' (rename M x z Nil)(rename N y z Nil) Z)
                        ->(schroer' (abs x M)(abs y N)(cons z Z))
| schroer_var  : forall (z : name) (Z : stack), (schroer' (var z)(var z) Z)
| schroer_eos  : forall (M N : Adbmal) (x : name) (Z : stack), 
                    (schroer' M N Z)
                     ->(schroer' (eos x M)(eos x N) Z)
| schroer_ap   : forall (M M' N N' : Adbmal) (Z : stack), 
                    (schroer' M M' Z)
                     ->(schroer' N N' Z)
                      ->(schroer' (ap M N)(ap M' N') Z).

Definition schroer := fun M N : Adbmal => exists Z : stack, schroer' M N Z.

(** We write [M=(Z)N] for [(schroer' M N Z)]. *)

(** [M=(Z)N => M[x:=z,Y]=(Z)N[x:=z,Y]] *)

Lemma scb_schroer : 
 forall (M N : Adbmal) (Z : stack), 
  (schroer' M N Z)
   ->forall (X : stack), 
      (scb X M)
       ->(scb X N).
Proof.
induction 1; intros X h.
apply scb_abs.
assert (h0 := (scb_abs_inv h)).
assert (h1 := (scb_rename x z Nil X h0)).
simpl in h1.
assert (h2 := (IHschroer' (cons z X) h1)).
assert (h3 : ~(In z Nil)).
exact (fun h => h).
exact (scb_rename2 N y z Nil X H0 h3 h2).
exact h.
elim (scb_eos_inv2 h); intros X' h0.
elim h0; clear h0; intros h0 h1.
rewrite h0.
apply scb_eos.
apply IHschroer'.
exact h1.
elim (scb_ap_inv h); intros h1 h2.
apply scb_ap.
apply IHschroer'1.
exact h1.
apply IHschroer'2; exact h2.
Qed.

Lemma schroer_skel :
 forall (M N : Adbmal) (Z : stack), 
  (schroer' M N Z)
   ->(skeleton M)=(skeleton N).
Proof.
induction 1; simpl.
rewrite <- (rename_skel_eq x z M Nil) in IHschroer'.
rewrite <- (rename_skel_eq y z N Nil) in IHschroer'.
rewrite IHschroer'; reflexivity.
reflexivity.
rewrite IHschroer'; reflexivity.
rewrite IHschroer'1; rewrite IHschroer'2; reflexivity.
Qed.

Lemma schroer'_rename_same : 
 forall (M N : Adbmal) (x z : name) (Z : stack), 
  (schroer' M N Z)
   ->~(In z Z)
    ->~(In z (names M))
     ->~(In z (names N))
      ->forall (Y : stack), (schroer' (rename M x z Y)(rename N x z Y) Z).
Proof.
intros M N x z Z h.
elim h; clear h M N Z.
(* abs *)
simpl.
intros M N y1 y2 z' Z h h0 h1 h2 ih h3 h4 h5 Y.
assert (h6 : ~z'=z).
intro h6; apply h3; left; exact h6.
assert (h7 : ~(In z Z)).
intro h7; apply h3; right; exact h7.
clear h3.
assert (h8 : (schroer' (rename (rename M x z (cons y1 Y)) y1 z' Nil)
              (rename (rename N x z (cons y2 Y)) y2 z' Nil) Z)).
replace (cons y1 Y) with (juxt Nil (cons y1 Y)).
rewrite rename_commutes.
replace (cons y2 Y) with (juxt Nil (cons y2 Y)).
rewrite rename_commutes.
apply ih.
exact h7.
apply not_in_renamed_term.
exact h6.
intro h8; apply h4; right; exact h8.
apply not_in_renamed_term.
exact h6.
intro h8; apply h5; right; exact h8.
intro h8; apply h5; left; symmetry; exact h8.
intro h8; apply h5; right; exact h8.
exact h0.
exact (fun f => f).
exact (fun f => f).
reflexivity.
intro h8; apply h4; left; symmetry; exact h8.
intro h8; apply h4; right; exact h8.
exact h.
exact (fun f => f).
exact (fun f => f).
reflexivity.
apply schroer_rule.
apply not_in_renamed_term.
intro h9; apply h6; symmetry; exact h9.
exact h.
apply not_in_renamed_term.
intro h9; apply h6; symmetry; exact h9.
exact h0.
exact h1.
exact h8.
(* var *)
simpl.
intros y Z h h0 h1 Y.
destruct (in_dec y Y) as [h2|h2]; simpl.
apply schroer_var.
destruct (eq_dec y x) as [e|ne]; apply schroer_var.
(* eos *)
intros M N y Z h ih h0 h1 h2 Y.
destruct (in_dec y Y) as [h3|h3].
elim (in_split eq_dec y Y h3); intros Y1 h4; elim h4; clear h4; intros
  Y2 h4; elim h4; clear h4; intros h5 h6.
rewrite h5.
rewrite rename_eos_not_in.
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec y y) as [h7|h7].
apply schroer_eos.
apply ih.
exact h0.
intro h8; apply h1; right; exact h8.
intro h8; apply h2; right; exact h8.
elim h7; reflexivity.
exact h6.
exact h6.
pattern Y; rewrite (juxt_nil_end Y).
rewrite rename_eos_not_in.
rewrite rename_eos_not_in.
simpl.
destruct (eq_dec x y) as [h4|h4]; apply schroer_eos; exact h.
exact h3.
exact h3.
(* ap *)
simpl.
intros M M' N N' Z aM ihM aN ihN h h0 h1 Y.
apply schroer_ap.
apply ihM.
exact h.
intro h2; apply h0; apply in_or_juxt; left; exact h2.
intro h2; apply h1; apply in_or_juxt; left; exact h2.
apply ihN.
exact h.
intro h2; apply h0; apply in_or_juxt; right; exact h2.
intro h2; apply h1; apply in_or_juxt; right; exact h2.
Qed.

(** [M[x:=z,nil]=(Z)N[y:=z,nil] => M[x:=z',nil]=(Z)N[y:=z',nil]] *)

Lemma rename_diff_schroer' : 
 forall (M N : Adbmal) (Z : stack) (x y z z' : name), 
  ~(In z (names M))
   ->~(In z (names N))
    ->~(In z' (names M))
     ->~(In z' (names N))
      ->~(In z' Z)
       ->(schroer' (rename M x z Nil)(rename N y z Nil) Z)
        ->(schroer' (rename M x z' Nil)(rename N y z' Nil) Z).
Proof.
intros M N Z x y z z'.
destruct (eq_dec z' z) as [h|h]; intros h0 h1 h2 h3 h4 h5.
rewrite h; exact h5.
assert (h6 : ~(In z' (names (rename M x z Nil)))).
apply not_in_renamed_term.
intro h6; apply h; symmetry; exact h6.
exact h2.
assert (h7 : ~(In z' (names (rename N y z Nil)))).
apply not_in_renamed_term.
intro h7; apply h; symmetry; exact h7.
exact h3.
assert (h8 := (schroer'_rename_same z z' h5 h4 h6 h7 Nil)).
rewrite rename_trans in h8.
rewrite rename_trans in h8.
exact h8.
exact h1.
exact (fun f => f).
exact h0.
exact (fun f => f).
Qed.

(** [M=(Z)N => \x.M=(wZ)\x.N] for some [w] *)

Lemma schroer'_abs : 
 forall (M N : Adbmal) (x : name) (Z : stack), 
  (schroer' M N Z)->(exists w : name, (schroer' (abs x M)(abs x N)(cons w Z))).
Proof.
intros M N x Z h.
elim (inf_many_names (juxt Z (juxt (names M) (names N))));
intros w h1.
exists w.
assert (h2 : ~(In w Z)).
intro h2; apply h1; apply in_or_juxt; left; exact h2.
assert (h3 : ~(In w (names M))).
intro h3; apply h1; apply in_or_juxt; right; apply in_or_juxt;
 left; exact h3.
assert (h4 : ~(In w (names N))).
intro h4; apply h1; apply in_or_juxt; right; apply in_or_juxt;
 right; exact h4.
apply schroer_rule.
exact h3.
exact h4.
exact h2.
exact (schroer'_rename_same x w h h2 h3 h4 Nil).
Qed.

Lemma le_Sn_m : forall (n m : nat), (le (S n) m)->(exists m' : nat, m=(S m')/\(le n m')).
Proof.
induction n; destruct m; intro h.
inversion h.
exists m; split.
reflexivity.
apply le_0_n.
inversion h.
exists m; split.
reflexivity.
apply le_S_n.
exact h.
Qed.

(** [M=(Z1)N => M=(Z2)N] for [Z2] disjoint from [Z1], [|Z2|>=|Z1|],
   none of the [z] in [Z2] occur in [MN], and all elements of [Z2] distinct *)

Lemma schroer_change_Z :
 forall (M N : Adbmal) (Z1 : stack), 
  (schroer' M N Z1)
   ->forall (Z2 : stack), 
      (le (length Z1)(length Z2))
       ->(disjoint Z2 Z1)
        ->(disjoint Z2 (names M))
         ->(disjoint Z2 (names N))
          ->(all_distinct Z2)
           ->(schroer' M N Z2).
Proof.
induction 1; simpl.
intros Z2 h3.
elim (le_Sn_m h3); intros n h4; elim h4; clear h4; intros h4 h5.
elim (length_S Z2 h4); intros z' h6; elim h6; clear h6; intros Z2' h6.
rewrite h6.
intros h7 h8 h9 h10.
inversion_clear h10.
assert (h13 := (h7 z' (or_introl eq_refl))).
assert (h14 : ~z=z').
 intro h14; apply h13; left; exact h14.
assert (h15 : ~(In z' Z)).
 intro h15; apply h13; right; exact h15.
assert (h16 : ~(In z' (names M))).
 intro h16; apply (h8 z' (or_introl eq_refl));
 right; exact h16.
assert (h17 : ~(In z' (names N))).
 intro h17; apply (h9 z' (or_introl eq_refl));
 right; exact h17.
apply schroer_rule.
exact h16.
exact h17.
exact H4.
assert (h18 : (schroer' (rename M x z Nil) (rename N y z Nil) Z2')).
apply IHschroer'.
rewrite h6 in h3; apply le_S_n; exact h3.
unfold disjoint; intros a h18 h19;
 apply (h7 a (or_intror h18)); right; exact h19.
unfold disjoint; intros a h18; apply not_in_renamed_term.
intro h19; apply (h7 a (or_intror h18)); left; exact h19.
intro h20; apply (h8 a (or_intror h18)); right; exact h20.
unfold disjoint; intros a h18; apply not_in_renamed_term.
intro h19; apply (h7 a (or_intror h18)); left; exact h19.
intro h20; apply (h9 a (or_intror h18)); right; exact h20.
exact H3.
exact (rename_diff_schroer' M N x y z z' H H0 h16 h17 H4 h18).
(* var *)
intros; apply schroer_var.
(* eos *)
intros Z2 h0 h1 h2 h3 h4.
apply schroer_eos.
apply IHschroer'.
exact h0.
exact h1.
unfold disjoint; intros z h5 h6; apply (h2 z h5); right; exact h6.
unfold disjoint; intros z h5 h6; apply (h3 z h5); right; exact h6.
exact h4.
(* ap *)
intros Z2 h2 h3 h4 h5 h6.
apply schroer_ap.
apply IHschroer'1.
exact h2.
exact h3.
unfold disjoint; intros z h7 h8; apply (h4 z h7); 
 apply in_or_juxt; left; exact h8.
unfold disjoint; intros z h7 h8; apply (h5 z h7); 
 apply in_or_juxt; left; exact h8.
exact h6.
apply IHschroer'2.
exact h2.
exact h3.
unfold disjoint; intros z h7 h8; apply (h4 z h7); 
 apply in_or_juxt; right; exact h8.
unfold disjoint; intros z h7 h8; apply (h5 z h7); 
 apply in_or_juxt; right; exact h8.
exact h6.
Qed.

Lemma fresh_list : 
 forall (n : nat) (l : stack), 
  {m:stack|(length m)=n/\(disjoint m l)/\(all_distinct m)}.
Proof.
unfold disjoint; induction n; simpl; intro l.
exists Nil; split.
reflexivity.
split.
intros a h; elim h.
apply all_distinct_nil.
elim (IHn l); intros m h; elim h; intros h0 h1; elim h1; clear h1; intros h1 h2.
elim (inf_many_names (juxt l m)); intros a h3.
assert (h4 : ~(In a l)).
intro h4; apply h3; apply in_or_juxt; left; exact h4.
assert (h5 : ~(In a m)).
intro h5; apply h3; apply in_or_juxt; right; exact h5.
exists (cons a m); split.
simpl; rewrite h0; reflexivity.
split.
intros b h6 h7.
elim h6; intro h8.
apply h4; rewrite h8; exact h7.
exact (h1 b h8 h7).
apply all_distinct_cons.
exact h2.
exact h5.
Qed.

Lemma schroer_ap_Z1Z2 : 
 forall (M1 M2 N1 N2 : Adbmal) (Z1 Z2 : stack), 
  (schroer' M1 N1 Z1)
   ->(schroer' M2 N2 Z2)
    ->(exists Z : stack,  (schroer' (ap M1 M2) (ap N1 N2) Z)).
Proof.
intros M1 M2 N1 N2 Z1 Z2 h h0.
elim (fresh_list (max (length Z1)(length Z2))
      (juxt (juxt Z1 Z2) 
       (juxt (juxt (names M1) (names M2))
         (juxt (names N1) (names N2)))));
 intros Z3 h3; elim h3; clear h3; intros h3 h4; elim h4; clear h4;
 intros h4 h5.
exists Z3.
elim (disjoint_juxt_and h4); clear h4; intros h6 h7.
elim (disjoint_juxt_and h6); clear h6; intros h8 h9.
elim (disjoint_juxt_and h7); clear h7; intros h10 h11.
elim (disjoint_juxt_and h10); clear h10; intros h4 h6.
elim (disjoint_juxt_and h11); clear h11; intros h7 h10.
elim (Nat.max_dec (length Z1) (length Z2)); intro h12; rewrite h12 in h3.
(* (max (length Z1) (length Z2))=(length Z1) *)
assert (h13 : (le (length Z1) (length Z3))).
 rewrite h3; apply le_n.
assert (h14 : (le (length Z2) (length Z3))).
 rewrite h3; rewrite <- h12; apply Nat.le_max_r.
apply schroer_ap.
apply (schroer_change_Z h h13).
exact h8.
exact h4.
exact h7.
exact h5.
apply (schroer_change_Z h0 h14).
exact h9.
exact h6.
exact h10.
exact h5.
(* (max (length Z1) (length Z2))=(length Z2) *)
assert (h13 : (le (length Z1) (length Z3))).
 rewrite h3; rewrite <- h12; apply Nat.le_max_l.
assert (h14 : (le (length Z2) (length Z3))).
 rewrite h3; apply le_n.
apply schroer_ap.
apply (schroer_change_Z h h13).
exact h8.
exact h4.
exact h7.
exact h5.
apply (schroer_change_Z h0 h14).
exact h9.
exact h6.
exact h10.
exact h5.
Qed.

Lemma schroer'_refl : forall (M : Adbmal), (exists Z : stack, (schroer' M M Z)).
Proof.
induction M.
(* var *)
exists Nil; apply schroer_var.
(* abs *)
elim IHM; intros Z h.
elim (schroer'_abs n h); intros w h0.
exists (cons w Z); exact h0.
(* eos *)
elim IHM; intros Z h.
exists Z; apply schroer_eos; exact h.
(* ap *)
elim IHM1; intros Z1 h1.
elim IHM2; intros Z2 h2.
exact (schroer_ap_Z1Z2 h1 h2).
Qed.

Lemma schroer_refl : forall (M : Adbmal), (schroer M M).
Proof.
intro M; exact (schroer'_refl M).
Qed.

Lemma schroer'_symm : 
 forall (M N : Adbmal) (Z : stack), (schroer' M N Z)->(schroer' N M Z).
Proof.
induction 1.
apply schroer_rule; assumption.
apply schroer_var.
apply schroer_eos; assumption.
apply schroer_ap; assumption.
Qed.

Lemma schroer_symm : forall (M N : Adbmal), (schroer M N)->(schroer N M).
Proof.
intros M N h; elim h; intros Z h0.
exists Z.
exact (schroer'_symm h0).
Qed.

Lemma schroer'_tranzzz : 
 forall (M N : Adbmal) (Z : stack), 
  (schroer' M N Z)
   ->forall (P : Adbmal), 
      (schroer' N P Z)
       ->(schroer' M P Z).
Proof.
induction 1; simpl; intros P h; inversion_clear h.
apply schroer_rule.
exact H.
exact H4.
exact H1.
apply IHschroer'; exact H6.
apply schroer_var.
apply schroer_eos.
apply IHschroer'.
exact H0.
apply schroer_ap.
apply IHschroer'1.
exact H1.
apply IHschroer'2.
exact H2.
Qed.

Lemma schroer'_trans : 
 forall (M N : Adbmal) (Z1 : stack), 
  (schroer' M N Z1)
   ->forall (P : Adbmal) (Z2 : stack), 
      (schroer' N P Z2)
       ->(exists Z3 : stack, (schroer' M P Z3)).
Proof.
intros M N Z1 h P Z2 h0.
elim (fresh_list (max (length Z1)(length Z2))
       (juxt (juxt Z1 Z2) 
             (juxt (names M)(juxt (names N)(names P)))));
 intros Z3 h3; elim h3; clear h3; intros h3 h4; elim h4; clear h4;
 intros h4 h5.
exists Z3.
elim (disjoint_juxt_and h4); clear h4; intros h6 h7.
elim (disjoint_juxt_and h6); clear h6; intros h8 h9.
elim (disjoint_juxt_and h7); clear h7; intros h10 h11.
elim (disjoint_juxt_and h11); clear h11; intros h11 h12.
elim (Nat.max_dec (length Z1) (length Z2)); intro h13; rewrite h13 in h3.
(* (max (length Z1) (length Z2))=(length Z1) *)
assert (h14 : (le (length Z1) (length Z3))).
 rewrite h3; apply le_n.
assert (h15 : (le (length Z2) (length Z3))).
 rewrite h3; rewrite <- h13; apply Nat.le_max_r.
exact (schroer'_tranzzz 
       (schroer_change_Z h h14 h8 h10 h11 h5) 
        (schroer_change_Z h0 h15 h9 h11 h12 h5)).
(* (max (length Z1) (length Z2))=(length Z2) *)
assert (h14 : (le (length Z1) (length Z3))).
 rewrite h3; rewrite <- h13; apply Nat.le_max_l.
assert (h15 : (le (length Z2) (length Z3))).
 rewrite h3; apply le_n.
exact (schroer'_tranzzz 
       (schroer_change_Z h h14 h8 h10 h11 h5) 
        (schroer_change_Z h0 h15 h9 h11 h12 h5)).
Qed.

Lemma schroer_trans : 
 forall (M N : Adbmal), 
  (schroer M N)
   ->forall (P : Adbmal), 
      (schroer N P)
       ->(schroer M P).
Proof.
intros M N h; elim h; intros Z1 h0 P h1; elim h1; intros Z2 h2.
exact (schroer'_trans h0 h2).
Qed.

Lemma schroer'_abs_congr : 
 forall (M N : Adbmal) (Z : stack) (x : name), 
  (schroer' M N Z)
   ->(exists z : name, (schroer' (abs x M)(abs x N)(cons z Z))).
Proof.
intros M N Z x h.
elim (inf_many_names (juxt Z (juxt (names M) (names N))));
 intros z h0.
exists z.
assert (h1 : ~(In z Z)).
intro h1; apply h0; apply in_or_juxt; left; exact h1.
assert (h2 : ~(In z (names M))).
intro h2; apply h0; apply in_or_juxt; right; apply in_or_juxt; left;
 exact h2.
assert (h3 : ~(In z (names N))).
intro h3; apply h0; apply in_or_juxt; right; apply in_or_juxt; right;
 exact h3.
apply schroer_rule.
exact h2.
exact h3.
exact h1.
apply schroer'_rename_same.
exact h.
exact h1.
exact h2.
exact h3.
Qed.

Lemma schroer_abs_congr : 
 forall (M N : Adbmal) (x : name), 
  (schroer M N)
   ->(schroer (abs x M)(abs x N)).
Proof.
intros M N x h; elim h; intros Z h0.     
elim (schroer'_abs_congr x h0); intros z h1.
exists (cons z Z); exact h1.
Qed.

Lemma schroer_eos_congr : 
 forall (M N : Adbmal) (x : name), 
  (schroer M N)
   ->(schroer (eos x M) (eos x N)).
Proof.
intros M N x h; elim h; intros Z h0.     
exists Z; apply schroer_eos; exact h0.
Qed.

Lemma schroer'_apl_congr : 
 forall (M M' N : Adbmal) (Z : stack), 
  (schroer' M M' Z)
   ->(exists Z' : stack, (schroer' (ap M N)(ap M' N) Z')).
Proof.
intros M M' N Z1 h.
elim (schroer'_refl N); intros Z2 h0.
exact (schroer_ap_Z1Z2 h h0).
Qed.

Lemma schroer_apl_congr : 
 forall (M M' N : Adbmal), (schroer M M')->(schroer (ap M N)(ap M' N)).
Proof.
intros M M' N h; elim h; intros Z h0.
exact (schroer'_apl_congr N h0).
Qed.

Lemma schroer'_apr_congr : 
 forall (M N N' : Adbmal) (Z : stack), 
  (schroer' N N' Z)
   ->(exists Z' : stack, (schroer' (ap M N)(ap M N') Z')).
intros M N N' Z2 h.
elim (schroer'_refl M); intros Z1 h0.
exact (schroer_ap_Z1Z2 h0 h).
Qed.

Lemma schroer_apr_congr : 
 forall (M N N' : Adbmal), (schroer N N')->(schroer (ap M N)(ap M N')).
Proof.
intros M M' N h; elim h; intros Z h0.
exact (schroer'_apr_congr M h0).
Qed.

Lemma alpha_conv_to_schroer :
 forall (M N : Adbmal), (alpha_conv M N)->(schroer M N).
Proof.
induction 1.
(* alpha_conv_rule *)
elim (schroer'_refl M); intros Z H0.
elim (inf_many_names (cons y (juxt Z (names M)))); intros z H1.
exists (cons z Z).
assert (H2 : ~z=y).
intro H2; apply H1; left; symmetry; exact H2.
assert (H3 : ~(In z Z)).
intro H3; apply H1; right; apply in_or_juxt; left; exact H3.
assert (H4 : ~(In z (names M))).
intro H4; apply H1; right; apply in_or_juxt; right; exact H4.
apply schroer_rule.
exact H4.
apply not_in_renamed_term.
intro H5; apply H2; symmetry; exact H5.
exact H4.
exact H3.
rewrite rename_trans.
apply schroer'_rename_same.
exact H0.
exact H3.
exact H4.
exact H4.
exact H.
exact (fun f => f).
(* alpha_conv_abs *)
exact (schroer_abs_congr x IHalpha_conv).
(* alpha_conv_eos *)
exact (schroer_eos_congr x IHalpha_conv).
(* alpha_conv_apl *)
exact (schroer_apl_congr N IHalpha_conv).
(* alpha_conv_apr *)
exact (schroer_apr_congr N IHalpha_conv).
Qed.

Lemma church_to_schroer :
 forall (M N : Adbmal), (church M N)->(schroer M N).
Proof.
induction 1.
exact (alpha_conv_to_schroer H).
apply schroer_refl.
apply schroer_symm; exact IHRhat.
exact (schroer_trans IHRhat1 IHRhat2).
Qed.

Lemma schroer'_to_church :
 forall (M N : Adbmal) (Z : stack), (schroer' M N Z)->(church M N).
Proof.
induction 1.
(* schroer_rule *)
assert (H3 := (Rhat_ext alpha_conv (abs x M) (abs z (rename M x z Nil))
  (alpha_conv_rule M x z H))). 
 (* why can't position 3 be inferred? *)
assert (H4 := (Rhat_symm (Rhat_ext alpha_conv (abs y N) (abs z (rename N y z Nil))
  (alpha_conv_rule N y z H0)))).
assert (H5 := (church_cxt_congr (cxt_abs z) IHschroer')).
exact (Rhat_trans H3 (Rhat_trans H5 H4)).
(* schroer_var *)
unfold church; apply Rhat_refl. (* why is unfolding necessary? *)
(* schroer_eos *)
apply (church_cxt_congr (cxt_eos x)); exact IHschroer'.
(* schroer_ap *)
assert (H2 := (church_cxt_congr (cxt_apl N) IHschroer'1)).
assert (H3 := (church_cxt_congr (cxt_apr M') IHschroer'2)).
exact (Rhat_trans H2 H3).
Qed.

Lemma schroer_to_church :
 forall (M N : Adbmal), (schroer M N)->(church M N).
Proof.
intros M N h; elim h; intros Z h0.
exact (schroer'_to_church h0).
Qed.

Lemma same_schroer_church : (same_rel schroer church).
Proof.
split; unfold incl_rel; intros M N H.
exact (schroer_to_church H).
exact (church_to_schroer H).
Qed.

Lemma same_schroer_kahrs : (same_rel schroer kahrs).
Proof.
split; unfold incl_rel; intros x y h.
apply (proj2 same_kahrs_church).
apply (proj1 same_schroer_church); exact h.
apply (proj2 same_schroer_church).
apply (proj1 same_kahrs_church); exact h.
Qed.

Lemma rename_bwr1 :
 forall (M N : Adbmal) (x y z : name) (X1 X2 Z Z' : stack), 
  (scb (juxt Z (cons x Z')) M)
   ->~(In z X1)
    ->~(In z (names M))
     ->(rename M x z Z)=(eoss X1 (eos z (eoss X2 (abs y N))))
      -> Z = X1 /\ M = (eoss (juxt Z (cons x X2))(abs y N)).
Proof.
induction M; intros N x y z X1 X2 Z Z' h h0 h1.
(* var n *)
simpl; destruct (in_dec n Z) as [h2|h2].
destruct X1; intro h3; discriminate h3.
destruct (eq_dec n x) as [h3|h3]; destruct X1; intro h4; discriminate h4.
(* abs n M *)
destruct X1; intro h2; discriminate h2.
(* eos n M *)
destruct Z; simpl.
simpl in h; elim (scb_eos_inv h); intros h2 h3.
destruct (eq_dec x n) as [h4|h4]; simpl.
destruct X1; simpl.
intro h5; injection h5; intro h6.
split.
reflexivity.
rewrite h4; rewrite h6; reflexivity.
intro h5; injection h5; intros h6 h7.
elim h0; left; symmetry; exact h7.
elim h4; symmetry; exact h2.
simpl in h; elim (scb_eos_inv h); intros h2 h3.
destruct (eq_dec n n0) as [h4|h4]; simpl.
destruct X1; simpl.
intro h5; injection h5; intros h6 h7.
elim h1; left; exact h7.
intro h5; injection h5; intros h6 h7.
assert (h8 : ~(In z X1)).
intro h8; apply h0; right; exact h8.
assert (h9 : ~(In z (names M))).
intro h9; apply h1; right; exact h9.
elim (IHM N x y z X1 X2 Z Z' h3 h8 h9 h6); intros h10 h11.
split.
rewrite <- h4; rewrite <- h7; rewrite h10; reflexivity.
rewrite h4; rewrite h11; reflexivity.
elim (h4 h2).
(* ap M N *)
simpl; destruct X1; simpl; intro h2; discriminate h2.
Qed.

Lemma rename_bwr2 : 
 forall (M N : Adbmal) (x y z : name) (X Z Z' : stack), 
  (scb (juxt Z (cons x Z')) M)
   ->~(In z X)
    ->~(In z (names M))
     ->(rename M x z Z)=(eoss X (abs y N))
      ->(exists X' : stack, 
         Z=(juxt X X')
          /\ (exists M' : Adbmal,  M=(eoss X (abs y M')) 
                          /\ N = (rename M' x z (cons y X')))).
Proof.
induction M; intros N x y z X Z Z' h h0 h1.
simpl; destruct (in_dec n Z) as [h2|h2]; simpl.
destruct X; intro h3; discriminate h3.
destruct (eq_dec n x) as [h3|h3]; simpl; destruct X; simpl; 
 intro h4; discriminate h4.
destruct X; simpl.
intro h2; injection h2; intros h3 h4.
exists Z; split.
reflexivity.
exists M; split.
rewrite h4; reflexivity.
symmetry; rewrite <- h4; exact h3.
intro h2; discriminate h2.
(* eos n M *)
destruct Z; simpl.
simpl in h.
elim (scb_eos_inv2 h); intros Z0 h2; elim h2; clear h2; intros h2 h3.
injection h2; intros h4 h5.
destruct (eq_dec x n) as [h6|h6]; simpl.
destruct X; simpl.
intro h7; discriminate h7.
intro h7; injection h7; intros h8 h9.
elim h0; left; symmetry; exact h9.
elim (h6 h5).
simpl in h.
elim (scb_eos_inv h); intros h2 h3.
destruct (eq_dec n n0) as [h4|h4]; simpl.
destruct X; simpl.
intro h5; discriminate h5.
intro h5; injection h5; intros h6 h7.
elim (IHM N x y z X Z Z').
intros X' h8; elim h8; clear h8; intros h8 h9.
elim h9; intros M' h10; elim h10; clear h10; intros h10 h11.
exists X'; split.
rewrite <- h4; rewrite <- h7; rewrite h8; reflexivity.
exists M'; split.
rewrite h10.
rewrite <- h7.
reflexivity.
exact h11.
exact h3.
intro h8; apply h0; right; exact h8.
intro h8; apply h1; right; exact h8.
exact h6.
elim h4; exact h2.
destruct X; simpl; intro h2; discriminate h2.
Qed.

Lemma rename_bwr3 : 
 forall (M P : Adbmal) (x z : name) (Z Z' : stack), 
  (scb (juxt Z (cons x Z')) M)
   ->~(In z (names M))
    ->(adbmal_beta (rename M x z Z) P)
     ->(exists N : Adbmal,  (adbmal_beta M N) /\ P = (rename N x z Z)).
Proof.
induction M; intros P x z Z Z' d1 d2; simpl.
(* var *)
destruct (in_dec n Z) as [h|h]; simpl.
intro h0; inversion h0.
destruct (eq_dec n x) as [h0|h0]; simpl; intro h1; inversion h1.
(* abs *)
intro h; inversion_clear h.
assert (d1' := (scb_abs_inv d1)).
assert (d2' : ~(In z (names M))).
intro h; apply d2; right; exact h.
elim (IHM N x z (cons n Z) Z' d1' d2' H); intros N' h; elim h; clear h; 
 intros h h0.
exists (abs n N'); split.
apply beta_abs; exact h.
simpl; rewrite h0; reflexivity.
(* eos *)
destruct (eq_dec x n) as [h|h]; simpl.
destruct Z.
intro h0; inversion_clear h0.
exists (eos n N); split.
apply beta_eos; assumption.
simpl; destruct (eq_dec x n) as [h0|h0].
reflexivity.
elim (h0 h).
simpl in d1.
assert (h0 := (scb_eos_inv d1)).
elim h0; clear h0; intros h0 d1'.
assert (d2' : ~(In z (names M))).
intro h1; apply d2; right; exact h1.
destruct (eq_dec n n0) as [h1|h1]; simpl.
intro h2; inversion_clear h2.
elim (IHM N x z Z Z' d1' d2' H); intros N' h2; elim h2; clear h2; intros h2 h3.
exists (eos n N'); split.
apply beta_eos; assumption.
rewrite h3; simpl.
destruct (eq_dec n n0) as [h4|h4]; simpl.
reflexivity.
elim h4; exact h1.
elim h1; exact h0.
destruct Z.
intro h0; inversion_clear h0.
exists (eos n N); split.
apply beta_eos; assumption.
simpl; destruct (eq_dec x n) as [h0|h0]; simpl.
elim (h h0).
reflexivity.
assert (h0 := (scb_eos_inv d1)).
elim h0; clear h0; intros h0 d1'.
assert (d2' : ~(In z (names M))).
intro h1; apply d2; right; exact h1.
destruct (eq_dec n n0) as [h1|h1]; simpl.
intro h2; inversion_clear h2.
elim (IHM N x z Z Z' d1' d2' H); intros N' h2; elim h2; clear h2; intros h2 h3.
exists (eos n N'); split.
apply beta_eos; assumption.
rewrite h3; simpl.
destruct (eq_dec n n0) as [h4|h4]; simpl.
reflexivity.
elim h4; exact h1.
elim h1; exact h0.
(* ap *)
intro h; inversion h.
assert (h0 := (scb_ap_inv d1)).
elim h0; clear h0; intros d1a d1b.
assert (h0 : ~(In z (names M1))/\~(In z (names M2))).
split; intro h0; apply d2; simpl.
apply in_or_juxt; left; exact h0.
apply in_or_juxt; right; exact h0.
elim h0; clear h0; intros d2a d2b.
elim (IHM1 M' x z Z Z' d1a d2a H2); intros N1 h0; elim h0; clear h0; 
 intros h0 h1.
exists (ap N1 M2); split.
apply beta_apl; assumption.
rewrite h1; reflexivity.
assert (h0 := (scb_ap_inv d1)).
elim h0; clear h0; intros d1a d1b.
assert (h0 : ~(In z (names M1))/\~(In z (names M2))).
split; intro h0; apply d2; simpl.
apply in_or_juxt; left; exact h0.
apply in_or_juxt; right; exact h0.
elim h0; clear h0; intros d2a d2b.
elim (IHM2 M' x z Z Z' d1b d2b H2); intros N2 h0; elim h0; clear h0; 
 intros h0 h1.
exists (ap M1 N2); split.
apply beta_apr; assumption.
rewrite h1; reflexivity.
(* adbmal_beta rule *)
clear H1 N.
assert (h0 := (scb_ap_inv d1)).
elim h0; clear h0; intros d1a d1b.
assert (h0 : ~(In z (names M1))/\~(In z (names M2))).
split; intro h0; apply d2;simpl.
apply in_or_juxt; left; exact h0.
apply in_or_juxt; right; exact h0.
elim h0; clear h0; intros d2a d2b.
(*!*) destruct (in_dec z X) as [h0|h0].
(* In z X *)
elim (in_split eq_dec z X h0); intros X1 h1; elim h1; clear h1; intros X2 h1;
elim h1; clear h1; intros h1 h2.
assert (h3 : (rename M1 x z Z)=(eoss X1 (eos z (eoss X2 (abs x0 M))))).
rewrite h1 in H0.
rewrite eoss_juxt in H0.
symmetry; exact H0.
elim (rename_bwr1 M x x0 z X1 X2 Z Z' d1a h2 d2a h3); intros h4 h5.
exists (adbmal_subst (juxt Z (cons x X2)) Nil M x0 M2); split.
rewrite h5.
apply beta_rule.
symmetry.
rewrite h1.
rewrite h4.
rewrite h5 in d1a.
rewrite eoss_juxt in d1a.
assert (h6 := (scb_eoss_inv2 (eoss (cons x X2) (abs x0 M)) Z (cons x Z') d1a)).
simpl in h6.
elim (scb_eos_inv h6); intros h7 h8.
elim (scb_eoss_inv X2 (abs x0 M) h8); intros Z0 h9.
elim h9; clear h9 h7; intros h7 h9.
assert (h10 := (scb_abs_inv h9)).
rewrite <- h7 in d1b; rewrite h4 in d1b.
exact (rename_subst_commute_closed Nil X1 X2 Z0 x x0 z h10 d1b).
(* ~In z X *)
assert (h1 : (rename M1 x z Z)=(eoss X (abs x0 M))).
symmetry; assumption.
elim (rename_bwr2 M x x0 z X Z Z' d1a h0 d2a h1); intros X' h2; elim h2; clear h2; 
 intros h2 h3; elim h3; clear h3; intros M' h3; elim h3; clear h3; 
 intros h3 h4.
exists (adbmal_subst X Nil M' x0 M2); split.
rewrite h3; apply beta_rule.
rewrite h4.
rewrite h2.
assert (h5 : ~(In z (names M'))).
intro h5; apply d2a; rewrite h3.
apply in_eoss2.
right.
exact h5.
assert (h6 : ~z=x0).
intro h6; apply d2a; rewrite h3.
apply in_eoss2.
left; symmetry; exact h6.
assert (h7 : ~(In z Nil)).
exact (fun h => h).
rewrite h3 in d1a.
rewrite h2 in d1a.
rewrite juxt_ass in d1a.
assert (h8 := (scb_eoss_inv2 (abs x0 M') X (juxt X' (cons x Z')) d1a)).
assert (h9 := (scb_abs_inv h8)).
rewrite h2 in d1b.
rewrite juxt_ass in d1b.
symmetry.
exact (rename_subst_commute_open Nil X X' Z' x h5 h7 h6 h9 d1b).
Qed.

Lemma rename_beta :
 forall (M N : Adbmal) (x z : name), 
  ~(In z (names M))
  ->(adbmal_beta M N)
   ->forall (X Z : stack), 
      (scb (juxt Z (cons x X)) M)
       ->(adbmal_beta (rename M x z Z)(rename N x z Z)).
Proof.
induction M; intros N x z d h0 X Z h; inversion h0; simpl.
apply beta_abs.
assert (h1 := (scb_abs_inv h)).
assert (h2 : ~(In z (names M))).
intro h2; apply d; right; exact h2.
exact (IHM N0 x z h2 H2 X (cons n Z) h1).
destruct (eq_dec x n) as [h1|h1]; simpl.
destruct Z; simpl.
apply beta_eos; assumption.
simpl in h.
elim (scb_eos_inv h); intros h2 h3.
destruct (eq_dec n n0) as [h4|h4]; simpl.
apply beta_eos.
assert (h5 : ~(In z (names M))).
intro h5; apply d; right; exact h5.
exact (IHM N0 x z h5 H2 X Z h3).
elim (h4 h2).
destruct Z; simpl.
apply beta_eos; assumption.
simpl in h.
elim (scb_eos_inv h); intros h2 h3.
destruct (eq_dec n n0) as [h4|h4]; simpl.
apply beta_eos.
assert (h5 : ~(In z (names M))).
intro h5; apply d; right; exact h5.
exact (IHM N0 x z h5 H2 X Z h3).
elim (h4 h2).
elim (scb_ap_inv h); intros h1 h2.
assert (h3 : ~(In z (names M1))).
intro h3; apply d; simpl; apply in_or_juxt; left; exact h3.
apply beta_apl.
exact (IHM1 M' x z h3 H2 X Z h1).
elim (scb_ap_inv h); intros h1 h2.
assert (h4 : ~(In z (names M2))).
intro h4; apply d; simpl; apply in_or_juxt; right; exact h4.
apply beta_apr.
exact (IHM2 M' x z h4 H2 X Z h2).
elim (scb_ap_inv h); intros h1 h2.
rewrite <- H0 in h1.
elim (scb_eoss_inv X0 (abs x0 M) h1); intros Z' h3; elim h3; clear h3; intros h3 h4.
(*!*) elim (le_or_gt_list X0 Z Z' (cons x X) h3); intro h6.
(* (le_list X Z) *)
elim h6; intros Y h7.
rewrite h7.
rewrite rename_eoss.
simpl.
assert (h8 : ~(In z (names M1))).
intro h8; apply d; simpl; apply in_or_juxt; left; exact h8.
rewrite <- H0 in h8.
assert (h9 : ~(In z (names M))).
intro h9; apply h8; apply in_eoss2; right; exact h9.
assert (h10 : ~z=x0).
intro h10; apply h8; apply in_eoss2; left; symmetry; exact h10.
assert (h11 := (scb_abs_inv h4)).
assert (h12 : ~(In z Nil)).
exact (fun h => h).
rewrite h7 in h2.
rewrite h7 in h3; rewrite juxt_ass in h3.
apply juxt_inj in h3.
rewrite h3 in h11.
rewrite juxt_ass in h2.
assert (rsc := (rename_subst_commute_open Nil X0 Y X x h9 h12 h10 h11 h2)).
simpl in rsc.
(* at last ... *) rewrite rsc.
apply beta_rule.
(* (gt_list X0 Z) *)
elim h6; intros y h7; elim h7.
clear h7 H0 H1 N0 H2 h0 N h4 h3 Z' h6 h.
intros Y h3.
rewrite h3 in h1; rewrite eoss_juxt in h1.
elim (scb_eoss_inv Z (eoss (cons y Y) (abs x0 M)) h1); intros W h4; elim h4; clear h4; intros h4 h5.
apply juxt_inj in h4; rewrite h4 in h5; clear h4.
simpl in h5; elim (scb_eos_inv h5); clear h5; intros h4 h5.
elim (scb_eoss_inv Y (abs x0 M) h5); intros Y' h6; elim h6; clear h6; intros h6 h7.
assert (h8 := (scb_abs_inv h7)).
rewrite h3.
rewrite h4.
pattern Z at 2; rewrite (juxt_nil_end Z).
rewrite eoss_juxt.
rewrite rename_eoss; simpl.
destruct (eq_dec x x) as [h9|h9]; simpl.
rewrite (rename_subst_commute_closed Nil Z Y Y' x x0 z).
replace (eoss Z (eos z (eoss Y (abs x0 M))))
 with (eoss (juxt Z (cons z Y)) (abs x0 M)).
apply beta_rule.
rewrite eoss_juxt; reflexivity.
exact h8.
rewrite h6; exact h2.
elim h9; reflexivity.
Qed.

Lemma schroer_eoss_inv1 : 
 forall (X Z : stack) (M N : Adbmal), 
  (schroer' (eoss X M) N Z)
   ->(exists N' : Adbmal, N=(eoss X N')/\(schroer' M N' Z)).
Proof.
induction X; simpl; intros Z M N h.
exists N; split; auto.
inversion_clear h.
elim (IHX Z M N0 H); intros N' h; elim h; intros h1 h2.
exists N'; split.
rewrite h1; reflexivity.
exact h2.
Qed.

Lemma schroer_eoss : 
 forall (M N : Adbmal) (X Z : stack), 
  (schroer' M N Z)->
   (schroer' (eoss X M)(eoss X N) Z). 
Proof.
induction X; simpl; intros Z h.
exact h.
apply schroer_eos; apply IHX; exact h.
Qed.

Lemma in_rename :
forall (M : Adbmal) (x w z : name) (Y : stack), 
 (In w (names (rename M x z Y)))
 ->~w=z
  ->(In w (names M)).
Proof.
induction M; simpl; intros x w z Y h h0.
destruct (in_dec n Y).
exact h.
destruct (eq_dec n x).
elim h; intro h1.
right; apply h0; symmetry; exact h1.
right; exact h1.
elim h; intro h1.
left; exact h1.
right; exact h1.
elim h; intro h1.
left; exact h1.
right; apply (IHM x w z (cons n Y) h1 h0).
induction Y.
destruct (eq_dec x n).
elim h; intro h1.
elim h0; symmetry; exact h1.
right; exact h1.
exact h.
destruct (eq_dec n a).
elim h; intro h1.
left; exact h1.
right; apply (IHM x w z Y h1 h0).
exact (IHY h).
elim (in_juxt_or h); intro h1.
apply in_or_juxt; left; apply (IHM1 x w z Y h1 h0).
apply in_or_juxt; right; apply (IHM2 x w z Y h1 h0).
Qed.

Lemma schroer_subst_skel_ind :
 forall (s : skel) (M : Adbmal) (h : s=(skeleton M)) (M' N N' : Adbmal) (x y z : name) (X Y Z1 Z2 W : stack), 
  (schroer' N N' Z1)
   ->(schroer' (rename M x z Y)(rename M' y z Y) Z2)
    ->(scb (juxt Y (cons x W)) M)
     ->(scb (juxt Y (cons y W)) M')
      ->~(In z (names M))
       ->~(In z (names M'))
        ->~(In z Z2)
         ->(disjoint Z2 X)
          ->(disjoint Z2 Y)
           ->(disjoint Z2 Z1)
            ->(disjoint Z2 (names M))
             ->(disjoint Z2 (names M'))
              ->(disjoint Z2 (names N))
               ->(disjoint Z2 (names N'))
                ->(exists Z3 : stack,  
                   (schroer' (adbmal_subst X Y M x N)(adbmal_subst X Y M' y N') Z3)).
Proof.
intros s M h M' N N' x y z X Y Z1 Z2 W h0 h1.
assert (q : (skeleton M)=(skeleton M')). 
(* makes it easier to eliminate absurd cases *)
rewrite (rename_skel_eq x z M Y).
rewrite (rename_skel_eq y z M' Y).
exact (schroer_skel h1).
generalize M h M' q Y Z2 h1; clear h1 Z2 Y q M' h M.
induction s; destruct M; intro h.
(* var *)
destruct M'; simpl; 
 intros q Y Z2 h1 b1 b2 d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
exists Z1.
destruct (in_dec n Y).
destruct (in_dec n0 Y).
inversion h1.
apply schroer_var.
destruct (eq_dec n0 y).
inversion h1.
elim d1; left; exact H.
inversion h1.
elim n1; rewrite <- H; exact i.
destruct (eq_dec n x).
destruct (in_dec n0 Y).
inversion h1.
elim d2; left; symmetry; exact H.
destruct (eq_dec n0 y).
destruct (eq_dec y n0).
destruct (eq_dec x n).
apply schroer_eoss; exact h0.
elim n3; symmetry; exact e.
elim n3; symmetry; exact e0.
inversion h1.
elim d2; left; symmetry; exact H.
destruct (in_dec n0 Y).
inversion h1.
elim n1; rewrite H; exact i.
destruct (eq_dec n0 y).
inversion h1.
elim d1; left; exact H.
destruct (eq_dec x n).
elim n2; symmetry; exact e.
destruct (eq_dec y n0).
elim n4; symmetry; exact e.
inversion h1.
apply schroer_eoss; apply schroer_eoss; apply schroer_var.
(* impossible cases *)
discriminate q.
discriminate q.
discriminate q.
discriminate h.
discriminate h.
discriminate h.
discriminate h.
simpl in h; injection h; clear h; intro h.
rename M into t.
destruct M'; simpl; intros q Y Z2 h1.
discriminate q.
(* abs *)
inversion_clear h1.
rename M' into t0.
intros b1 b2 d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
assert (h1 : s=(skeleton (rename t n z0 Nil))).
rewrite h; apply rename_skel_eq.
assert (h2 : ~z0=z).
intro h2; apply d3; left; exact h2.
assert (h3 : ~(In z (names t))).
intro h3; apply d1; right; exact h3.
assert (d1' : ~(In z (names (rename t n z0 Nil)))).
exact (not_in_renamed_term n t h2 h3 Nil).
assert (h4 : ~(In z (names t0))).
intro h4; apply d2; right; exact h4.
assert (d2' : ~(In z (names (rename t0 n0 z0 Nil)))).
exact (not_in_renamed_term n0 t0 h2 h4 Nil).
assert (d3' : ~(In z Z)).
intro h5; apply d3; right; exact h5.
assert (d4' : (disjoint Z X)).
intros w h5; apply (d4 w (or_intror h5)). 
assert (d5' : (disjoint Z (cons z0 Y))).
intros w h5; intro h6; elim h6; intro h7.
apply H1; rewrite h7; exact h5.
exact (d5 w (or_intror h5) h7).
assert (d6' : (disjoint Z Z1)).
intros w h5 h6; apply (d6 w).
right; exact h5.
exact h6.
assert (d8' : (disjoint Z (names (rename t n z0 Nil)))).
intros w h5; intro h6.
apply (d8 w (or_intror h5)); right.
assert (h8 : ~w=z0).
intro h8; apply H1; rewrite <- h8; exact h5.
exact (in_rename t n Nil h6 h8).
assert (d9' : (disjoint Z (names (rename t0 n0 z0 Nil)))).
intros w h5; intro h6.
apply (d9 w (or_intror h5)); right.
assert (h8 : ~w=z0).
intro h8; apply H1; rewrite <- h8; exact h5.
exact (in_rename t0 n0 Nil h6 h8).
assert (d10' : (disjoint Z (names N))).
intros w h5; exact (d10 w (or_intror h5)).
assert (d11' : (disjoint Z (names N'))).
intros w h5; exact (d11 w (or_intror h5)).
assert (h5 : (schroer' 
             (rename (rename t n z0 Nil) x z (cons z0 Y))
             (rename (rename t0 n0 z0 Nil) y z (cons z0 Y)) Z)).
assert (h5 : ~z=n0).
intro h5; apply d2; left; symmetry; exact h5.
assert (h7 : ~(In z0 (names t0))).
intro h7; apply (d9 z0 (or_introl eq_refl));
 right; exact h7.
assert (h8 : ~z=n).
intro h8; apply d1; left; symmetry; exact h8.
assert (h9 : ~(In z (names t))).
intro h9; apply d1; right; exact h9.
assert (h10 : ~(In z0 (names t))).
intro h10; apply (d8 z0 (or_introl eq_refl)); 
 right; exact h10.
replace (cons z0 Y) with (juxt Nil (cons z0 Y)).
rewrite <- (rename_commutes y z0 h5 t0 h4 h7 Nil Y (fun h => h) (fun h => h)).
rewrite <- (rename_commutes x z0 h8 t h9 h10 Nil Y (fun h => h) (fun h => h)).
exact H2.
reflexivity.
assert (b1' := (scb_rename n z0 Nil (juxt Y (cons x W)) (scb_abs_inv b1))).
assert (b2' := (scb_rename n0 z0 Nil (juxt Y (cons y W)) (scb_abs_inv b2))).
assert (q' : (skeleton (rename t n z0 Nil))=(skeleton (rename t0 n0 z0 Nil))).
injection q; intro h6.
rewrite <- (rename_skel_eq n z0 t Nil).
rewrite <- (rename_skel_eq n0 z0 t0 Nil).
exact h6.
elim (IHs (rename t n z0 Nil) h1 (rename t0 n0 z0 Nil) q' (cons z0 Y) Z
           h5 b1' b2' d1' d2' d3' d4' d5' d6' d8' d9' d10' d11');
 intros Z3 h6.
(* we cannot give (cons z0 Z3) as witness for the goal, as then we'd need
  that z0 not in Z3; therefore we introduce Z4: *)
elim (fresh_list (length Z3)
      (juxt (cons z0 Z3)
            (juxt (names (adbmal_subst X (cons z0 Y)(rename t n z0 Nil) x N))
                  (names (adbmal_subst X (cons z0 Y)(rename t0 n0 z0 Nil) y N')))));
 intros Z4 h7; elim h7; clear h7; intros h7 h8; elim h8; clear h8;
 intros h8 h9.
elim (disjoint_juxt_and h8); clear h8; intros h8 h10.
elim (disjoint_juxt_and h10); clear h10; intros h10 h11.
assert (h12 : (le (length Z3) (length Z4))).
rewrite h7; apply le_n.
assert (h13 : (disjoint Z4 Z3)).
intros w h13 h14; apply (h8 w h13); right; exact h14.
assert (h14 := (schroer_change_Z h6 h12 h13 h10 h11 h9)).
exists (cons z0 Z4).
assert (p8 : ~(In z0 (names t))).
intro p8; apply (d8 z0 (or_introl eq_refl)); right; 
 exact p8.
assert (p9 : ~(In z0 (names N))).
intro p9; apply (d10 z0 (or_introl eq_refl)); exact p9.
assert (p10 : ~(In z0 X)).
intro p10; apply (d4 z0 (or_introl eq_refl)); exact p10.
assert (p11 : ~(In z0 (cons n Y))).
intro p11; elim p11; intro p12.
apply (d8 z0 (or_introl eq_refl)); left; exact p12.
exact (d5 z0 (or_introl eq_refl) p12).
assert (p12 : ~(In z0 (names t0))).
intro p12; apply (d9 z0 (or_introl eq_refl)); right; 
 exact p12.
assert (p13 : ~(In z0 (names N'))).
intro p13; apply (d11 z0 (or_introl eq_refl)); exact p13.
assert (p14 : ~(In z0 (cons n0 Y))).
intro p14; elim p14; intro p15.
apply (d9 z0 (or_introl eq_refl)); left; exact p15.
exact (d5 z0 (or_introl eq_refl) p15).
apply schroer_rule.
exact (not_in_subst t N X (cons n Y) x z0 p8 p9 p10 p11).
exact (not_in_subst t0 N' X (cons n0 Y) y z0 p12 p13 p10 p14).
intro h15; apply (h8 z0 h15); left; reflexivity.
replace (cons n Y) with (juxt Nil (cons n Y)).
replace (cons n0 Y) with (juxt Nil (cons n0 Y)).
rewrite (subst_rename_commute_open N X Y Nil W x n z0 p8 (scb_abs_inv b1)).
rewrite (subst_rename_commute_open N' X Y Nil W y n0 z0 p12 (scb_abs_inv b2)).
exact h14.
reflexivity.
reflexivity.
(* absurd cases *)
discriminate q.
discriminate q.
discriminate h.
discriminate h.
discriminate h.
discriminate h.
simpl in h; injection h; clear h; intro h.
destruct M'; intros q Y Z2 h1.
discriminate q.
discriminate q.
(* eos *)
rename M into t.
rename M' into t0.
simpl in q; injection q; intro q'.
destruct Y.
intros b1 b2; simpl in b1, b2.
elim (scb_eos_inv b1); intros e1 b1'.
elim (scb_eos_inv b2); intros e2 b2'.
intros d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
simpl; simpl in h1.
destruct (eq_dec x n).
destruct (eq_dec y n0).
inversion_clear h1.
exists Z2.
apply schroer_eoss.
exact H.
elim n1; symmetry; exact e2.
elim n1; symmetry; exact e1.
intros b1 b2; simpl in b1, b2.
elim (scb_eos_inv b1); intros e1 b1'.
elim (scb_eos_inv b2); intros e2 b2'.
simpl; simpl in h1.
destruct (eq_dec n n1).
destruct (eq_dec n0 n1).
inversion_clear h1.
intros d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
assert (d1' : ~(In z (names t))).
intro h1; apply d1; right; exact h1.
assert (d2' : ~(In z (names t0))).
intro h1; apply d2; right; exact h1.
assert (d5' : (disjoint Z2 Y)).
intros w h1 h2; apply (d5 w h1); right; exact h2.
assert (d8' : (disjoint Z2 (names t))).
intros w h1 h2; apply (d8 w h1); right; exact h2.
assert (d9' : (disjoint Z2 (names t0))).
intros w h1 h2; apply (d9 w h1); right; exact h2.
elim (IHs t h t0 q' Y Z2 H b1' b2' d1' d2' d3 d4 d5' d6 d8' d9' d10 d11); 
 intros Z3 h1.
exists Z3; apply schroer_eos; exact h1.
elim (n2 e2).
elim (n2 e1).
discriminate q.
discriminate h.
discriminate h.
discriminate h.
discriminate h.
simpl in h; injection h; intros h1 h2.
destruct M'; intros q Y Z2 h3.
discriminate q.
discriminate q.
discriminate q.
(* ap *)
rename M1 into t; rename M2 into t0; rename M'1 into t1; rename M'2 into t2.
simpl in q; injection q; intros q1 q2.
intros b1 b2.
elim (scb_ap_inv b1); intros b1a b1b.
elim (scb_ap_inv b2); intros b2a b2b.
simpl.
intros d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
assert (d1a : ~(In z (names t))).
intro h4; apply d1; apply in_or_juxt; left; exact h4.
assert (d1b : ~(In z (names t0))).
intro h4; apply d1; apply in_or_juxt; right; exact h4.
assert (d2a : ~(In z (names t1))).
intro h4; apply d2; apply in_or_juxt; left; exact h4.
assert (d2b : ~(In z (names t2))).
intro h4; apply d2; apply in_or_juxt; right; exact h4.
simpl in h3.
inversion_clear h3.
elim (disjoint_juxt_and d8); intros d8a d8b.
elim (disjoint_juxt_and d9); intros d9a d9b.
elim (IHs1 t h2 t1 q2 Y Z2 H b1a b2a d1a d2a d3 d4 d5 d6 d8a d9a d10 d11);
 intros Z3a h4.
elim (IHs2 t0 h1 t2 q1 Y Z2 H0 b1b b2b d1b d2b d3 d4 d5 d6 d8b d9b d10 d11);
 intros Z3b h5.
elim (schroer_ap_Z1Z2 h4 h5); intros Z3 h6.
exists Z3.
exact h6.
Qed.

Lemma schroer_subst :
 forall (M M' N N' : Adbmal) (x y z : name) (X Y Z1 Z2 W : stack), 
  (schroer' N N' Z1)
   ->(schroer' (rename M x z Y)(rename M' y z Y) Z2)
    ->(scb (juxt Y (cons x W)) M)
     ->(scb (juxt Y (cons y W)) M')
      ->~(In z (names M))
       ->~(In z (names M'))
        ->~(In z Z2)
         ->(disjoint Z2 X)
          ->(disjoint Z2 Y)
           ->(disjoint Z2 Z1)
            ->(disjoint Z2 (names M))
             ->(disjoint Z2 (names M'))
              ->(disjoint Z2 (names N))
               ->(disjoint Z2 (names N'))
                ->(exists Z3 : stack,  
                   (schroer' (adbmal_subst X Y M x N)(adbmal_subst X Y M' y N') Z3)).
Proof.
intro M; exact (schroer_subst_skel_ind (eq_refl (skeleton M))).
Qed.

Lemma commute_schroer_beta_skel_ind : 
 forall (s : skel) (M : Adbmal) (h : s=(skeleton M)) (X : stack), 
  (scb X M)
   ->forall (N : Adbmal), 
      (adbmal_beta M N)
       ->forall (M' : Adbmal) (Z : stack), 
          (schroer' M M' Z)
           ->(exists N' : Adbmal, (adbmal_beta M' N')
              /\(exists Z' : stack, (schroer' N N' Z'))).
Proof.
induction s; destruct M; simpl.
intros h X h0 N h1.
(* var *)
inversion h1.
intro h; discriminate h.
intro h; discriminate h.
intro h; discriminate h.
intro h; discriminate h.
(* abs *)
rename M into t.
intro h; injection h; clear h; intro h.
intros X h0 N h1.
inversion_clear h1.
clear N.
intros M' Z h1.
inversion_clear h1.
assert (h1 : s=(skeleton (rename t n z Nil))).
rewrite h; exact (rename_skel_eq n z t Nil).
assert (h2 := (scb_abs_inv h0)).
assert (h3 := (rename_beta n z H0 H X Nil h2)).
assert (h4 := (scb_rename n z Nil X h2)).
elim (IHs (rename t n z Nil) h1 (juxt Nil (cons z X)) h4
  (rename N0 n z Nil) h3 (rename N y z Nil) Z0 H3);
  intros N' h6; elim h6; clear h6; 
 intros h6 h7; elim h7; clear h7; intros Z' h7.
simpl in h4.
assert (h8 := (scb_schroer H3 h4)).
assert (h9 : ~(In z Nil)).
exact (fun h => h).
assert (h10 := (scb_rename2 N y z Nil X H1 h9 h8)).
simpl in h10.
elim (rename_bwr3 y z Nil X h10 H1 h6); intros P h11; elim h11; clear h11;
intros h11 h12.
rewrite h12 in h7.
exists (abs y P); split.
apply beta_abs.
exact h11.
assert (h13 := (not_in_beta z H0 H)).
assert (h14 := (not_in_beta z H1 h11)).
(* we need a z' not in N0,P,Z' *)
pose (z' := fresh (names (ap N0 (eoss Z' P)))).
assert (h15 := (fresh_not_in (names (ap N0 (eoss Z' P))))).
assert (h16 : ~(In z' (names N0))).
intro h16; apply h15; simpl; apply in_or_juxt; left; exact h16.
assert (h17 : ~(In z' (names P))).
intro h17; apply h15; simpl; apply in_or_juxt; right;
apply in_eoss2; exact h17.
assert (h18 : ~(In z' Z')).
intro h18; apply h15; simpl; apply in_or_juxt; right;
apply in_eoss1; exact h18.
assert (h19 := (rename_diff_schroer' N0 P n y z z' h13 h14 h16 h17 h18 h7)).
exists (cons z' Z').
apply schroer_rule.
exact h16.
exact h17.
exact h18.
exact h19.
intro h; discriminate h.
intro h; discriminate h.
intro h; discriminate h.
intro h; discriminate h.
(* eos *)
rename M into t.
intro h; injection h; clear h; intro h.
intros X h0.
elim (scb_eos_inv2 h0); intros X' h1; elim h1; clear h1; intros h1 h2.
intros N h3.
inversion_clear h3.
intros M' Z h3.
inversion_clear h3.
elim (IHs t h X' h2 N0 H N1 Z H0); intros N' h3; elim h3; clear h3;
intros h3 h4.
exists (eos n N'); split.
apply beta_eos; exact h3.
elim h4; intros Z' h5.
exists Z'; apply schroer_eos; exact h5.
intro h; discriminate h.
intro h; discriminate h.
intro h; discriminate h.
intro h; discriminate h.
(* ap *)
rename M1 into t.
rename M2 into t0.
intro h; injection h; clear h; intros h h0.
intros X h1.
elim (scb_ap_inv h1); clear h1; intros h1 h2.
intros N h3.
inversion h3.
intros P Z h4.
inversion_clear h4.
clear P.
elim (IHs1 t h0 X h1 M' H2 M'0 Z H3); intros P h4; elim h4; clear h4;
 intros h4 h5; elim h5; clear h5; intros Z' h5.
exists (ap P N'); split.
apply beta_apl; exact h4.
exact (schroer_ap_Z1Z2 h5 H4).
intros P Z h4.
inversion_clear h4.
clear P.
elim (IHs2 t0 h X h2 M' H2 N' Z H4); intros P h4; elim h4; clear h4;
 intros h4 h5; elim h5; clear h5; intros Z' h5.
exists (ap M'0 P); split.
apply beta_apr; exact h4.
exact (schroer_ap_Z1Z2 H3 h5).
(* adbmal_beta *)
rewrite <- H0 in h1.
elim (scb_eoss_inv X0 (abs x M) h1); intros X' b; elim b; clear b; intros e b1'.
assert (b1 := (scb_abs_inv b1')); clear b1'.
clear IHs1 IHs2 h h0 h1 h2 e X H2 H1 H0 N0 h3 s1 s2 N t.
intros M' Z h4.
inversion_clear h4; clear M'.
elim (schroer_eoss_inv1 X0 (abs x M) H); intros P h4; elim h4; clear H h4; intros h5 h6.
rewrite h5; clear h5 M'0.
generalize H0; clear H0; inversion_clear h6; clear P.
exists (adbmal_subst X0 Nil N y N'); split.
apply beta_rule.
(* choose Z2 fresh from [X0,M,N,zZ0] *)
elim 
 (fresh_list (length Z0) 
  (juxt (names t0)(juxt (names N')
   (juxt (names M)(juxt (names N)
    (juxt X0 (cons z Z0)))))));
 intros Z2 h; elim h; clear h; intros h h0; elim h0; clear h0; 
 intros h0 h1.
assert (h2 : (le (length Z0) (length Z2))).
rewrite h; apply le_n.
clear h.
elim (disjoint_juxt_and h0); clear h0; intros h3 h0; 
 elim (disjoint_juxt_and h0); clear h0; intros h4 h0;
 elim (disjoint_juxt_and h0); clear h0; intros h5 h0;
 elim (disjoint_juxt_and h0); clear h0; intros h6 h0;
 elim (disjoint_juxt_and h0); clear h0; intros h h0.
assert (h7 : (disjoint Z2 (names (rename M x z Nil)))).
unfold disjoint; intros w h7 h8; apply (h5 w h7).
apply (in_rename M x Nil h8).
intro h9; apply (h0 w h7); left; symmetry; exact h9.
assert (h8 : (disjoint Z2 (names (rename N y z Nil)))).
unfold disjoint; intros w h8 h9; apply (h6 w h8).
apply (in_rename N y Nil h9).
intro h10; apply (h0 w h8); left; symmetry; exact h10.
assert (h9 : (disjoint Z2 Z0)).
unfold disjoint; intros w h9 h10; apply (h0 w h9); right; exact h10.
assert (h10 := (schroer_change_Z H2 h2 h9 h7 h8 h1)).
assert (b2 := (scb_rename2 N y z Nil X' H0 (fun f => f)
  (scb_schroer h10 (scb_rename x z Nil X' b1)))).
simpl in b2.
assert (h11 : ~(In z Z2)).
intro h11; apply (h0 z h11); left; reflexivity.
assert (h12 : (disjoint Z2 Nil)).
intros w h12 h13; elim h13.
exact (schroer_subst x y z X' H3 h10 b1 b2 H H0 h11 h h12 h0 h5 h6 h3 h4).
Qed.

Lemma commute_schroer_beta : 
 forall (M : Adbmal) (X : stack), 
  (scb X M)
   ->forall (N : Adbmal), 
      (adbmal_beta M N)
       ->forall (M' : Adbmal) (Z : stack), 
          (schroer' M M' Z)
           ->(exists N' : Adbmal, (adbmal_beta M' N')
              /\(exists Z' : stack, (schroer' N N' Z'))).
Proof.
intro M; exact (commute_schroer_beta_skel_ind (eq_refl (skeleton M))).
Qed.

Lemma commute_kahrs_beta :
 forall (M N M' : Adbmal) (X : stack), 
  (scb X M)
   ->(adbmal_beta M N)
    ->(kahrs M M')
     ->(exists N' : Adbmal, (adbmal_beta M' N')/\(kahrs N N')).
Proof.
intros M N M' X b h h0.
assert (h1 : (schroer M M')).
apply (proj2 same_schroer_kahrs); exact h0.
elim h1; intros Z h2.
elim (commute_schroer_beta b h h2); intros N' h3; elim h3; clear h3; intros h3 h4.
exists N'; split.
exact h3.
apply (proj1 same_schroer_kahrs); exact h4.
Qed.

Inductive omega : Adbmal->Adbmal->stack->Prop :=
| omega_rule : forall (x : name) (M M' : Adbmal) (X : stack), 
                ~(In x (FV M Nil))->(omega M M' X)->(omega (eos x M) M' (cons x X))
| omega_var  : forall (x : name) (X : stack), (omega (var x)(var x) X)
| omega_abs  : forall (x : name) (M M' : Adbmal) (X : stack), (omega M M'  (cons x X))
                ->(omega (abs x M)(abs x M') X)
| omega_ap   : forall (M1 M2 M1' M2' : Adbmal) (X : stack), 
                (omega M1 M1' X)
                 ->(omega M2 M2' X)
                  ->(omega (ap M1 M2)(ap M1' M2') X).

Lemma omega_rule_gen :
 forall (M N : Adbmal) (X Y : stack), 
  (omega M N Y)
   ->(disjoint X (FV M Nil))
    ->(omega (eoss X M) N (juxt X Y)).
Proof.
induction X; intros Y h h0.
exact h.
simpl; apply omega_rule.
intro h1; elim (h0 a).
left; reflexivity.
rewrite FV_eoss_nil in h1; exact h1.
apply IHX.
exact h.
intros b h1.
apply (h0 b).
right; exact h1.
Qed.

Lemma omega_gen_rule_inv :
 forall (M N : Adbmal) (Z X : stack), 
  (omega (eoss X M) N (juxt X Z))
   ->(disjoint X (FV M Nil))
      /\(omega M N Z).
Proof.
induction X; simpl; intro h.
split; [ exact (fun _ f _ => f) | exact h ].
inversion_clear h.
elim (IHX H0); intros h h0.
split.
intros u h1; elim h1; intro h2.
rewrite <- h2; intro h3; apply H.
rewrite FV_eoss_nil.
exact h3.
exact (h u h2).
exact h0.
Qed.

Lemma omega_abs_inv : 
 forall (x : name) (M N : Adbmal) (X : stack), 
  (omega (abs x M)(abs x N) X)
   ->(omega M N (cons x X)).
Proof.
intros x M N X h; inversion_clear h; assumption.
Qed.

Lemma omega_eoss_inv : 
 forall (M N : Adbmal) (X : stack), 
  (omega M N X)
   ->(exists X1 : stack, (exists M' : Adbmal, (exists X2 : stack, 
      M=(eoss X1 M') 
       /\ X=(juxt X1 X2) 
        /\ (disjoint X1 (FV M' Nil))
         /\ (omega M' N X2)))).
Proof.
induction 1.
rename M' into N.
elim IHomega; intros X1 h; elim h; clear h; intros M' h; elim h;
 clear h; intros X2 h; elim h; clear h; intros h h0; elim h0; clear h0;
 intros h0 h1; elim h1; clear h1; intros h1 h2.
exists (cons x X1); exists M'; exists X2; split.
simpl; rewrite h; reflexivity.
split.
rewrite h0; reflexivity.
rewrite h in H.
rewrite FV_eoss_nil in H.
split.
intros a h3; elim h3; intro h4.
rewrite <- h4; exact H.
exact (h1 a h4).
exact h2.
exists Nil; exists (var x); exists X; split;
[ reflexivity | split; [ reflexivity | split; [ intros a h; elim h | apply omega_var ] ] ].
exists Nil; exists (abs x M); exists X; split; [ reflexivity | split; 
[ reflexivity | split; [ intros a h; elim h | apply omega_abs; assumption ] ] ].
exists Nil; exists (ap M1 M2); exists X; split; [ reflexivity | split; 
[ reflexivity | split; [ intros a h; elim h | apply omega_ap; assumption ] ] ].
Qed.

Lemma omega_eoss_abs_inv : 
 forall (y : name) (M N : Adbmal) (X : stack), 
  (omega M (abs y N) X)
   ->(exists X1 : stack, (exists M' : Adbmal, (exists X2 : stack, 
      M=(eoss X1 (abs y M')) 
       /\ X=(juxt X1 X2) 
        /\ (disjoint X1 (FV (abs y M') Nil))
         /\ (omega M' N (cons y X2))))).
Proof.
induction M; intros N X h; inversion_clear h.
exists Nil; exists M; exists X; split;
[ reflexivity | split; [ reflexivity | split; [ intros a h; elim h | assumption ] ] ].
elim (IHM N X0 H0); intros X1 h; elim h; clear h; intros M' h; elim h;
 clear h; intros X2 h; elim h; clear h; intros h h0; elim h0; clear h0;
 intros h0 h1; elim h1; clear h1; intros h1 h2.
exists (cons n X1); exists M'; exists X2; split.
simpl; rewrite h; reflexivity.
split.
rewrite h0; reflexivity.
rewrite h in H.
rewrite FV_eoss_nil in H.
split.
intros a h3; elim h3; intro h4.
rewrite <- h4; exact H.
exact (h1 a h4).
exact h2.
Qed.

Lemma omega_target_eos_free : forall (M N : Adbmal) (X : stack), (omega M N X)->(eos_free N).
Proof.
induction 1.
exact IHomega.
exact I.
exact IHomega.
split; [ exact IHomega1 | exact IHomega2 ].
Qed.

Lemma omega_scb :
 forall (M N : Adbmal) (X : stack), 
  (omega M N X)
   ->(scb X M).
Proof.
induction 1.
apply scb_eos; exact IHomega.
apply scb_var.
apply scb_abs; exact IHomega.
apply scb_ap; [ exact IHomega1 | exact IHomega2 ].
Qed.

Lemma omega_FV_sub1 :
 forall (M M' : Adbmal) (X Y : stack), (omega M M' (juxt X Y))->(sub (FV M' X)(FV M X)).
Proof.
induction M; intros M' X Y h; inversion h.
apply sub_refl.
exact (IHM M'0 (cons n X) Y H3).
destruct X as [|n0 l].
exact (IHM M' Nil X0 H4).
simpl in H1; injection H1; intros h0 h1.
simpl; destruct (eq_dec n n0) as [h2|h2].
apply sub_trans with (l2 := FV M' l).
exact (FV_sub1 M' Nil (cons n0 Nil) l).
rewrite h0 in H4.
apply (IHM M' l Y H4).
elim (h2 h1).
exact (sub_juxt (IHM1 M1' X Y H1) (IHM2 M2' X Y H4)).
Qed.

Lemma omega_FV_sub2 :
 forall (M M' : Adbmal) (X Y : stack), (omega M M' (juxt X Y))->(sub (FV M X)(FV M' X)).
Proof.
induction M; intros M' X Y h; inversion h.
apply sub_refl.
exact (IHM M'0 (cons n X) Y H3).
destruct X as [|n0 l].
exact (IHM M' Nil X0 H4).
simpl in H1; injection H1; intros h0 h1.
simpl; destruct (eq_dec n n0) as [h2|h2].
apply sub_trans with (l2 := FV M' l).
rewrite h0 in H4.
apply (IHM M' l Y H4).
assert (h3 : (disjoint (cons n0 Nil) (FV M' Nil))).
assert (h3 : ~(In n (FV M' Nil))).
intro h3; apply H3.
exact (omega_FV_sub1 Nil X0 H4 n h3).
intros a h4 h5; elim h4; intro h6.
apply h3; rewrite h1; rewrite h6; exact h5.
exact h6.
assert (h4 : (eos_free M')).
apply (omega_target_eos_free H4).
exact (FV_sub2 M' h4 Nil l h3).
elim (h2 h1).
exact (sub_juxt (IHM1 M1' X Y H1) (IHM2 M2' X Y H4)).
Qed.

Lemma kahrs_weak :
forall (M N : Adbmal) (X1 X2 Y1 Y2 : stack) (x y : name), 
 (eos_free M)
  ->(length X1)=(length Y1)
   ->~(In x (FV M X1))
    ->~(In y (FV N Y1))
     ->(kahrs' M (juxt X1 X2) N (juxt Y1 Y2))
      ->(kahrs' M (juxt X1 (cons x X2)) N (juxt Y1 (cons y Y2))).
Proof.
induction M.
destruct N; intros X1 X2 Y1 Y2 x y h h0 h1 h2 h3.
(* var *)
clear h.
assert (h4 : (length X2)=(length Y2)).
 assert (h5 := (kahrs_list_length h3)).
 rewrite length_juxt in h5; rewrite length_juxt in h5.
 rewrite h0 in h5.
 exact (proj1 (Nat.add_cancel_l _ _ _) h5).
assert (h5 : (length (cons x X2))=(length (cons y Y2))).
simpl; rewrite h4; reflexivity.
generalize h1 h2; clear h1 h2; simpl.
destruct (in_dec n X1) as [h6|h6]; destruct (in_dec n0 Y1) as [h7|h7].
intros h1 h2; clear h1 h2.
exact (kahrs_var_repl_tails X2 Y2 (cons x X2) (cons y Y2) X1 Y1 h6 h0 h5 h3).
elim h7; exact (kahrs_var_in_in X1 X2 Y1 Y2 h3 h0 h6).
elim h6; exact (kahrs_var_in_in Y1 Y2 X1 X2 (kahrs_symm h3) (eq_sym h0) h7).
intros h1 h2.
assert (h8 : ~n=x).
intro h; apply h1; left; exact h.
assert (h9 : ~n0=y).
intro h; apply h2; left; exact h. 
exact (kahrs_var_weak X1 Y1 h0 h6 h7
  (kahrs_var3 h8 h9 (kahrs_var_rm_top X1 X2 Y1 Y2 h0 h6 h3))).
(* diff M N *)
inversion h3.
inversion h3.
inversion h3.
destruct N; intros X1 X2 Y1 Y2 x y h h0 h1 h2 h3.
(* diff M N *) inversion h3.
(* abs *)
rename N into t.
inversion_clear h3.
apply kahrs_abs.
exact (IHM t (cons n X1) X2 (cons n0 Y1) Y2 x y h (f_equal S h0) h1 h2 H).
(* diff M N *)
inversion h3.
inversion h3.
(* eos *)
intros N X1 X2 Y1 Y2 x y h; inversion h.
destruct N; intros X1 X2 Y1 Y2 x y h h0 h1 h2 h3.
(* diff M N *)
inversion h3.
inversion h3.
inversion h3.
(* ap *)
rename N1 into t.
rename N2 into t0.
inversion_clear h3.
elim h; intros h4 h5.
assert (h6 : ~(In x (FV M1 X1))/\~(In x (FV M2 X1))).
 split; intro h6; apply h1; simpl; apply in_or_juxt.
 left; exact h6.
 right; exact h6.
elim h6; clear h6; intros h6 h7.
assert (h8 : ~(In y (FV t Y1))/\~(In y (FV t0 Y1))).
 split; intro h8; apply h2; simpl; apply in_or_juxt.
 left; exact h8.
 right; exact h8.
elim h8; clear h8; intros h8 h9.
apply kahrs_ap.
exact (IHM1 t X1 X2 Y1 Y2 x y h4 h0 h6 h8 H).
exact (IHM2 t0 X1 X2 Y1 Y2 x y h5 h0 h7 h9 H0).
Qed.

Lemma kahrs_omega_commute : 
 forall (M M' N N' : Adbmal) (X X' : stack), 
  (kahrs' M X M' X')
   ->(omega M N X)
    ->(omega M' N' X')
     ->(kahrs' N X N' X').
Proof.
induction M; intros M' N N' X X' h; inversion_clear h.
intro h; inversion_clear h.
intro h; inversion_clear h.
apply kahrs_var1.
intro h; inversion_clear h.
intro h; inversion_clear h.
apply kahrs_var2; assumption.
intro h; inversion_clear h.
intro h; inversion_clear h.
apply kahrs_var3; assumption.
intro h; inversion_clear h.
intro h; inversion_clear h.
apply kahrs_abs.
apply (IHM N0 M'0 M'1 (cons n X) (cons y X') H H0 H1).
intro h; inversion_clear h.
intro h; inversion_clear h.
intro h; inversion_clear h.
assert (h1 : ~(In n (FV N Nil))).
 intro h; apply H0; exact (omega_FV_sub1 Nil X0 H1 n h).
assert (h2 : ~(In y (FV N' Nil))).
 intro h; apply H2; exact (omega_FV_sub1 Nil Y H3 y h).
exact (kahrs_weak Nil X0 Nil Y n y (omega_target_eos_free H1) eq_refl h1 h2
  (IHM N0 N N' X0 Y H H1 H3)).
intro h; inversion h.
elim (H H4).
intro h; inversion_clear h.
intro h; inversion_clear h.
apply kahrs_ap.
exact (IHM1 N1 M1' M1'0 X X' H H1 H3).
exact (IHM2 N2 M2' M2'0 X X' H0 H2 H4).
Qed.

Lemma phone_lemma' : 
 forall (x y : name) (M : Adbmal), 
  (eos_free M)
   ->forall (N : Adbmal), 
      (skeleton M)=(skeleton N) (* for convenience only, follows from third assumpion *)
       ->forall (X1 X2 Y1 Y2 : stack), 
          (kahrs' M (juxt X1 (cons x X2)) N (juxt Y1 (cons y Y2)))
           ->(length X1)=(length Y1)
            ->~(In x (FV M X1))
             ->(kahrs' M (juxt X1 X2) N (juxt Y1 Y2))/\~(In y (FV N Y1)).
Proof.
induction M; intro h.
(* var *) 
clear h; destruct N; intro h.
clear h.
simpl.
intros X1 X2 Y1 Y2 h h0.
destruct (in_dec n X1) as [h1|h1]; destruct (in_dec n0 Y1) as [h2|h2].
intro h3; clear h3.
split.
assert (h3 : (length X2)=(length Y2)).
assert (h3 := (kahrs_list_length h)).
rewrite length_juxt in h3; rewrite length_juxt in h3; rewrite h0 in h3. 
assert (h4 : (length (cons x X2))=(length (cons y Y2))).
rewrite (proj1 (Nat.add_cancel_l _ _ _) h3); reflexivity.
injection h4; exact (fun d => d).
exact (kahrs_var_repl_tails (cons x X2) (cons y Y2) X2 Y2 X1 Y1 h1 h0 h3 h).
exact (fun z => z).
intro h3; clear h3.
elim h2; exact (kahrs_var_in_in X1 (cons x X2) Y1 (cons y Y2) h h0 h1).
elim h1; exact (kahrs_var_in_in Y1 (cons y Y2) X1 (cons x X2)
  (kahrs_symm h) (eq_sym h0) h2).
intro h3.
assert (h6 := (kahrs_var_rm_top X1 (cons x X2) Y1 (cons y Y2) h0 h1 h)).
split.
apply kahrs_var_weak.
exact h0.
exact h1.
exact h2.
apply (kahrs_var_rm_top (cons x Nil) X2 (cons y Nil) Y2 eq_refl).
intro h4; elim h4; intro h5.
apply h3; left; symmetry; exact h5.
exact h5.
exact h6.
generalize h3; clear h3; inversion_clear h6.
intros h3 h4.
apply h3; left; reflexivity.
intros h3 h4.
elim h4.
assumption.
exact (fun f => f).
(* N diff skel *)
discriminate h.
discriminate h.
discriminate h.
(* abs *)
destruct N; intro h0.
(* N diff skel *)
discriminate h0.
rename N into t.
simpl in h0; injection h0; clear h0; intro h0.
intros X1 X2 Y1 Y2 h1 h2 h3.
inversion_clear h1.
elim (IHM h t h0 (cons n X1) X2 (cons n0 Y1) Y2 H (f_equal S h2) h3); intros h4 h5; split.
apply kahrs_abs; exact h4.
exact h5.
(* N diff skel *)
discriminate h0.
discriminate h0.
(* eos *)
elim h.
(* ap *)
simpl in h.
elim h; clear h; intros h h0.
destruct N; intro h1.
(* N diff skel *)
discriminate h1.
discriminate h1.
discriminate h1.
rename N1 into t.
rename N2 into t0.
simpl in h1; injection h1; clear h1; intros h1 h2.
intros X1 X2 Y1 Y2 h3 h4 h5.
assert (h6 : ~(In x (FV M1 X1))/\~(In x (FV M2 X1))).
simpl in h5.
split; intro h6; apply h5; apply in_or_juxt; [ left; exact h6 | right; exact h6 ].
elim h6; clear h6; intros h6 h7.
inversion_clear h3.
elim (IHM1 h t h2 X1 X2 Y1 Y2 H h4 h6); intros h8 h9.
elim (IHM2 h0 t0 h1 X1 X2 Y1 Y2 H0 h4 h7); intros h10 h11.
split.
apply kahrs_ap; assumption.
intro h12; elim (in_juxt_or h12); assumption.
Qed.

Lemma phone_lemma : 
 forall (M N : Adbmal) (X Y : stack) (x y : name), 
  (eos_free M)
   ->~(In x (FV M Nil))
    ->(kahrs' M (cons x X) N (cons y Y))
     ->(kahrs' M X N Y)/\~(In y (FV N Nil)).
Proof.
intros M N X Y x y h h0 h1.
exact (phone_lemma' x y h (kahrs_skel h1) Nil X Nil Y h1 eq_refl h0).
Qed.

Lemma omega_kahrs_postpone :
 forall (M P : Adbmal) (X : stack), 
  (omega M P X)
   ->forall (N : Adbmal) (Y : stack), 
      (kahrs' P X N Y)
       ->(exists Q : Adbmal, (omega Q N Y)/\(kahrs' M X Q Y)).
Proof.
induction 1; intros N Y h.
(* omega_rule *)
assert (h0 : (length Y)=(S(length X))).
symmetry; exact (kahrs_list_length h).
elim (length_S Y h0); intros y h1; elim h1; clear h0 h1; intros Y' h0.
rewrite h0; rewrite h0 in h; clear h0.
assert (h0 := (omega_target_eos_free H0)).
assert (h1 : ~(In x (FV M' Nil))).
intro h1; apply H; exact (omega_FV_sub1 Nil X H0 x h1).
elim (phone_lemma h0 h1 h); intros h2 h3.
elim (IHomega N Y' h2); intros Q h4; elim h4; clear h4; intros h4 h5.
exists (eos y Q); split.
assert (h6 : ~(In y (FV Q Nil))).
intro h6; apply h3.
exact (omega_FV_sub2 Nil Y' h4 y h6).
exact (omega_rule y h6 h4).
apply kahrs_eos2.
exact h5.
(* omega_var *)
inversion_clear h.
exists (var x); split.
apply omega_var.
apply kahrs_var1.
exists (var y); split.
apply omega_var.
apply kahrs_var2.
assumption.
exists (var y); split.
apply omega_var.
apply kahrs_var3; assumption.
(* omega_abs *)
inversion_clear h.
elim (IHomega N0 (cons y Y) H0); intros Q h; elim h; clear h; intros h h0.
exists (abs y Q); split; [ exact (omega_abs h) | exact (kahrs_abs h0) ].
(* omega_ap *)
inversion_clear h.
elim (IHomega1 N1 Y H1); intros Q1 h; elim h; clear h; intros h h0.
elim (IHomega2 N2 Y H2); intros Q2 h1; elim h1; clear h1; intros h1 h2.
exists (ap Q1 Q2); split; [ exact (omega_ap h h1) | exact (kahrs_ap h0 h2) ].
Qed.

Lemma rename_sub :
 forall (x y : name) (M : Adbmal) (Z : stack),  
  (sub (names (rename M x y Z)) (cons y (names M))).
Proof.
induction M; intro Z.
simpl;destruct (in_dec n Z) as [h|h].
intros u h0; right; elim h0; intro h1;
[ left; exact h1 | right; exact h1 ].
destruct (eq_dec n x) as [h0|h0].
intros u h1; elim h1; intro h2;
[ left; exact h2 | right; right; exact h2 ].
intros u h1; right; elim h1; intro h2;
[ left; exact h2 | right; exact h2 ].
intros u h1; elim h1; intro h2.
right; left; exact h2.
elim (IHM (cons n Z) u h2); intro h3.
left; exact h3.
right; right; exact h3.
induction Z.
simpl.
destruct (eq_dec x n) as [h|h].
simpl.
intros u h0; elim h0; intro h1.
left; exact h1.
right; right; exact h1.
intros u h0; right; exact h0.
simpl.
destruct (eq_dec n a) as [h|h].
intros u h0; elim h0; intro h1.
right; left; exact h1.
elim (IHM Z u h1); intro h2.
left; exact h2.
right; right; exact h2.
exact IHZ.
simpl.
intros u h; elim (in_juxt_or h); intro h0.
elim (IHM1 Z u h0); intro h1.
left; exact h1.
right; apply in_or_juxt; left; exact h1.
elim (IHM2 Z u h0); intro h1.
left; exact h1.
right; apply in_or_juxt; right; exact h1.
Qed.

Lemma rename_eos_free_not_in_FV_id :
forall (x y : name) (M : Adbmal) (X : stack), 
 (eos_free M)
  ->~(In x (FV M X))
   ->(rename M x y X) = M.
Proof.
induction M; intros X h; simpl.
destruct (in_dec n X) as [h0|h0].
reflexivity.
intro h1.
destruct (eq_dec n x) as [h2|h2].
elim h1; left; exact h2.
reflexivity.
intro h0.
rewrite (IHM (cons n X) h h0); reflexivity.
elim h.
elim h; intros h1 h2.
intro h0.
elim (dmx (fun d => h0 (in_or_juxt d))); intros h3 h4.
rewrite (IHM1 X h1 h3); rewrite (IHM2 X h2 h4); reflexivity.
Qed.

Lemma kahrs_find_var :
 forall (x : name) (X : stack), 
  (In x X)
   ->forall (Y : stack), 
      (length X)=(length Y)
       ->(all_distinct Y)
        ->(exists y : name, (In y Y) /\ (kahrs' (var x) X (var y) Y)).
Proof.
induction X as [|x' X IHX]; intro c; [ elim c | destruct Y as [|y' Y]; intro h ].
discriminate h.
simpl in h; injection h; clear h; intros h h0.
inversion_clear h0.
destruct (eq_dec x' x) as [h0|h0].
rewrite h0; exists y'; split; [ left; reflexivity | apply kahrs_var2; exact h ].
elim c; intro h1.
elim (h0 h1).
elim (IHX h1 Y h H); intros y h2; elim h2; clear h2; intros h2 h3.
assert (h4 : ~y'=y).
intro h4; apply H0; rewrite h4; exact h2.
exists y; split; [ right; exact h2 | apply kahrs_var3; auto ].
Qed.

End Alpha.
