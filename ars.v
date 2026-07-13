Set Implicit Arguments.

Section abstract_rewriting_systems.

Variable A : Set.

Definition incl_rel (R1 R2 : A -> A -> Prop) :=
  forall x y : A, R1 x y -> R2 x y.
Definition same_rel (R1 R2 : A -> A -> Prop) :=
  incl_rel R1 R2 /\ incl_rel R2 R1.

Lemma incl_trans : 
 forall R1 R2 R3 : A -> A -> Prop,
   incl_rel R1 R2 -> incl_rel R2 R3 -> incl_rel R1 R3.
Proof. intros R1 R2 R3 h1 h2 x y h3; exact (h2 x y (h1 x y h3)). Qed.

(** P is closed under R *)

Definition subj_red (R : A -> A -> Prop) (P : A -> Prop) :=
  forall x y : A, R x y -> P x -> P y.

Section stars.

Variable R : A->A->Prop.

(** reflexive closure of R *)
Inductive refl_closure : A->A->Prop :=
| refl_closure_refl  : forall x : A, refl_closure x x
| refl_closure_ext : forall x y : A, R x y -> refl_closure x y.

(** reflexive and transitive closure of R *)

Inductive Rstar : A->A->Prop :=
| Rstar_refl  : forall x : A, Rstar x x
| Rstar_ext   : forall x y : A, R x y -> Rstar x y
| Rstar_trans : forall x y z : A, Rstar x y -> Rstar y z -> Rstar x z.

(** reflexive and transitive closure of R *)
(** with accumulating nat indicating complexity (here: number of R steps) *)

Inductive Rstar_n : nat->A->A->Prop :=
| Rstar_n_refl  : forall x : A, Rstar_n O x x
| Rstar_n_ext   : forall x y : A, R x y -> Rstar_n (S O) x y
| Rstar_n_trans : forall (x y z : A) (n m : nat),
                   Rstar_n n x y -> Rstar_n m y z -> Rstar_n (plus n m) x z.

(** equivalence closure of R *)
Inductive Rhat : A->A->Prop :=
| Rhat_ext   : forall x y : A, R x y -> Rhat x y
| Rhat_refl  : forall x : A, Rhat x x
| Rhat_symm  : forall x y : A, Rhat x y -> Rhat y x
| Rhat_trans : forall x y z : A, Rhat x y -> Rhat y z -> Rhat x z.

End stars.

Definition transits (R R' : A -> A -> Prop) :=
  incl_rel R R' /\ incl_rel R' (Rstar R).

Definition modulo (R T : A -> A -> Prop) (x y : A) :=
  exists x' : A, exists y' : A, T x' x /\ R x y /\ T y y'.

Section diamonds.

Definition diamond' := 
 fun (R : A -> A -> Prop) (x : A) =>
   forall y : A, R x y -> forall z : A, R x z ->
     exists u : A, R y u /\ R z u.

Definition diamond_P (R : A -> A -> Prop) (P : A -> Prop) :=
  forall x : A, P x -> diamond' R x.

Definition diamond (R : A -> A -> Prop) := forall x : A, diamond' R x.

Definition diamond_n' := 
 fun (R : nat -> A -> A -> Prop) (x : A) =>
   forall (x1 : A) (n1 : nat), R n1 x x1 ->
   forall (x2 : A) (n2 : nat), R n2 x x2 ->
     exists u : A, R n2 x1 u /\ R n1 x2 u.

Definition diamond_n (R : nat -> A -> A -> Prop) :=
  forall x : A, diamond_n' R x.

Definition diamond_n_P := 
 fun (R : nat -> A -> A -> Prop) (P : A -> Prop) =>
   forall x : A, P x -> diamond_n' R x.

Definition diamond_up_to :=
 fun (R T : A -> A -> Prop) =>
   forall x y : A, R x y -> forall z : A, R x z ->
     exists u : A, exists u' : A, R y u /\ R z u' /\ T u u'.

Definition confluent (R : A -> A -> Prop) := diamond (Rstar R).

Definition confluent_P (R : A -> A -> Prop) := diamond_P (Rstar R).

Definition confluent_n_P (R : A -> A -> Prop) (P : A -> Prop) :=
  diamond_n_P (Rstar_n R) P.

Definition confluent_n (R : A -> A -> Prop) := diamond_n (Rstar_n R).

Definition confluent_up_to (R T : A -> A -> Prop) :=
  diamond_up_to (Rstar R) T.

End diamonds.

Section starprops.

Variables R R' : A->A->Prop.

(** idempotence of Rstar *)

Lemma Rstar_idemp : (same_rel (Rstar (Rstar R)) (Rstar R)).
Proof.
split;
(intros x y h; elim h; clear h x y;
[ intro x; apply Rstar_refl | intros x y h | intros x y z h h0 h1 h2 ]).
exact h.
exact (Rstar_trans h0 h2).
apply Rstar_ext.
apply Rstar_ext.
exact h.
exact (Rstar_trans h0 h2).
Qed.

(** monotonicity of Rstar *)

Lemma Rstar_mon : (incl_rel R R')->(incl_rel (Rstar R)(Rstar R')).
Proof.
red.
intros h x y h0.
elim h0; clear h0 x y.
intro.
apply Rstar_refl.
intros x y h0.
apply Rstar_ext.
exact (h x y h0).
intros x y z h0 h1 h2 h3.
exact (Rstar_trans h1 h3).
Qed.

Lemma same_diamond_P : 
 forall P : A -> Prop, same_rel R R' -> diamond_P R P -> diamond_P R' P.
Proof.
unfold diamond_P, diamond'.
intros P h; elim h; clear h; intros h h0 diamR x p y d1 z d2.
elim (diamR x p y (h0 x y d1) z (h0 x z d2)); 
 intros u h1; elim h1; clear h1; intros c1 c2.
exists u; split.
exact (h y u c1).
exact (h z u c2).
Qed.

Lemma same_diamond : (same_rel R R')->(diamond R)->(diamond R').
Proof.
unfold diamond, diamond'.
intro h; elim h; clear h; intros h h0 diamR x y d1 z d2.
elim (diamR x y (h0 x y d1) z (h0 x z d2)); 
 intros u h1; elim h1; clear h1; intros c1 c2.
exists u; split.
exact (h y u c1).
exact (h z u c2).
Qed.

Remark plus_eq_0 : forall n m : nat, plus n m = O -> n = O /\ m = O.
Proof.
intros n m h.
destruct n as [|n]; destruct m as [|m]; simpl in h; try discriminate.
split; reflexivity.
Qed.

Remark plus_eq_1 : forall n m : nat,
  plus n m = S O -> n = S O /\ m = O \/ n = O /\ m = S O.
Proof.
intros n m h.
destruct n as [|n].
destruct m as [|m].
discriminate h.
simpl in h.
injection h as h.
subst m.
right; split; reflexivity.
destruct m as [|m].
destruct n as [|n].
left; split; reflexivity.
simpl in h.
discriminate h.
simpl in h.
injection h as h.
rewrite <- plus_n_Sm in h.
discriminate h.
Qed.

Lemma Rstar_n_refl_inv' : forall (x y : A) (n : nat),
  Rstar_n R n x y -> n = O -> x = y.
Proof.
intros x y n h.
elim h; clear h x y n.
reflexivity.
intros x y h h0; discriminate h0.
intros x y z n m h h0 h1 h2 h3.
elim (plus_eq_0 n m h3); intros h4 h5.
rewrite (h0 h4).
exact (h2 h5).
Qed.

Lemma Rstar_n_refl_inv : forall x y : A, Rstar_n R O x y -> x = y.
Proof. intros x y h; exact (Rstar_n_refl_inv' h (eq_refl O)). Qed.

Lemma Rstar_n_ext_inv' : forall (x y : A) (n : nat),
  Rstar_n R n x y -> n = S O -> R x y.
Proof.
intros x y n h.
elim h; clear h x y n.
intros x h; discriminate h.
intros x y h h0; exact h.
intros x y z n m h h0 h1 h2 h3.
elim (plus_eq_1 n m h3); intro h4; elim h4; clear h3 h4; intros h3 h4.
rewrite h4 in h1.
rewrite <- (Rstar_n_refl_inv h1).
exact (h0 h3).
rewrite h3 in h.
rewrite (Rstar_n_refl_inv h).
exact (h2 h4).
Qed.

Lemma Rstar_n_ext_inv : forall x y : A, Rstar_n R (S O) x y -> R x y.
Proof. intros x y h; exact (Rstar_n_ext_inv' h (eq_refl (S O))). Qed.

Lemma Rstar2Rstar_n : forall x y : A, Rstar R x y ->
  exists n : nat, Rstar_n R n x y.
Proof.
intros x y h.
elim h; clear h x y.
exists O.
apply Rstar_n_refl.
exists (S O).
apply Rstar_n_ext; assumption.
intros x y z h1 ih1 h2 ih2.
elim ih1; intros n h3.
elim ih2; intros m h4.
exists (plus n m).
exact (Rstar_n_trans h3 h4).
Qed.

Lemma Rstar_n2Rstar : forall (n : nat) (x y : A),
  Rstar_n R n x y -> Rstar R x y.
Proof.
intros n x y h.
elim h; clear h n x y.
intro; apply Rstar_refl.
intros x y h; apply Rstar_ext; exact h.
intros x y z n m h1 ih1 h2 ih2; exact (Rstar_trans ih1 ih2).
Qed.

Lemma subj_red_Rstar : forall P : A -> Prop,
  subj_red R P -> subj_red (Rstar R) P.
Proof.
unfold subj_red.
intros P h x y h0.
elim h0; clear h0 x y.
exact (fun x d => d).
exact h.
intros x y z h0 h1 h2 h3 h4.
exact (h3 (h1 h4)). 
Qed.

Lemma subj_red_Rstar_n : 
 forall P : A -> Prop, subj_red R P -> forall (x y : A) (n : nat),
   Rstar_n R n x y -> P x -> P y.
Proof. intros P h x y n h0; exact (subj_red_Rstar h (Rstar_n2Rstar h0)). Qed.

Lemma diamond_P2confluent_n_P : 
 forall P : A -> Prop,
   subj_red R P -> diamond_P R P -> confluent_n_P R P.
Proof.
unfold confluent_n_P, diamond_n_P, diamond_n'.
intros P sr diam x p x1 n1 d1.
generalize p.
elim d1; clear p d1 x x1 n1.
(* G1 *)
intros x p x2 n2 d2.
exists x2.
split.
exact d2.
apply Rstar_n_refl.
(* G2 *)
intros x x1 d1 p x2 n2 d2.
generalize p x1 d1 .
elim d2; clear d1 d2 p x x1 x2.
(* G21 *)
intros x p x1 d1.
exists x1.
split.
apply Rstar_n_refl.
apply Rstar_n_ext.
exact d1.
(* G22 *)
intros x x2 d2 p x1 d1.
elim (diam x p x1 d1 x2 d2).
intros u h.
elim h; clear h; intros c1 c2.
exists u.
split.
apply Rstar_n_ext; exact c1.
apply Rstar_n_ext; exact c2.
(* G23 *)
intros x x2' x2 n m d1a ih1 d1b ih2 p x1 d1.
elim (ih1 p x1 d1).
intros u1 h.
elim h; clear h; intros c1a c2'.
elim (ih2 (subj_red_Rstar_n sr d1a p) u1 (Rstar_n_ext_inv c2')).
intros u h; elim h; clear h; intros c1b c2.
exists u.
split.
exact (Rstar_n_trans c1a c1b).
exact c2.
(* G3 *)
intros x x1' x1 n1 m1 d1a ih1 d1b ih2 p x2 n2 d2.
generalize d1a ih1 p.
clear d1a ih1 p.
destruct d2.
(* G31 *)
intros d1a ih1 p.
exists x1.
split.
apply Rstar_n_refl.
exact (Rstar_n_trans d1a d1b).
(* G32 *)
intros d1a ih1 p.
assert (d2 : Rstar_n R (S O) x y).
apply Rstar_n_ext; exact H.
elim (ih1 p y (S O) d2).
intros u2 h.
elim h; clear h; intros c1' c2a.
elim (ih2 (subj_red_Rstar_n sr d1a p) u2 (S O) c1'); 
 intros u h; elim h; clear h; intros c1 c2b.
exists u.
split.
exact c1.
exact (Rstar_n_trans c2a c2b).
(* G33 *)
intros d1a ih1 p.
assert (d2 : Rstar_n R (plus n m) x z).
apply Rstar_n_trans with (y := y); assumption.
elim (ih1 p z (plus n m) d2).
intros u2 h.
elim h; clear h; intros c1' c2a.
elim (ih2 (subj_red_Rstar_n sr d1a p) u2 (plus n m) c1').
intros u h.
elim h; clear h; intros c1 c2b.
exists u.
split.
exact c1.
exact (Rstar_n_trans c2a c2b).
Qed.

Definition my_true := False -> False.

Lemma subj_red_true : subj_red R (fun _ => my_true).
Proof. intros x y _ h; exact h. Qed.

Lemma diamond2confluent_n : (diamond R)->(confluent_n R).
Proof.
  intros h x.
  exact (diamond_P2confluent_n_P subj_red_true (fun y _ => h y)
           (fun b => b)).
Qed.

Lemma confluent_n_P2confluent_P : 
 forall P : A -> Prop, confluent_n_P R P -> confluent_P R P.
Proof.
unfold confluent_n_P, confluent_P, diamond_n_P, diamond_n', diamond_P, diamond'.
intros P h x p y h0 z h1.
elim (Rstar2Rstar_n h0); intros n h2.
elim (Rstar2Rstar_n h1); intros m h3.
elim (h x p y n h2 z m h3); intros u h4; elim h4; clear h4; intros h4 h5.
exists u; split.
exact (Rstar_n2Rstar h4).
exact (Rstar_n2Rstar h5).
Qed.

Lemma confluent_n2confluent : (confluent_n R)->(confluent R).
Proof.
(*[h;x](confluent_n_P2confluent_P [y;_](h y) [b]b) *)
unfold confluent, diamond.
intros h x.
cut (confluent_n_P R (fun _ => my_true)); 
 [ exact (fun h0 => confluent_n_P2confluent_P h0 (fun b => b))
 | exact (fun y _ => h y) ].
Qed.

Lemma diamond2confluent : (diamond R)->(confluent R).
Proof. intros h; exact (confluent_n2confluent (diamond2confluent_n h)). Qed.

Lemma diamond_P2confluent_P : 
 forall P : A -> Prop,
   subj_red R P -> diamond_P R P -> confluent_P R P.
Proof.
  intros P h h0.
  exact (confluent_n_P2confluent_P (diamond_P2confluent_n_P h h0)).
Qed.

Lemma transits_R_refl_closureR: (transits R (refl_closure R)).
Proof.
split; intros x y h.
apply refl_closure_ext; exact h.
destruct h.
apply Rstar_refl.
apply Rstar_ext; assumption.
Qed.

End starprops.

Lemma transits_diamond_confluent : 
 forall R R' : A -> A -> Prop,
  transits R R' 
   ->(diamond R')
    ->(confluent R).
Proof.
intros R R' h; elim h; clear h; intros h h0.
pose proof (Rstar_mon h) as h1.
assert (h2 : incl_rel (Rstar R') (Rstar R)).
apply incl_trans with (R2 := Rstar (Rstar R)).
exact (Rstar_mon h0).
exact (proj1 (Rstar_idemp R)).
assert (h3 : same_rel (Rstar R') (Rstar R)).
split; assumption.
intro h4.
pose proof (diamond2confluent h4) as h5.
exact (same_diamond h3 h5).
Qed.

Lemma transits_diamond_P_confluent_P : 
 forall (R R' : A -> A -> Prop) (P : A -> Prop),
  subj_red R' P
   ->(transits R R') 
    ->(diamond_P R' P)
     ->(confluent_P R P).
Proof.
intros R R' P sr h; elim h; clear h; intros h h0.
pose proof (Rstar_mon h) as h1.
assert (h2 : incl_rel (Rstar R') (Rstar R)).
apply incl_trans with (R2 := Rstar (Rstar R)).
exact (Rstar_mon h0).
exact (proj1 (Rstar_idemp R)).
assert (h3 : same_rel (Rstar R') (Rstar R)).
split; assumption.
intro h4.
pose proof (diamond_P2confluent_P sr h4) as h5.
exact (same_diamond_P h3 h5).
Qed.


Section Hindley_Rosen.

Inductive empty : Set :=.

Fixpoint finite (n : nat) : Set :=
match n with
| O     => empty
|(S n') => unit + (finite n')
end.

Variable n : nat.

Local Definition N := finite n.

Variable R : N->A->A->Prop.

Definition union (x y : A) := exists i : N, R i x y.

Definition commute :=
 fun i j : N =>
   forall x y z : A, R i x y -> R j x z ->
     exists u : A, R j y u /\ R i z u.

Lemma hindley_rosen : (forall i j : N, commute i j) -> diamond union.
Proof.
intros h x y h0 z h1.
elim h0; clear h0; intros i h0.
elim h1; clear h1; intros j h1.
elim (h i j x y z h0 h1); intros u h2; elim h2; clear h2; intros h2 h3.
exists u; split; [ exists j; exact h2 | exists i; exact h3 ].
Qed.

Definition commute' :=
 fun i j : N =>
   forall x y z : A, R i x y -> R j x z ->
     exists k : N, exists l : N, exists u : A, R k y u /\ R l z u.

Lemma hindley_rosen' : (forall i j : N, commute' i j) -> diamond union.
Proof.
intros h x y h0 z h1.
elim h0; clear h0; intros i h0.
elim h1; clear h1; intros j h1.
elim (h i j x y z h0 h1); intros k h2; elim h2; clear h2; intros l h2; 
 elim h2; clear h2; intros u h2; elim h2; clear h2; intros h2 h3.
exists u; split; [ exists k; exact h2 | exists l; exact h3 ].
Qed.

End Hindley_Rosen.

End abstract_rewriting_systems.
