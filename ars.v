Set Implicit Arguments.

Section abstract_rewriting_systems.

Variable A : Set.

Definition incl_rel := [R1,R2:A->A->Prop](x,y:A)(R1 x y)->(R2 x y).
Definition same_rel := [R1,R2:A->A->Prop](incl_rel R1 R2)/\(incl_rel R2 R1).

Lemma incl_trans : 
 (R1,R2,R3:A->A->Prop)(incl_rel R1 R2)->(incl_rel R2 R3)->(incl_rel R1 R3).
Proof [R1,R2,R3;h1;h2;x,y;h3](h2 x y (h1 x y h3)).

(** P is closed under R *)

Definition subj_red := [R:A->A->Prop;P:A->Prop](x,y:A)(R x y)->(P x)->(P y).

Section stars.

Variable R : A->A->Prop.

(** reflexive closure of R *)
Inductive refl_closure : A->A->Prop :=
| refl_closure_refl  : (x:A)(refl_closure x x)
| refl_closure_ext : (x,y:A)(R x y)->(refl_closure x y).

(** reflexive and transitive closure of R *)

Inductive Rstar : A->A->Prop :=
| Rstar_refl  : (x:A)(Rstar x x)
| Rstar_ext   : (x,y:A)(R x y)->(Rstar x y)
| Rstar_trans : (x,y,z:A)(Rstar x y)->(Rstar y z)->(Rstar x z).

(** reflexive and transitive closure of R *)
(** with accumulating nat indicating complexity (here: number of R steps) *)

Inductive Rstar_n : nat->A->A->Prop :=
| Rstar_n_refl  : (x:A)(Rstar_n O x x)
| Rstar_n_ext   : (x,y:A)(R x y)->(Rstar_n (S O) x y)
| Rstar_n_trans : (x,y,z:A;n,m:nat)
                   (Rstar_n n x y)->(Rstar_n m y z)->(Rstar_n (plus n m) x z).

(** equivalence closure of R *)
Inductive Rhat : A->A->Prop :=
| Rhat_ext   : (x,y:A)(R x y)->(Rhat x y)
| Rhat_refl  : (x:A)(Rhat x x)
| Rhat_symm  : (x,y:A)(Rhat x y)->(Rhat y x)
| Rhat_trans : (x,y,z:A)(Rhat x y)->(Rhat y z)->(Rhat x z).

End stars.

Definition transits := [R,R'](incl_rel R R') /\ (incl_rel R' (Rstar R)).

Definition modulo := [R,T;x,y](EX x':A|(EX y':A|(T x' x)/\(R x y)/\(T y y'))).

Section diamonds.

Definition diamond' := 
 [R:A->A->Prop;x:A](y:A)(R x y)->(z:A)(R x z)->(EX u:A|(R y u)/\(R z u)).

Definition diamond_P := [R:A->A->Prop;P:A->Prop](x:A)(P x)->(diamond' R x).

Definition diamond := [R:A->A->Prop](x:A)(diamond' R x).

Definition diamond_n' := 
[R:nat->A->A->Prop;x:A]
 (x1:A;n1:nat)
  (R n1 x x1)->(x2:A;n2:nat)(R n2 x x2)->(EX u:A | (R n2 x1 u)/\(R n1 x2 u)).

Definition diamond_n := [R:nat->A->A->Prop](x:A)(diamond_n' R x).

Definition diamond_n_P := 
 [R:nat->A->A->Prop;P:A->Prop](x:A)(P x)->(diamond_n' R x).

Definition diamond_up_to :=
 [R,T:A->A->Prop]
  (x,y:A)
   (R x y)
    ->(z:A)(R x z)
     ->(EX u:A | (EX u':A | (R y u) /\ (R z u') /\ (T u u'))).

Definition confluent := [R:A->A->Prop](diamond (Rstar R)).

Definition confluent_P := [R:A->A->Prop](diamond_P (Rstar R)).

Definition confluent_n_P := [R:A->A->Prop;P:A->Prop](diamond_n_P (Rstar_n R) P).

Definition confluent_n := [R:A->A->Prop](diamond_n (Rstar_n R)).

Definition confluent_up_to := [R,T](diamond_up_to (Rstar R) T).

End diamonds.

Section starprops.

Variables R,R' : A->A->Prop.

(** idempotence of Rstar *)

Lemma Rstar_idemp : (same_rel (Rstar (Rstar R)) (Rstar R)).
Proof.
Split;
(Intros x y h; Elim h; Clear h x y;
[ Intro x; Apply Rstar_refl | Intros x y h | Intros x y z h h0 h1 h2 ]).
Exact h.
Exact (Rstar_trans h0 h2).
Apply Rstar_ext.
Apply Rstar_ext.
Exact h.
Exact (Rstar_trans h0 h2).
Qed.

(** monotonicity of Rstar *)

Lemma Rstar_mon : (incl_rel R R')->(incl_rel (Rstar R)(Rstar R')).
Proof.
Red.
Intros h x y h0.
Elim h0; Clear h0 x y.
Intro.
Apply Rstar_refl.
Intros x y h0.
Exact (Rstar_ext (h x y h0)).
Intros x y z h0 h1 h2 h3.
Exact (Rstar_trans h1 h3).
Qed.

Lemma same_diamond_P : 
 (P:A->Prop)(same_rel R R')->(diamond_P R P)->(diamond_P R' P).
Proof.
Unfold diamond_P diamond'.
Intros P h; Elim h; Clear h; Intros h h0 diamR x p y d1 z d2.
Elim (diamR x p y (h0 x y d1) z (h0 x z d2)); 
 Intros u h1; Elim h1; Clear h1; Intros c1 c2.
Exists u; Split.
Exact (h y u c1).
Exact (h z u c2).
Qed.

Lemma same_diamond : (same_rel R R')->(diamond R)->(diamond R').
Proof.
Unfold diamond diamond'.
Intro h; Elim h; Clear h; Intros h h0 diamR x y d1 z d2.
Elim (diamR x y (h0 x y d1) z (h0 x z d2)); 
 Intros u h1; Elim h1; Clear h1; Intros c1 c2.
Exists u; Split.
Exact (h y u c1).
Exact (h z u c2).
Qed.

Remark plus_eq_0 : (n,m:nat)(plus n m)=O->n=O/\m=O.
Proof.
Destruct n.
Destruct m.
Split; Reflexivity.
Intros m0 h; Discriminate h.
Intros n0 m h; Discriminate h.
Save.

Remark plus_eq_1 : (n,m:nat)(plus n m)=(S O)->n=(S O)/\m=O\/n=O/\m=(S O).
Proof.
Destruct n; Destruct m; Simpl.
Intro h; Discriminate h.
Right; Split; Auto.
Intro h.
Left.
Injection h.
Rewrite <- (plus_n_O n0).
Intro h0.
Split.
Rewrite h0.
Reflexivity.
Reflexivity.
Intros m0 h; Injection h.
Rewrite <- (plus_n_Sm n0 m0).
Intro h0; Discriminate h0.
Save.

Lemma Rstar_n_refl_inv' : (x,y:A)(n:nat)(Rstar_n R n x y)->n=O->x=y.
Proof.
Intros x y n h.
Elim h; Clear h x y n.
Reflexivity.
Intros x y h h0; Discriminate h0.
Intros x y z n m h h0 h1 h2 h3.
Elim (plus_eq_0 h3); Intros h4 h5.
Rewrite (h0 h4).
Exact (h2 h5).
Qed.

Lemma Rstar_n_refl_inv : (x,y:A)(Rstar_n R O x y)->x=y.
Proof [x,y;h](Rstar_n_refl_inv' h (refl_equal nat O)).

Lemma Rstar_n_ext_inv' : (x,y:A)(n:nat)(Rstar_n R n x y)->n=(S O)->(R x y).
Proof.
Intros x y n h.
Elim h; Clear h x y n.
Intros x h; Discriminate h.
Intros x y h h0; Exact h.
Intros x y z n m h h0 h1 h2 h3.
Elim (plus_eq_1 h3); Intro h4; Elim h4; Clear h3 h4; Intros h3 h4.
Rewrite h4 in h1.
Rewrite <- (Rstar_n_refl_inv h1).
Exact (h0 h3).
Rewrite h3 in h.
Rewrite (Rstar_n_refl_inv h).
Exact (h2 h4).
Qed.

Lemma Rstar_n_ext_inv : (x,y:A)(Rstar_n R (S O) x y)->(R x y).
Proof [x,y;h](Rstar_n_ext_inv' h (refl_equal nat (S O))).

Lemma Rstar2Rstar_n : (x,y:A)(Rstar R x y)->(EX n:nat | (Rstar_n R n x y)).
Proof.
Intros x y h.
Elim h; Clear h x y.
Exists O.
Apply Rstar_n_refl.
Exists (S O).
Apply Rstar_n_ext; Assumption.
Intros x y z h1 ih1 h2 ih2.
Elim ih1; Intros n h3.
Elim ih2; Intros m h4.
Exists (plus n m).
Exact (Rstar_n_trans h3 h4).
Qed.

Lemma Rstar_n2Rstar : (n:nat;x,y:A)(Rstar_n R n x y)->(Rstar R x y).
Proof.
Intros n x y h.
Elim h; Clear h n x y.
Intro; Apply Rstar_refl.
Intros x y h; Exact (Rstar_ext h).
Intros x y z n m h1 ih1 h2 ih2; Exact (Rstar_trans ih1 ih2).
Qed.

Lemma subj_red_Rstar : (P:A->Prop)(subj_red R P)->(subj_red (Rstar R) P).
Proof.
Unfold subj_red.
Intros P h x y h0.
Elim h0; Clear h0 x y.
Exact [x;d]d.
Exact h.
Intros x y z h0 h1 h2 h3 h4.
Exact (h3 (h1 h4)). 
Qed.

Lemma subj_red_Rstar_n : 
 (P:A->Prop)(subj_red R P)->(x,y:A;n:nat)(Rstar_n R n x y)->(P x)->(P y).
Proof [P;h;x,y;n;h0](subj_red_Rstar h (Rstar_n2Rstar h0)).

Lemma diamond_P2confluent_n_P : 
 (P:A->Prop)(subj_red R P)->(diamond_P R P)->(confluent_n_P R P).
Proof.
Unfold confluent_n_P diamond_n_P diamond_n'.
Intros P sr diam x p x1 n1 d1.
Generalize p.
Elim d1; Clear p d1 x x1 n1.
(* G1 *)
Intros x p x2 n2 d2.
Exists x2.
Split.
Exact d2.
Apply Rstar_n_refl.
(* G2 *)
Intros x x1 d1 p x2 n2 d2.
Generalize p x1 d1 .
Elim d2; Clear d1 d2 p x x1 x2.
(* G21 *)
Intros x p x1 d1.
Exists x1.
Split.
Apply Rstar_n_refl.
Apply Rstar_n_ext.
Exact d1.
(* G22 *)
Intros x x2 d2 p x1 d1.
Elim (diam x p x1 d1 x2 d2).
Intros u h.
Elim h; Clear h; Intros c1 c2.
Exists u.
Split.
Exact (Rstar_n_ext c1).
Exact (Rstar_n_ext c2).
(* G23 *)
Intros x x2' x2 n m d1a ih1 d1b ih2 p x1 d1.
Elim (ih1 p x1 d1).
Intros u1 h.
Elim h; Clear h; Intros c1a c2'.
Elim (ih2 (subj_red_Rstar_n sr d1a p) u1 (Rstar_n_ext_inv c2')).
Intros u h; Elim h; Clear h; Intros c1b c2.
Exists u.
Split.
Exact (Rstar_n_trans c1a c1b).
Exact c2.
(* G3 *)
Intros x x1' x1 n1 m1 d1a ih1 d1b ih2 p x2 n2 d2.
Generalize d1a ih1 p.
Case d2; Clear d1a ih1 p d2 x x2 n2.
(* G31 *)
Intros x d1a ih1 p.
Exists x1.
Split.
Apply Rstar_n_refl.
Exact (Rstar_n_trans d1a d1b).
(* G32 *)
Intros x x2 d2 d1a ih1 p.
Elim (ih1 p x2 (S O) (Rstar_n_ext d2)).
Intros u2 h.
Elim h; Clear h; Intros c1' c2a.
Elim (ih2 (subj_red_Rstar_n sr d1a p) u2 (S O) c1'); 
 Intros u h; Elim h; Clear h; Intros c1 c2b.
Exists u.
Split.
Exact c1.
Exact (Rstar_n_trans c2a c2b).
(* G33 *)
Intros x x2' x2 n2 m2 d2a d2b d1a ih1 p.
Elim (ih1 p x2 (plus n2 m2) (Rstar_n_trans d2a d2b)).
Intros u2 h.
Elim h; Clear h; Intros c1' c2a.
Elim (ih2 (subj_red_Rstar_n sr d1a p) u2 (plus n2 m2) c1').
Intros u h.
Elim h; Clear h; Intros c1 c2b.
Exists u.
Split.
Exact c1.
Exact (Rstar_n_trans c2a c2b).
Qed.

Definition my_true := False->False.

Lemma subj_red_true : (subj_red R [_]my_true).
Proof [x,y;_;h]h.

Lemma diamond2confluent_n : (diamond R)->(confluent_n R).
Proof [h;x](diamond_P2confluent_n_P subj_red_true [y;_](h y) [b]b).

Lemma confluent_n_P2confluent_P : 
 (P:A->Prop)(confluent_n_P R P)->(confluent_P R P).
Proof.
Unfold confluent_n_P confluent_P diamond_n_P diamond_n' diamond_P diamond'.
Intros P h x p y h0 z h1.
Elim (Rstar2Rstar_n h0); Intros n h2.
Elim (Rstar2Rstar_n h1); Intros m h3.
Elim (h x p y n h2 z m h3); Intros u h4; Elim h4; Clear h4; Intros h4 h5.
Exists u; Split.
Exact (Rstar_n2Rstar h4).
Exact (Rstar_n2Rstar h5).
Qed.

Lemma confluent_n2confluent : (confluent_n R)->(confluent R).
Proof.(*[h;x](confluent_n_P2confluent_P [y;_](h y) [b]b) *)
Unfold confluent diamond.
Intros h x.
Cut (confluent_n_P R [_]my_true); 
 [ Exact [h0](confluent_n_P2confluent_P h0 [b]b) | Exact [y;_](h y) ].
Qed.

Lemma diamond2confluent : (diamond R)->(confluent R).
Proof [h](confluent_n2confluent (diamond2confluent_n h)).

Lemma diamond_P2confluent_P : 
 (P:A->Prop)(subj_red R P)->(diamond_P R P)->(confluent_P R P).
Proof [P;h;h0](confluent_n_P2confluent_P (diamond_P2confluent_n_P h h0)).

Lemma transits_R_refl_closureR: (transits R (refl_closure R)).
Proof.
Split; Intros x y h.
Exact (refl_closure_ext h).
NewDestruct h.
Apply Rstar_refl.
Apply Rstar_ext; Assumption.
Qed.

End starprops.

Lemma transits_diamond_confluent : 
 (R,R':A->A->Prop)
  (transits R R') 
   ->(diamond R')
    ->(confluent R).
Proof.
Intros R R' h; Elim h; Clear h; Intros h h0.
Assert h1 := (Rstar_mon h).
Assert h2 : (incl_rel (Rstar R') (Rstar R)).
Apply incl_trans with R2:=(Rstar (Rstar R)).
Exact (Rstar_mon h0).
Exact (proj1 ?? (Rstar_idemp R)).
Assert h3 : (same_rel (Rstar R') (Rstar R)).
Split; Assumption.
Intro h4.
Assert h5 := (diamond2confluent h4).
Exact (same_diamond h3 h5).
Qed.

Lemma transits_diamond_P_confluent_P : 
 (R,R':A->A->Prop;P:A->Prop)
  (subj_red R' P)
   ->(transits R R') 
    ->(diamond_P R' P)
     ->(confluent_P R P).
Proof.
Intros R R' P sr h; Elim h; Clear h; Intros h h0.
Assert h1 := (Rstar_mon h).
Assert h2 : (incl_rel (Rstar R') (Rstar R)).
Apply incl_trans with R2:=(Rstar (Rstar R)).
Exact (Rstar_mon h0).
Exact (proj1 ?? (Rstar_idemp R)).
Assert h3 : (same_rel (Rstar R') (Rstar R)).
Split; Assumption.
Intro h4.
Assert h5 := (diamond_P2confluent_P sr h4).
Exact (same_diamond_P h3 h5).
Qed.


Section Hindley_Rosen.

Inductive empty : Set :=.

Fixpoint finite [n:nat] : Set :=
Cases n of
| O     => empty
|(S n') => unit + (finite n')
end.

Variable n : nat.

Local N := (finite n).

Variable R : N->A->A->Prop.

Definition union := [x,y](EX i:N | (R i x y)).

Definition commute :=
 [i,j:N]
  (x,y,z:A)
   (R i x y)
   ->(R j x z)
    ->(EX u:A | (R j y u) /\ (R i z u)).

Lemma hindley_rosen : ((i,j:N)(commute i j))->(diamond union).
Proof.
Intros h x y h0 z h1.
Elim h0; Clear h0; Intros i h0.
Elim h1; Clear h1; Intros j h1.
Elim (h i j x y z h0 h1); Intros u h2; Elim h2; Clear h2; Intros h2 h3.
Exists u; Split; [ Exists j; Exact h2 | Exists i; Exact h3 ].
Qed.

Definition commute' :=
 [i,j:N]
  (x,y,z:A)
   (R i x y)
   ->(R j x z)
    ->(EX k:N |(EX l:N |(EX u:A | (R k y u) /\ (R l z u)))).

Lemma hindley_rosen' : ((i,j:N)(commute' i j))->(diamond union).
Proof.
Intros h x y h0 z h1.
Elim h0; Clear h0; Intros i h0.
Elim h1; Clear h1; Intros j h1.
Elim (h i j x y z h0 h1); Intros k h2; Elim h2; Clear h2; Intros l h2; 
 Elim h2; Clear h2; Intros u h2; Elim h2; Clear h2; Intros h2 h3.
Exists u; Split; [ Exists k; Exact h2 | Exists l; Exact h3 ].
Qed.

End Hindley_Rosen.

End abstract_rewriting_systems.
