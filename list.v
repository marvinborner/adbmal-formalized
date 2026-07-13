From Stdlib Require Export Lists.List Arith.Arith.

Notation Nil := (@nil _).

Set Implicit Arguments.

Section lists.

Variable A : Set.

(** list concatenation, [app] renamed to [juxt] to avoid confusion with 
[ap], (apply) constructor of terms *)

Definition juxt : list A -> list A -> list A := @app A.

Lemma juxt_ass (l m n : list A) :
  juxt (juxt l m) n = juxt l (juxt m n).
Proof.
  induction l as [|a l IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma juxt_nil_end (l : list A) : l = juxt l (@nil A).
Proof.
  symmetry; apply app_nil_r.
Qed.

Lemma in_or_juxt (l m : list A) (a : A) :
  In a l \/ In a m -> In a (juxt l m).
Proof.
  apply in_or_app.
Qed.

Lemma in_juxt_or (l m : list A) (a : A) :
  In a (juxt l m) -> In a l \/ In a m.
Proof.
  apply in_app_or.
Qed.

Lemma in_split : 
 (forall x y : A, {x = y} + {x <> y})
  -> forall (x : A) (X : list A),
     In x X
      -> exists X1 : list A,
         exists X2 : list A,
          X = juxt X1 (cons x X2)
          /\ ~ In x X1.
Proof.
  intros eq_dec x X.
  induction X as [|a X IH]; simpl.
  - contradiction.
  - intros H.
    destruct (eq_dec a x) as [Hax|Hax].
    + subst a.
      exists Nil, X; split; simpl; auto.
    + destruct H as [Heq|Hin].
      * contradiction.
      * destruct (IH Hin) as [X1 [X2 [HX Hnot]]].
        exists (a :: X1), X2; split.
        -- simpl; now rewrite HX.
        -- simpl; intros [Hhead|Htail].
           ++ apply Hax; exact Hhead.
           ++ apply Hnot; exact Htail.
Qed.

Inductive all_distinct : list A -> Prop :=
| all_distinct_nil  : all_distinct Nil
| all_distinct_cons : forall (a : A) (l : list A),
                       all_distinct l -> ~ In a l -> all_distinct (cons a l).

Definition disjoint := 
 fun l m : list A => forall a : A, In a l -> ~ In a m.

(** ofcourse ... *)
Lemma disjoint_symm (l m : list A) : disjoint l m -> disjoint m l.
Proof.
  unfold disjoint.
  intros H a Ha Hcontra.
  exact (H a Hcontra Ha).
Qed.

Lemma disjoint_juxt_and : 
 forall l l1 l2 : list A,
  disjoint l (juxt l1 l2)
   -> disjoint l l1 /\ disjoint l l2.
Proof.
  unfold disjoint.
  intros l l1 l2 H; split; intros a Ha Hcontra; apply (H a Ha).
  - apply in_or_juxt; now left.
  - apply in_or_juxt; now right.
Qed.

Lemma disjoint_and_juxt : 
 forall l l1 l2 : list A,
  disjoint l l1 /\ disjoint l l2
   -> disjoint l (juxt l1 l2).
Proof.
  unfold disjoint.
  intros l l1 l2 [H1 H2] a Ha Hcontra.
  destruct (in_juxt_or l1 l2 a Hcontra) as [Hin|Hin].
  - exact (H1 a Ha Hin).
  - exact (H2 a Ha Hin).
Qed.

Lemma all_distinct_juxt : 
 forall l m : list A,
  all_distinct (juxt l m) -> all_distinct l /\ all_distinct m.
Proof.
  induction l as [|a l IH]; intros m H; simpl in H.
  - split; [constructor|exact H].
  - inversion H as [|? ? Htail Hnot]; subst.
    destruct (IH m Htail) as [Hl Hm].
    split.
    + constructor.
      * exact Hl.
      * intros Hin; apply Hnot; apply in_or_juxt; now left.
    + exact Hm.
Qed.

Lemma juxt_inj (l m n : list A) : juxt l m = juxt l n -> m = n.
Proof.
  induction l as [|a l IH]; simpl; intros H.
  - exact H.
  - injection H as H; now apply IH.
Qed.

Fixpoint snoc (a : A) (l : list A) : list A :=
  match l with
  | nil       => cons a Nil
  | cons b t  => cons b (snoc a t)
  end.

Lemma snoc_not_nil (a : A) (l : list A) (p : Prop) :
  Nil = snoc a l -> p.
Proof.
  destruct l; discriminate.
Qed.

Lemma length_snoc (a : A) (l : list A) :
  length (snoc a l) = S (length l).
Proof.
  induction l as [|b t IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma snoc_juxt (a : A) (l m : list A) :
  snoc a (juxt l m) = juxt l (snoc a m).
Proof.
  induction l as [|b l IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma juxt_snoc (a : A) (l m : list A) :
  juxt l (cons a m) = juxt (snoc a l) m.
Proof.
  induction l as [|b l IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma length_juxt : 
 forall l m : list A,
  length (juxt l m) = length l + length m.
Proof.
  induction l as [|a l IH]; simpl; intros m.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma length_S : 
 forall (l : list A) (n : nat),
  length l = S n
   -> exists a : A, exists l' : list A, l = cons a l'.
Proof.
  destruct l as [|a l]; intros n H.
  - discriminate H.
  - exists a, l; reflexivity.
Qed.

Lemma in_juxt1 (l m : list A) (a : A) :
  In a l -> In a (juxt l m).
Proof.
  intros H; apply in_or_juxt; now left.
Qed.

Lemma in_juxt2 (l m : list A) (a : A) :
  In a m -> In a (juxt l m).
Proof.
  intros H; apply in_or_juxt; now right.
Qed.

Lemma in_juxt_inv (l m : list A) (a : A) :
  In a (juxt l m) -> In a l \/ In a m.
Proof.
  apply in_juxt_or.
Qed.

Definition le_list : list A -> list A -> Prop :=
 fun C D => exists E, D = juxt C E.

Definition gt_list : list A -> list A -> Prop :=
 fun C D => exists x, exists E, C = juxt D (cons x E).

(* if XY=X'Z, then either X<=X' (i.e. X'=XW for some W)
   or X>X' (i.e. X=X'wW for some w,W) *)

Lemma le_or_gt_list :
 forall X X' Y Z : list A,
  juxt X Y = juxt X' Z
   -> le_list X X' \/ gt_list X X'.
Proof.
  induction X as [|x X IH]; intros X' Y Z H; simpl in H.
(* nil *)
  - left; exists X'; reflexivity.
(* cons x X *)
  - destruct X' as [|x' X']; simpl in H.
    + right; exists x, X; reflexivity.
    + injection H as Hxx Htail; subst x'.
      destruct (IH X' Y Z Htail) as [Hle|Hgt].
      * destruct Hle as [W HW].
        left; exists W; simpl; now rewrite HW.
      * destruct Hgt as [w [W HW]].
        right; exists w, W; simpl; now rewrite HW.
Qed.

Lemma juxt_nil : forall X Y : list A, juxt X Y = Nil -> X = Nil /\ Y = Nil.
Proof.
  destruct X as [|a X]; simpl; intros Y H.
  - split; [reflexivity|exact H].
  - discriminate H.
Qed.

Lemma le_or_gt_list_cor :
 forall (X Z Z' : list A) (x : A),
  juxt X Z' = snoc x Z
  -> le_list X Z \/ X = snoc x Z.
Proof.
  intros X Z; revert X.
  induction Z as [|z Z IH]; intros X Z' x H.
  - destruct X as [|a X].
    + left; exists Nil; reflexivity.
    + simpl in H; injection H as Hax Hnil; subst a.
      destruct (juxt_nil X Z' Hnil) as [HX _]; subst X.
      right; reflexivity.
  - destruct X as [|a X].
    + left; exists (z :: Z); reflexivity.
    + simpl in H; injection H as Haz Htail; subst a.
      destruct (IH X Z' x Htail) as [Hle|Heq].
      * destruct Hle as [E HE].
        left; exists E; simpl; now rewrite HE.
      * right; simpl; now rewrite Heq.
Qed.

Lemma juxt_inj1 (l m n : list A) : juxt l m = juxt l n -> m = n.
Proof.
  apply juxt_inj.
Qed.

Lemma juxtlml (l m : list A) : juxt l m = l -> m = Nil.
Proof.
  induction l as [|a l IH]; simpl; intros H.
  - exact H.
  - injection H as H; now apply IH.
Qed.

Definition infinitely_many := forall l : list A, {a : A | ~ In a l}.

Fixpoint maxlist (l : list nat) : nat :=
  match l with
  | nil       => O (* default *)
  | cons n t  => max n (maxlist t)
  end.

Lemma gt_all_not_in : 
 forall (l : list nat) (n : nat),
  (forall m : nat, In m l -> m < n) -> ~ In n l.
Proof.
  intros l n H Hin.
  exact (Nat.lt_irrefl n (H n Hin)).
Qed.

Lemma le_n_max_n_m (n m : nat) : n <= max n m.
Proof.
  apply Nat.le_max_l.
Qed.

Lemma max_symm (n m : nat) : max n m = max m n.
Proof.
  apply Nat.max_comm.
Qed.

Lemma in_le_max : forall (l : list nat) (m : nat),
  In m l -> m <= maxlist l.
Proof.
  induction l as [|a l IH]; simpl; intros m H.
  - contradiction.
  - destruct H as [H|H].
    + subst a; apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * exact (IH m H).
      * apply Nat.le_max_r.
Qed.

Lemma le_S_S (n m : nat) : n <= m -> S n <= S m.
Proof.
  apply Nat.succ_le_mono.
Qed.

Lemma succ_max_not_in (l : list nat) : ~ In (S (maxlist l)) l.
Proof.
  intros Hin.
  apply (Nat.nle_succ_diag_l (maxlist l)).
  exact (in_le_max l (S (maxlist l)) Hin).
Qed.

Definition sub := fun l m : list A => forall x : A, In x l -> In x m.

Lemma sub_nil (l : list A) : sub Nil l.
Proof.
  intros x H; contradiction.
Qed.

Lemma sub_refl (l : list A) : sub l l.
Proof.
  intros x H; exact H.
Qed.

Lemma sub_trans (l1 l2 l3 : list A) :
  sub l1 l2 -> sub l2 l3 -> sub l1 l3.
Proof.
  intros H12 H23 x Hx; exact (H23 x (H12 x Hx)).
Qed.

Lemma sub_juxt : 
 forall l l' m m' : list A,
  sub l l' -> sub m m' -> sub (juxt l m) (juxt l' m').
Proof.
  unfold sub.
  intros l l' m m' Hl Hm x Hx.
  apply in_or_juxt.
  destruct (in_juxt_or l m x Hx) as [Hx'|Hx'].
  - left; exact (Hl x Hx').
  - right; exact (Hm x Hx').
Qed.

Fixpoint reverse_rec (l : list A) : list A -> list A :=
 fun m =>
  match l with
  | nil        => m
  | cons a l'  => reverse_rec l' (cons a m)
  end.

Definition reverse := fun l : list A => reverse_rec l Nil.

Lemma rev_rec_juxt (l m : list A) :
  reverse_rec l m = juxt (reverse l) m.
Proof.
  revert m; induction l as [|a l IH]; intros m; simpl.
  - reflexivity.
  - change (reverse_rec l (a :: m) =
            juxt (reverse_rec l (a :: Nil)) m).
    rewrite (IH (a :: m)), (IH (a :: Nil)).
    symmetry; apply juxt_ass.
Qed.

Lemma rev_cons_juxt (l m : list A) (a : A) :
 juxt (reverse (cons a l)) m = juxt (reverse l) (cons a m).
Proof.
  unfold reverse; simpl.
  rewrite rev_rec_juxt.
  rewrite juxt_ass.
  reflexivity.
Qed.

Lemma rev_snoc_juxt : 
 forall (a : A) (l m : list A),
  juxt (reverse (snoc a l)) m = juxt (cons a (reverse l)) m.
Proof.
  intros a l; induction l as [|a0 l IH]; intros m; simpl.
  - reflexivity.
  - rewrite rev_cons_juxt.
    rewrite rev_cons_juxt.
    exact (IH (cons a0 m)).
Qed.

Lemma rev_snoc (a : A) (l : list A) :
  reverse (snoc a l) = cons a (reverse l).
Proof.
  specialize (rev_snoc_juxt a l Nil) as H.
  unfold juxt in H.
  now rewrite !app_nil_r in H.
Qed.

Lemma rev_rev_juxt (l m : list A) :
  reverse (juxt (reverse l) m) = juxt (reverse m) l.
Proof.
  revert m; induction l as [|a l IH]; intros m.
  - simpl; symmetry; apply app_nil_r.
  - rewrite rev_cons_juxt.
    rewrite IH.
    rewrite rev_cons_juxt.
    reflexivity.
Qed.

Lemma rev_rev (l : list A) : reverse (reverse l) = l.
Proof.
  specialize (rev_rev_juxt l Nil) as H.
  unfold juxt in H.
  now rewrite app_nil_r in H.
Qed.

End lists.

(** other preliminaries, nothing to do with lists. *)

Lemma nat_eq_dec (n m : nat) : {n = m} + {n <> m}.
Proof.
  apply Nat.eq_dec.
Qed.

Lemma simpl_plus_r (n m k : nat) : m + n = k + n -> m = k.
Proof.
  apply Nat.add_cancel_r.
Qed.

Lemma dmx (A B : Prop) : ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
  intros H; split; intros H0; apply H.
  - now left.
  - now right.
Qed.

Unset Implicit Arguments.
