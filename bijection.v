Require Export list.

Set Implicit Arguments.

Section bijections_sec1.

Variables A B : Set.

Definition injective := fun f : A -> B =>
  forall x y : A, f x = f y -> x = y.

Definition surjective := fun f : A -> B =>
  forall y : B, {x : A | f x = y}.

(*

(* [(sig A P)], or more suggestively [{x:A | (P x)}], denotes the subset 
     of elements of the Set [A] which satisfy the predicate [P]. *)

  Inductive sig [A:Set;P:A->Prop] : Set
      := exist : (x:A)(P x) -> (sig A P).
*)

Inductive bijective : (A -> B) -> Set :=
  is_bijective : forall f : A -> B,
    injective f -> surjective f -> bijective f.

Record Bijection : Set := bijection
  { bij_fun : A -> B;
    bij_lrf : bijective bij_fun
  }.

Variable bij : Bijection.

Lemma bij_is_inj : injective (bij_fun bij).
Proof.
  destruct (bij_lrf bij) as [f Hinj Hsurj].
  exact Hinj.
Defined.

Lemma bij_is_surj : surjective (bij_fun bij).
Proof.
  destruct (bij_lrf bij) as [f Hinj Hsurj].
  exact Hsurj.
Defined.

Section inverses.

Variable f  : A -> B.
Variable f' : B -> A.

Definition left_inverse := forall x : A, f' (f x) = x.
Definition right_inverse := forall y : B, f (f' y) = y.
Definition inverse := left_inverse /\ right_inverse.

Lemma left_inv_inj : left_inverse -> injective f.
Proof.
  unfold left_inverse, injective.
  intros H x y Heq.
  rewrite <- (H x), <- (H y).
  now rewrite Heq.
Defined.

Lemma right_inv_surj : right_inverse -> surjective f.
Proof.
  unfold right_inverse, surjective.
  intros H y.
  exists (f' y).
  apply H.
Defined.

Lemma inv2bij : inverse -> bijective f.
Proof.
  intros [Hl Hr].
  exact (is_bijective (left_inv_inj Hl) (right_inv_surj Hr)).
Defined.

Lemma inv_map (l : list B) (x : A) :
  inverse -> In (f x) l <-> In x (map f' l).
Proof.
  intros [Hl Hr].
  induction l as [|a t IH]; simpl.
  - tauto.
  - split; intros H.
    + destruct H as [H|H].
      * left; subst a; apply Hl.
      * right; apply IH; exact H.
    + destruct H as [H|H].
      * left.
        rewrite <- (Hr a), H.
        reflexivity.
      * right; apply IH; exact H.
Qed.

End inverses.

End bijections_sec1.

Section bijections_sec2.

Variables A B : Set.

Lemma inv_symm (f : A -> B) (f' : B -> A) :
  inverse f f' -> inverse f' f.
Proof.
  intros [Hl Hr].
  split; assumption.
Defined.

Variable bij : Bijection A B.

Definition bij_fun_inv := fun y : B =>
  proj1_sig (bij_is_surj bij y).

Local Definition f : A -> B := bij_fun bij.
Local Definition f' : B -> A := bij_fun_inv.

Lemma bij_fun_right_inverse : right_inverse f f'.
Proof.
  intro y.
  exact (proj2_sig (bij_is_surj bij y)).
Defined.

Lemma bij_fun_left_inverse : left_inverse f f'.
Proof.
  intro x.
  apply (bij_is_inj bij).
  apply bij_fun_right_inverse.
Defined. 

Lemma bij_fun_inverse : inverse f f'.
Proof.
  split.
  - apply bij_fun_left_inverse.
  - apply bij_fun_right_inverse.
Defined.

Lemma bij_inv : Bijection B A.
Proof.
  refine (@bijection B A f' _).
  exact (@inv2bij B A f' f (inv_symm bij_fun_inverse)).
Defined.

(* NB. All proofs above are declared transparent     *)
(* in order to prove the following obvious equality. *)

Lemma inv_eq : bij_fun bij_inv = f'.
Proof.
  reflexivity.
Defined.

End bijections_sec2.

Section bijections_sec3.

Variable A : Set.

(* If there is a bijection between A and nat, *)
(* equality for A is decidable.               *)

Lemma bijnat2eq_dec : Bijection A nat -> forall x y : A, {x = y} + {x <> y}.
Proof.
  intros b x y.
  destruct (nat_eq_dec (bij_fun b x) (bij_fun b y)) as [H|H].
  - left; apply (bij_is_inj b); exact H.
  - right; intros Heq; apply H; now rewrite Heq.
Qed.

(* If there is a bijection between A and nat, *)
(* there are infinitely many A-elements.      *)

(* (list.v) infinitely_many := [A:Set](l:(list A)){a:A|~(In a l)} *)


Lemma bijnat2inf : Bijection A nat -> infinitely_many A.
Proof.
  intros b l.
  set (n := S (maxlist (map (bij_fun b) l))).
  exists (bij_fun (bij_inv b) n).
  intros Hin.
  apply (succ_max_not_in (map (bij_fun b) l)).
  change (In n (map (bij_fun b) l)).
  apply (proj1 (inv_map l n (inv_symm (bij_fun_inverse b)))).
  exact Hin.
Qed.

End bijections_sec3.
