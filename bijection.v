Require Export list.

Set Implicit Arguments.

Section bijections_sec1.

Variables A,B:Set.

Definition injective  := [f:A->B](x,y:A)(f x)=(f y)->x=y.

Definition surjective := [f:A->B](y:B){x:A|(f x)=y}.

(*

(* [(sig A P)], or more suggestively [{x:A | (P x)}], denotes the subset 
     of elements of the Set [A] which satisfy the predicate [P]. *)

  Inductive sig [A:Set;P:A->Prop] : Set
      := exist : (x:A)(P x) -> (sig A P).
*)

Inductive bijective : (A->B)->Set :=
 is_bijective : (f:A->B)(injective f)->(surjective f)->(bijective f).

Record Bijection : Set := bijection
  { bij_fun : A->B;
    bij_lrf : (bijective bij_fun)
  }.

Variable bij : Bijection.

Lemma bij_is_inj : (injective (bij_fun bij)).
Proof.
Elim (bij_lrf bij).
Exact [f;h;_]h.
Defined.

Lemma bij_is_surj : (surjective (bij_fun bij)).
Proof.
Elim (bij_lrf bij).
Exact [f;_;h]h.
Defined.

Section inverses.

Variable f  : A->B.
Variable f' : B->A.

Definition left_inverse  :=  (x:A)(f' (f x))=x.
Definition right_inverse :=  (y:B)(f (f' y))=y.
Definition inverse := left_inverse/\right_inverse.

Lemma left_inv_inj : left_inverse->(injective f).
Proof.
Red; Intros h x y h0.
Rewrite <- (h x).
Rewrite h0.
Apply h.
Defined.

Lemma right_inv_surj : right_inverse->(surjective f).
Proof.
Red; Intros h y.
Rewrite <- (h y).
Exact (exist A [x](f x)=(f (f' y)) (f' y) (refl_equal B (f (f' y)))).
Defined.

Lemma inv2bij : inverse->(bijective f).
Proof.
Intro h.
Elim h; Intros h1 h2.
Exact (is_bijective (left_inv_inj h1) (right_inv_surj h2)).
Defined.

Lemma inv_map : (l:(list B);x:A)inverse->(In (f x) l)<->(In x (map f' l)).
Proof.
Induction l; Simpl.
Intros a i.
Split; Trivial.
Intros a t ih x i.
Elim (ih x i); Intros ih1 ih2.
Elim i; Intros li ri.
Split; Intro h; Elim h; Intro h0.
Left; Rewrite h0; Apply li.
Right; Exact (ih1 h0).
Left; Rewrite <- h0; Symmetry; Apply ri.
Right; Exact (ih2 h0).
Qed.

End inverses.

End bijections_sec1.

Section bijections_sec2.

Variables A,B:Set.

Lemma inv_symm : (f:A->B;f':B->A)(inverse f f')->(inverse f' f).
Proof.
Intros f f' h.
Elim h; Intros h1 h2; Split.
Intro x; Pattern 2 x; Rewrite <- (h2 x); Reflexivity.
Intro y; Pattern 2 y; Rewrite <- (h1 y); Reflexivity.
Defined.

Variable bij : (Bijection A B).

Definition bij_fun_inv := [y:B](proj1_sig ?? (bij_is_surj bij y)).

Local f  := (bij_fun bij).
Local f' := bij_fun_inv.

Lemma bij_fun_right_inverse : (right_inverse f f').
Proof.
Exact [y](proj2_sig ?? (bij_is_surj bij y)).
Defined.

Lemma bij_fun_left_inverse : (left_inverse f f').
Proof.
Intro x.
Apply (bij_is_inj 3!bij).
Fold f.
Apply bij_fun_right_inverse.
Defined. 

Lemma bij_fun_inverse : (inverse f f').
Proof.
Exact (conj ?? bij_fun_left_inverse bij_fun_right_inverse).
Defined.

Lemma bij_inv : (Bijection B A).
Proof.
Exact (bijection 3!f' (inv2bij (inv_symm bij_fun_inverse))).
Defined.

(* NB. All proofs above are declared transparent     *)
(* in order to prove the following obvious equality. *)

Lemma inv_eq : (bij_fun bij_inv)=f'.
Proof.
Exact (refl_equal B->A f').
Defined.

End bijections_sec2.

Section bijections_sec3.

Variable A : Set.

(* If there is a bijection between A and nat, *)
(* equality for A is decidable.               *)

Lemma bijnat2eq_dec : (Bijection A nat)->(x,y:A){x=y}+{~x=y}.
Proof.
Intros b x y.
Case (nat_eq_dec (bij_fun b x)(bij_fun b y)); Intro h.
Left; Exact (bij_is_inj h).
Right; Red; Intro h0; Apply h; Rewrite h0; Reflexivity.
Qed.

(* If there is a bijection between A and nat, *)
(* there are infinitely many A-elements.      *)

(* (list.v) infinitely_many := [A:Set](l:(list A)){a:A|~(In a l)} *)


Lemma bijnat2inf : (Bijection A nat)->(infinitely_many A).
Proof.
Red; Intros b l.
Exists (bij_fun (bij_inv b) (S (maxlist (map (bij_fun b) l)))).
Red; Intro h.
Exact (succ_max_not_in 
       (proj1 ?? (inv_map l  (S (maxlist (map (bij_fun b) l))) (inv_symm (bij_fun_inverse b))) h)).
Qed.

End bijections_sec3.
