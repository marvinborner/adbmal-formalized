Require Export list.

Set Implicit Arguments.

(** parameter set of variable names *)

Parameter name : Set.

Definition stack := list name.

(** two axioms about the parameter set [name]: 
   - [eq_dec] (decidable equality for names);
   - [inf_many_names] (infinitely many names).
*)

(** decidable equality for names *)

Axiom eq_dec : forall x y : name, {x = y} + {x <> y}.

(** "{A}+{B}" is syntax for (sumbool A B),
    defined by (initial library):
    [ Inductive sumbool [A,B:Prop] : Set :=
        left  : A -> (sumbool A B)
      | right : B -> (sumbool A B). ]
*)

Axiom inf_many_names : infinitely_many name.

(** (list.v) [infinitely_many = [A:Set](l:(list A)){a:A|~(In a l)}] *)

(** [{x:A|(P x)}] is syntax for [(sig A P)], 
    defined by (initial library):
    [ Inductive sig [A : Set; P : A->Prop] : Set :=
        exist : (x:A)(P x)->(sig A P). ]
*)

(* (fresh l) returns a name not in l *)

Definition fresh := fun l : stack => proj1_sig (inf_many_names l).

Lemma fresh_not_in (l : stack) : ~ In (fresh l) l.
Proof.
  exact (proj2_sig (inf_many_names l)).
Qed.

Definition in_dec := @List.in_dec name eq_dec.

(** Alternatively, one can assume a bijection between
   [name] and [nat] and derive the above axioms as follows;
    see bijection.v for the definition of [Bijection],
    and for proofs [bijnat2inf] and [bijnat2eq_dec].
<<
Reset eq_dec.

Require Export bijection.

Parameter bij  : (Bijection name nat).

Definition eq_dec : (x,y:name){x=y}+{~x=y} := (bijnat2eq_dec bij).

Definition inf_many_names : (infinitely_many name) := (bijnat2inf bij).
>>
*)
