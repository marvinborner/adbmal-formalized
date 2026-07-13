Require Export PolyList.
Require Export Max.
Require Export Le.
Require Export Arith.

Syntactic Definition Nil := (nil ?).

Set Implicit Arguments.

Section lists.

Variable A : Set.

(** list concatenation, [app] renamed to [juxt] to avoid confusion with 
[ap], (apply) constructor of terms *)

Definition juxt := (app 1!A).

Lemma juxt_ass : (l,m,n:(list A))(juxt (juxt l m) n)=(juxt l (juxt m n)).
Proof (app_ass 1!A).

Lemma juxt_nil_end : (l:(list A))l=(juxt l (nil A)).
Proof (app_nil_end 1!A).

Lemma in_or_juxt : (l,m:(list A);a:A)(In a l)\/(In a m)->(In a (juxt l m)).
Proof (in_or_app 1!A).

Lemma in_juxt_or :(l,m:(list A);a:A)(In a (juxt l m))->(In a l)\/(In a m).
Proof (in_app_or 1!A).

Lemma in_split : 
 ((x,y:A){x=y}+{~x=y})
  ->(x:A;X:(list A)) 
     (In x X)
      ->(EX X1:(list A)|
         (EX X2:(list A)|
          X=(juxt X1 (cons x X2))
          /\ ~(In x X1))).
Proof.
Intros eq_dec x.
NewInduction X; Simpl; Intro h.
Elim h.
Case (eq_dec a x); Intro h0.
Exists (nil A); Exists X; Split.
Rewrite h0; Reflexivity.
Exact [h]h.

Elim h; Intro h1.
Elim (h0 h1).
Elim (IHX h1); Intros X1 h2; Elim h2; Clear h2; Intros X2 h2; Elim h2;
 Clear h2; Intros h2 h3.
Exists (cons a X1); Exists X2; Split.
Rewrite h2; Reflexivity.
Red; Intro h4; Elim h4; Intro h5.
Exact (h0 h5).
Exact (h3 h5).
Qed.

Inductive all_distinct : (list A)->Prop :=
| all_distinct_nil  : (all_distinct Nil)
| all_distinct_cons : (a:A;l:(list A))
                       (all_distinct l)->~(In a l)->(all_distinct (cons a l)).

Definition disjoint := 
 [l,m:(list A)]((a:A)(In a l)->~(In a m)).

(** ofcourse ... *)
Lemma disjoint_symm : (l,m:(list A))(disjoint l m)->(disjoint m l).
Proof.
Unfold disjoint.
NewInduction l; Simpl.
Intros; Exact [f]f.
Red; Intros m H b H0 H1.
Exact (H b H1 H0).
Qed.

Lemma disjoint_juxt_and : 
 (l,l1,l2:(list A))
  (disjoint l (juxt l1 l2))
   ->(disjoint l l1)/\(disjoint l l2).
Proof.
Unfold disjoint.
NewInduction l; Simpl.
Split; Intros a h; Elim h.
Intros l1 l2 h.
Assert h0 : ~(In a (juxt l1 l2)).
Apply (h a); Left; Reflexivity.
Assert h1 : (a:A)(In a l)->~(In a (juxt l1 l2)).
Intros b h1; Apply (h b (or_intror ?? h1)).
Assert h2 : ~(In a l1).
Red; Intro h2; Apply h0; Apply in_or_juxt; Left; Exact h2.
Assert h3 : ~(In a l2).
Red; Intro h3; Apply h0; Apply in_or_juxt; Right; Exact h3.
Elim (IHl l1 l2 h1); Intros h4 h5.
Split; Intros b h6; Elim h6; Intro h7.
Red; Intro h8; Apply h2; Rewrite h7; Exact h8.
Exact (h4 b h7).
Red; Intro h8; Apply h3; Rewrite h7; Exact h8.
Exact (h5 b h7).
Qed.

Lemma disjoint_and_juxt : 
 (l,l1,l2:(list A))
  (disjoint l l1)/\(disjoint l l2)
   ->(disjoint l (juxt l1 l2)).
Proof.
Unfold disjoint.
NewInduction l; Simpl.
Intros l1 l2 h a h0; Elim h0.
Intros l1 l2 h b h0.
Elim h; Intros h1 h2.
Elim h0; Intro h3.
Red; Intro h4; Elim (in_juxt_or h4); Intro h5.
Exact (h1 b (or_introl ?? h3) h5).
Exact (h2 b (or_introl ?? h3) h5).
Apply IHl.
Split; Intros c h4.
Exact (h1 c (or_intror ?? h4)).
Exact (h2 c (or_intror ?? h4)).
Exact h3.
Qed.

Lemma all_distinct_juxt : 
 (l,m:(list A))(all_distinct (juxt l m))->(all_distinct l)/\(all_distinct m).
Proof.
NewInduction l; Simpl.
Split.
Apply all_distinct_nil.
Assumption.
Intros m h; Inversion_clear h.
Elim (IHl m H); Intros h1 h2.
Split.
Apply all_distinct_cons.
Exact h1.
Red; Intro h3; Apply H0; Apply in_or_juxt; Left; Exact h3.
Exact h2.
Qed.

Lemma juxt_inj : (l,m,n:(list A))(juxt l m)=(juxt l n)->m=n.
Proof.
NewInduction l; Simpl; Intros m n h.
Exact h.
Injection h; Intro h0.
Apply IHl with 1:=h0.
Qed.

Fixpoint snoc [a:A;l:(list A)] : (list A) :=
Cases l of 
| nil       => (cons a Nil)
|(cons b t) => (cons b (snoc a t))
end.

Lemma snoc_not_nil : (a:A;l:(list A);p:Prop)Nil=(snoc a l)->p.
Proof.
Destruct l.
Intros p h; Discriminate h.
Intros b t p h; Discriminate h.
Qed.

Lemma length_snoc : (a:A;l:(list A))(length (snoc a l))=(S(length l)).
Proof.
Induction l; Simpl.
Reflexivity.
Intros b t ih; Rewrite ih; Reflexivity.
Qed.

Lemma snoc_juxt : (a:A;l,m:(list A))(snoc a (juxt l m))=(juxt l (snoc a m)).
Proof.
NewInduction l; Simpl; Intro m.
Reflexivity.
Rewrite IHl; Reflexivity.
Qed.

Lemma juxt_snoc : (a:A;l,m:(list A))(juxt l (cons a m))=(juxt (snoc a l) m).
Proof.
NewInduction l; Simpl; Intro m.
Reflexivity.
Rewrite IHl; Reflexivity.
Qed.

Lemma length_juxt : 
 (l,m:(list A))(length (juxt l m))=(plus (length l)(length m)).
Proof.
NewInduction l; Simpl; Intro m.
Reflexivity.
Rewrite (IHl m); Reflexivity.
Qed.

Lemma length_S : 
 (l:(list A);n:nat)
  (length l)=(S n)
   ->(EX a:A|(EX l':(list A)|l=(cons a l'))).
Proof.
NewDestruct l.
Intros n h; Discriminate h.
Intros n h.
Exists a.
Exists l.
Reflexivity.
Qed.

Lemma in_juxt1 : (l,m:(list A);a:A)(In a l)->(In a (juxt l m)).
Proof.
Intros l m a.
Elim l; Simpl.
Intro h. Elim h.
Intros b l' ih h.
Elim h; Intro h0.
Left.
Exact h0.
Right.
Exact (ih h0).
Qed.

Lemma in_juxt2 : (l,m:(list A);a:A)(In a m)->(In a (juxt l m)).
Proof.
Intros l m a.
Elim l.
Exact [h]h.
Intros b l' ih h.
Right.
Exact (ih h).
Qed.

Lemma in_juxt_inv : (l,m:(list A);a:A)(In a (juxt l m))->(In a l)\/(In a m).
Proof.
Induction l.
Right.
Assumption.
Intros b l' ih m a h.
Elim h; Intro h0.
Left.
Rewrite h0.
Left.
Reflexivity.
Elim (ih m a h0); Intro h1.
Left.
Right.
Exact h1.
Right.
Exact h1.
Qed.

Definition le_list : (list A)->(list A)->Prop :=
 [C,D](EX E | D = (juxt C E)).

Definition gt_list : (list A)->(list A)->Prop :=
 [C,D](EX x | (EX E | C = (juxt D (cons x E)))).

(* if XY=X'Z, then either X<=X' (i.e. X'=XW for some W)
   or X>X' (i.e. X=X'wW for some w,W) *)

Lemma le_or_gt_list :
 (X,X',Y,Z:(list A))
  (juxt X Y)=(juxt X' Z)
   -> (le_list X X') \/ (gt_list X X').
Proof.
Induction X; Clear X; Simpl.
(* nil *)
Intros X' Y Z h.
Left.
Exists X'.
Reflexivity.
(* cons x X *)
Intros x X ih X' Y Z.
Case X'; Simpl; Clear X'.
Intro h.
Right.
Exists x.
Exists X.
Reflexivity.
Intros x' X' h.
Injection h.
Intros e1 e2.
Rewrite e2.
Elim ih with 1:=e1; Intro h0; Elim h0.
Intros W h1.
Left.
Rewrite h1.
Exists W.
Reflexivity.
Intros w h1.
Elim h1.
Intros W h2.
Right.
Rewrite h2.
Exists w.
Exists W.
Reflexivity.
Qed.

Lemma juxt_nil :  (X,Y:(list A))(juxt X Y)=Nil->X=Nil/\Y=Nil.
Proof.
NewInduction X; Simpl; Intros Y h.
Split.
Reflexivity.
Exact h.
Discriminate h.
Qed.

Lemma le_or_gt_list_cor :
(X,Z,Z':(list A);x:A)
(juxt X Z')=(snoc x Z)
->(le_list X Z)\/X=(snoc x Z).
Proof.
Intros X Z Z' x.
Pattern 1 Z; Rewrite juxt_nil_end; Rewrite snoc_juxt.
Intro h; Elim (le_or_gt_list h); Intro h0.
Left; Exact h0.
Elim h0; Intros y h1; Elim h1; Intros Y h2.
Right.
Rewrite h2 in h.
Rewrite juxt_ass in h.
Assert h3 := (juxt_inj h).
Simpl in h3.
Injection h3; Intros h4 h5.
Elim (juxt_nil h4); Intros h6 h7.
Rewrite h2; Rewrite h6; Rewrite h5.
Pattern 2 Z; Rewrite juxt_nil_end.
Rewrite snoc_juxt.
Reflexivity.
Qed.

Lemma juxt_inj1 : (l,m,n:(list A))(juxt l m)=(juxt l n)->m=n.
Proof.
Induction l; Simpl.
Trivial.
Intros a l' ih m n h.
Injection h.
Intro h0.
Exact (ih m n h0).
Qed.

Lemma juxtlml : (l,m:(list A))(juxt l m)=l->m=Nil.
Proof.
NewInduction l; Simpl; Intros m h.
Exact h.
Injection h; Intro h0.
Exact (IHl m h0).
Qed.

Definition infinitely_many := (l:(list A)){a:A|~(In a l)}.

Fixpoint maxlist [l:(list nat)] : nat :=
Cases l of 
| nil       => O (* default *)
|(cons n t) => (max n (maxlist t))
end.

Lemma gt_all_not_in : 
 (l:(list nat);n:nat)((m:nat)(In m l)->(lt m n))->~(In n l).
Proof.
Induction l; Simpl.
Exact [_;_;h]h.
Intros a t ih n h.
Red; Intro h0.
Apply (le_Sn_n n).
Exact (h n h0).
Qed.

Lemma le_n_max_n_m : (n,m:nat)(le n (max n m)).
Proof.
Induction n; Clear n; Simpl.
Exact le_O_n.
Intros n ih m.
Case m; Clear m.
Apply le_n.
Intro m.
Elim (ih m); Clear m.
Apply le_n.
Intros m h h0.
Apply le_S.
Exact h0.
Qed.

Lemma max_symm : (n,m:nat)(max n m)=(max m n).
Proof.
Induction n.
Simpl.
Destruct m; Auto.
Intros n' ih m.
Case m; Simpl.
Reflexivity.
Intro m'.
Apply eq_S.
Apply ih.
Qed.

Lemma in_le_max : (l:(list nat);m:nat)(In m l)->(le m (maxlist l)).
Proof.
Induction l; Simpl.
Intros m h.
Elim h.
Intros a t ih m h.
Elim h; Intro h0.
Rewrite h0.
Apply le_n_max_n_m.
Apply le_trans with m:=(maxlist t).
Exact (ih m h0).
Rewrite max_symm.
Apply le_n_max_n_m.
Qed.

Lemma le_S_S : (n,m:nat)(le n m)->(le (S n)(S m)).
Proof.
Intros n m h.
Elim h.
Apply le_n.
Intros k h1 h2.
Apply le_S.
Exact h2.
Qed.

Lemma succ_max_not_in : (l:(list nat))~(In (S(maxlist l)) l).
Proof.
Intro l.
Apply gt_all_not_in.
Intros n h.
Unfold lt.
Apply le_S_S.
Exact (in_le_max h).
Qed.

Definition sub := [l,m:(list A)](x:A)(In x l)->(In x m).

Lemma sub_nil : (l:(list A))(sub Nil l).
Proof [l;x](False_ind (In x l)).

Lemma sub_refl : (l:(list A))(sub l l).
Proof [l;x;h]h.

Lemma sub_trans : (l1,l2,l3:(list A))(sub l1 l2)->(sub l2 l3)->(sub l1 l3).
Proof [l1,l2,l3;h;h0;x;h1](h0 x (h x h1)).

Lemma sub_juxt : 
 (l,l',m,m':(list A))(sub l l')->(sub m m')->(sub (juxt l m)(juxt l' m')).
Proof.
Unfold sub; Intros l l' m m' h h0 x h1.
Apply in_or_juxt.
Elim (in_juxt_or h1); Intro h2; [ Left; Exact (h x h2) | Right; Exact (h0 x h2) ].
Qed.

Fixpoint reverse_rec [l:(list A)] : (list A)->(list A) :=
[m] Cases l of
| nil        => m
|(cons a l') => (reverse_rec l' (cons a m))
end.

Definition reverse := [l:(list A)](reverse_rec l Nil).

Lemma rev_rec_juxt : (l,m:(list A))(reverse_rec l m) = (juxt (reverse l) m).
Proof.
NewInduction l; Intro m; Simpl.
Reflexivity.
Rewrite IHl.
Unfold reverse; Simpl.
Rewrite (IHl (cons a Nil)).
Rewrite juxt_ass.
Simpl.
Reflexivity.
Qed.

Lemma rev_cons_juxt : (l,m:(list A);a:A)
 (juxt (reverse (cons a l)) m) = (juxt (reverse l)(cons a m)).
Proof.
Unfold reverse; Simpl.
Intros l m a.
Rewrite rev_rec_juxt.
Rewrite juxt_ass.
Reflexivity.
Qed.

Lemma rev_snoc_juxt : 
 (a:A;l,m:(list A))(juxt (reverse (snoc a l)) m) = (juxt (cons a (reverse l)) m).
Proof.
NewInduction l; Intro m; Simpl.
Reflexivity.
Rewrite rev_cons_juxt.
Rewrite rev_cons_juxt.
Exact (IHl (cons a0 m)).
Qed.

Lemma rev_snoc : 
 (a:A;l:(list A))(reverse (snoc a l)) = (cons a (reverse l)).
Proof.
Intros a l.
Rewrite (juxt_nil_end (reverse (snoc a l))).
Rewrite (juxt_nil_end (cons a (reverse l))).
Apply rev_snoc_juxt.
Qed.

Lemma rev_rev_juxt : (l,m:(list A))(reverse (juxt (reverse l) m)) = (juxt (reverse m) l).
Proof.
NewInduction l; Intro m.
Rewrite <- juxt_nil_end; Reflexivity.
Rewrite rev_cons_juxt.
Rewrite IHl.
Rewrite rev_cons_juxt; Reflexivity.
Qed.

Lemma rev_rev : (l:(list A))(reverse (reverse l)) = l.
Proof.
Intro l; Rewrite (juxt_nil_end (reverse l)); Exact (rev_rev_juxt l Nil).
Qed.

End lists.

(** other preliminaries, nothing to do with lists. *)

Lemma nat_eq_dec : (n,m:nat){n=m}+{~n=m}.
Proof.
NewInduction n.
Destruct m.
Left; Reflexivity.
Right; Red; Intro h; Discriminate h.
Destruct m.
Right; Red; Intro h; Discriminate h.
Intro m'.
Elim (IHn m'); Intro h.
Left; Rewrite h; Reflexivity.
Right; Red; Intro h0; Injection h0; Intro h1; Exact (h h1).
Qed.

Lemma simpl_plus_r : (n,m,k:nat)(plus m n)=(plus k n)->m=k.
Proof.
Intros n m k; Rewrite (plus_sym m n); Rewrite (plus_sym k n); Exact (simpl_plus_l n m k).
Qed.

Lemma dmx : (A,B:Prop)~(A\/B)->~A/\~B.
Proof.
Intros p q h; Split; Intro h0; Apply h; [ Left; Exact h0 | Right; Exact h0 ].
Qed.

Unset Implicit Arguments.
