Require Export adbmal.

Set Implicit Arguments.

Section scope_subtraction.

Inductive sign : Set := pos : sign | neg : sign.

(** 
   [(scope_subtract_rec Y X C J B)]
   - subtract [X] from [Y];
   - [C] are the matches of [X] and [Y]; 
   - [J] are the [y]s jumped by the top of [X];
   - [B] stores [Y] (reversed). 
*)

Fixpoint scope_subtract_rec [Y:stack] : stack->stack->stack->stack->(sign*stack)*(stack*stack*stack) 
 := [X,C,J,B]
Cases X of
| nil        => ((pos,Y),(C,(J,B)))
|(cons x xs) =>
  Cases Y of
  | nil        => ((neg,(cons x xs)),(C,(J,B)))
  |(cons y ys) => 
    Cases (eq_dec x y) of
    |(left _) => (* x matches y; reset jump stack *)
                 (scope_subtract_rec ys xs (cons x C) Nil (cons y B)) 
    | _       => (* x scope_subtract y *)
                 (scope_subtract_rec ys (cons x xs) C (cons y J) (cons y B))
    end
  end
end. 

Definition scope_subtract := [Y,X](scope_subtract_rec Y X Nil Nil Nil).

Lemma scope_subtract_rec_neg_scb :
 (X1,X2,C,B:stack;x:name)
  [X1':=(reverse X1)]
   (scope_subtract_rec X1 (juxt X1 (cons x X2)) C Nil B) 
    = ((neg,(cons x X2)),((juxt X1' C),(Nil,(juxt X1' B)))).
Proof.
NewInduction X1; Intros X2 C B x X1'; Simpl.
Reflexivity.
Case (eq_dec a a); Intro h; [ Clear h | Elim h; Reflexivity ].
Unfold X1'; Rewrite rev_cons_juxt; Rewrite rev_cons_juxt; Apply IHX1.
Qed.

Lemma scope_subtract_neg_scb :
 (X1,X2:stack;x:name)
  [X1':=(reverse X1)]
   (scope_subtract X1 (juxt X1 (cons x X2))) 
    = ((neg,(cons x X2)),(X1',(Nil,X1'))).
Proof.
Intros X1 X2 x X1'.
Rewrite (juxt_nil_end X1').
Exact (scope_subtract_rec_neg_scb X1 X2 Nil Nil x).
Qed.

Lemma scope_subtract_rec_pos_scb :
 (Y1,Y2,C,B:stack)
  [Y1':=(reverse Y1)]
   (scope_subtract_rec (juxt Y1 Y2) Y1 C Nil B) 
    = ((pos,Y2),((juxt Y1' C),(Nil,(juxt Y1' B)))).
Proof.
NewInduction Y1; Intros Y2 C B Y1'; Simpl.
Case Y2; Reflexivity.
Case (eq_dec a a); Intro h; [ Clear h | Elim h; Reflexivity ].
Unfold Y1'; Rewrite rev_cons_juxt; Rewrite rev_cons_juxt; Apply IHY1.
Qed.

Lemma scope_subtract_pos_scb :
 (Y1,Y2:stack)
  [Y1':=(reverse Y1)]
   (scope_subtract (juxt Y1 Y2) Y1) = ((pos,Y2),(Y1',(Nil,Y1'))).
Proof.
Intros Y1 Y2 Y1'.
Rewrite (juxt_nil_end Y1').
Exact (scope_subtract_rec_pos_scb Y1 Y2 Nil Nil).
Qed.

Lemma scope_subtract_rec_dec :
 (Y,X,C,J,B:stack)
 (EX x:name|(EX X':stack|(EX C':stack|(EX J':stack|(EX B':stack|
  (scope_subtract_rec Y X C J B) = ((neg,(cons x X')),(C',(J',B')))
  /\ (juxt (reverse C) X) = (juxt (reverse C')(cons x X'))
  /\ (juxt (reverse B) Y) = (reverse B')
 )))))
 \/
 (Cases X of 
  | nil       => (scope_subtract_rec Y X C J B) = ((pos,Y),(C,(J,B)))
  |(cons _ _) => (EX Y':stack|(EX B':stack|
                  (scope_subtract_rec Y X C J B) = ((pos,Y'),((juxt (reverse X) C),(Nil,B')))
                  /\ (juxt (reverse B) Y) = (juxt (reverse B') Y')))
  end).
Proof.
NewInduction Y; Intros X C J B; NewDestruct X; Simpl.
Right; Reflexivity.
Left; Exists n; Exists l; Exists C; Exists J; Exists B; Split;
 [ Reflexivity | Split; [ Reflexivity | Rewrite juxt_nil_end; Reflexivity ] ].
Right; Reflexivity.
Case (eq_dec n a); Intro h; Simpl.
Elim (IHY l (cons n C) Nil (cons a B)); Intro h0; [ Left | Right ].
Elim h0; Intros x h1; Elim h1; Intros X' h2; Elim h2; Intros C' h3;
 Elim h3; Intros J' h4; Elim h4; Intros B' h5; Elim h5;
 Clear h0 h1 h2 h3 h4 h5; Intros h0 h1; Elim h1; Clear h1; Intros h1 h2.
Exists x; Exists X'; Exists C'; Exists J'; Exists B'; Split.
Exact h0.
Split.
Rewrite <- rev_cons_juxt; Exact h1.
Rewrite <- rev_cons_juxt; Exact h2.
NewDestruct l.
Exists Y; Exists (cons a B); Split.
Simpl.
Exact h0.
Rewrite rev_cons_juxt; Reflexivity.
Elim h0; Intros Y' h1; Elim h1; Intros B' h2; Elim h2; Clear h0 h1 h2; Intros h0 h1.
Exists Y'; Exists B'; Split.
Rewrite rev_cons_juxt; Exact h0.
Rewrite <- rev_cons_juxt; Exact h1.
Elim (IHY (cons n l) C (cons a J) (cons a B)); Intro h0; [ Left | Right ].
Elim h0; Intros x h1; Elim h1; Intros X' h2; Elim h2; Intros C' h3;
 Elim h3; Intros J' h4; Elim h4; Intros B' h5; Elim h5;
 Clear h0 h1 h2 h3 h4 h5; Intros h0 h1; Elim h1; Clear h1; Intros h1 h2.
Exists x; Exists X'; Exists C'; Exists J'; Exists B'; Split.
Exact h0.
Split.
Exact h1.
Rewrite <- rev_cons_juxt; Exact h2.
Elim h0; Intros Y' h1; Elim h1; Intros B' h2; Elim h2; Clear h0 h1 h2;
Intros h0 h1.
Exists Y'; Exists B'; Split.
Exact h0.
Rewrite <- rev_cons_juxt; Exact h1.
Qed.

(**
  [(scope_subtract X Y)] is decidable.
*)

Lemma scope_subtract_dec :
 (X,Y:stack)
  (EX x:name|(EX X':stack|(EX C:stack|(EX J:stack|
   (scope_subtract Y X) = ((neg,(cons x X')),(C,(J,(reverse Y))))
   /\ X = (juxt (reverse C)(cons x X'))))))
  \/ (EX Y':stack|(EX B:stack|
      (scope_subtract Y X) = ((pos,Y'),((reverse X),(Nil,B)))
       /\ Y = (juxt (reverse B) Y'))).
Proof.
Intros X Y; Elim (scope_subtract_rec_dec Y X Nil Nil Nil); Intro h; [ Left | Right ].
Elim h; Simpl; Intros x h0; Elim h0; Intros X' h1; Elim h1; 
 Intros C h2; Elim h2; Intros J h3; Elim h3; Intros B h4; Elim h4;
 Clear h h0 h1 h2 h3 h4; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists x; Exists X'; Exists C; Exists J; Split.
Pattern 2 Y; Rewrite h1; Rewrite rev_rev; Exact h.
Exact h0.
NewDestruct X.
Exists Y; Exists (nil name); Split; [ Exact h | Reflexivity ].
Elim h; Intros Y' h0; Elim h0; Intros B h1; Elim h1; Clear h h0 h1; Intros h h0.
Exists Y'; Exists B; Split.
Rewrite (juxt_nil_end (reverse (cons n l))); Exact h.
Exact h0.
Qed.

End scope_subtraction.
