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

Fixpoint scope_subtract_rec (Y X C J B:stack) {struct Y}
  : (sign*stack)*(stack*(stack*stack)) :=
match X with
| nil => ((pos,Y),(C,(J,B)))
| cons x xs =>
    match Y with
    | nil => ((neg,cons x xs),(C,(J,B)))
    | cons y ys =>
        match eq_dec x y with
        | left _ => (* x matches y; reset jump stack *)
            scope_subtract_rec ys xs (cons x C) nil (cons y B)
        | right _ => (* x scope_subtract y *)
            scope_subtract_rec ys (cons x xs) C (cons y J) (cons y B)
        end
    end
end.

Definition scope_subtract (Y X:stack) :=
  scope_subtract_rec Y X nil nil nil.

Lemma scope_subtract_rec_neg_scb :
 forall (X1 X2 C B:stack) (x:name),
  let X1' := reverse X1 in
   (scope_subtract_rec X1 (juxt X1 (cons x X2)) C nil B) 
    = ((neg,(cons x X2)),((juxt X1' C),(nil,(juxt X1' B)))).
Proof.
intros X1.
induction X1 as [|a X1 IHX1]; intros X2 C B x; simpl.
- reflexivity.
- destruct (eq_dec a a) as [_|h].
  + rewrite rev_cons_juxt. rewrite rev_cons_juxt. apply IHX1.
  + exfalso. apply h. reflexivity.
Qed.

Lemma scope_subtract_neg_scb :
 forall (X1 X2:stack) (x:name),
  let X1' := reverse X1 in
   (scope_subtract X1 (juxt X1 (cons x X2))) 
    = ((neg,(cons x X2)),(X1',(nil,X1'))).
Proof.
intros X1 X2 x; simpl.
rewrite (juxt_nil_end (reverse X1)).
exact (scope_subtract_rec_neg_scb X1 X2 nil nil x).
Qed.

Lemma scope_subtract_rec_pos_scb :
 forall Y1 Y2 C B:stack,
  let Y1' := reverse Y1 in
   (scope_subtract_rec (juxt Y1 Y2) Y1 C nil B) 
    = ((pos,Y2),((juxt Y1' C),(nil,(juxt Y1' B)))).
Proof.
intros Y1.
induction Y1 as [|a Y1 IHY1]; intros Y2 C B; simpl.
- destruct Y2; reflexivity.
- destruct (eq_dec a a) as [_|h].
  + rewrite rev_cons_juxt. rewrite rev_cons_juxt. apply IHY1.
  + exfalso. apply h. reflexivity.
Qed.

Lemma scope_subtract_pos_scb :
 forall Y1 Y2:stack,
  let Y1' := reverse Y1 in
   (scope_subtract (juxt Y1 Y2) Y1) = ((pos,Y2),(Y1',(nil,Y1'))).
Proof.
intros Y1 Y2; simpl.
rewrite (juxt_nil_end (reverse Y1)).
exact (scope_subtract_rec_pos_scb Y1 Y2 nil nil).
Qed.

Lemma scope_subtract_rec_dec :
 forall Y X C J B:stack,
 (exists x:name, exists X':stack, exists C':stack, exists J':stack,
  exists B':stack,
   scope_subtract_rec Y X C J B = ((neg,cons x X'),(C',(J',B')))
   /\ juxt (reverse C) X = juxt (reverse C') (cons x X')
   /\ juxt (reverse B) Y = reverse B')
 \/
 (match X with
  | nil => scope_subtract_rec Y X C J B = ((pos,Y),(C,(J,B)))
  | cons _ _ =>
      exists Y':stack, exists B':stack,
       scope_subtract_rec Y X C J B =
         ((pos,Y'),(juxt (reverse X) C,(nil,B')))
       /\ juxt (reverse B) Y = juxt (reverse B') Y'
  end).
Proof.
intros Y.
induction Y as [|a Y IHY]; intros X C J B; destruct X as [|n l]; simpl.
- right. reflexivity.
- left. exists n, l, C, J, B. split.
  + reflexivity.
  + split; [reflexivity | rewrite juxt_nil_end; reflexivity].
- right. reflexivity.
- destruct (eq_dec n a) as [h|h]; simpl.
  + destruct (IHY l (cons n C) nil (cons a B)) as [h0|h0].
    * left.
      destruct h0 as [x [X' [C' [J' [B' [h0 [h1 h2]]]]]]].
      exists x, X', C', J', B'. split.
      -- exact h0.
      -- split.
         ++ rewrite <- rev_cons_juxt. exact h1.
         ++ rewrite <- rev_cons_juxt. exact h2.
    * right.
      destruct l as [|n' l']; simpl in h0.
      -- exists Y, (cons a B). split.
         ++ simpl. exact h0.
         ++ rewrite rev_cons_juxt. reflexivity.
      -- destruct h0 as [Y' [B' [h0 h1]]].
         exists Y', B'. split.
         ++ rewrite rev_cons_juxt. exact h0.
         ++ rewrite <- rev_cons_juxt. exact h1.
  + destruct (IHY (cons n l) C (cons a J) (cons a B)) as [h0|h0].
    * left.
      destruct h0 as [x [X' [C' [J' [B' [h0 [h1 h2]]]]]]].
      exists x, X', C', J', B'. split.
      -- exact h0.
      -- split.
         ++ exact h1.
         ++ rewrite <- rev_cons_juxt. exact h2.
    * right.
      destruct h0 as [Y' [B' [h0 h1]]].
      exists Y', B'. split.
      -- exact h0.
      -- rewrite <- rev_cons_juxt. exact h1.
Qed.

(**
  [(scope_subtract X Y)] is decidable.
*)

Lemma scope_subtract_dec :
 forall X Y:stack,
  (exists x:name, exists X':stack, exists C:stack, exists J:stack,
    scope_subtract Y X = ((neg,cons x X'),(C,(J,reverse Y)))
    /\ X = juxt (reverse C) (cons x X'))
  \/ (exists Y':stack, exists B:stack,
      scope_subtract Y X = ((pos,Y'),(reverse X,(nil,B)))
       /\ Y = juxt (reverse B) Y').
Proof.
intros X Y.
destruct (scope_subtract_rec_dec Y X nil nil nil) as [h|h].
- left.
  destruct h as [x [X' [C [J [B [h [h0 h1]]]]]]].
  exists x, X', C, J. split.
  + simpl in h1.
    apply (f_equal (@reverse name)) in h1.
    rewrite rev_rev in h1.
    rewrite <- h1 in h.
    exact h.
  + exact h0.
- right. destruct X as [|n l]; simpl in h.
  + exists Y, nil. split; [exact h | reflexivity].
  + destruct h as [Y' [B [h h0]]].
    exists Y', B. split.
    * rewrite (juxt_nil_end (reverse (cons n l))). exact h.
    * exact h0.
Qed.

End scope_subtraction.
