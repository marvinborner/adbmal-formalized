Require Export scope_subtract.

Set Implicit Arguments.

Section substitution_lemmas.

(** 
  To simplify an expression [(/X.M)[Z,x:=N,Y]] we distinguish three cases.
   - 1. [X] ends more scopes than were opened by [Y], 
        thus including the scope of the substitution variable [x],
        which might be:
        -- a. matched --> lemma [simpl_adbmal_subst_eoss_closed_msv]; or
        -- b. jumped  --> lemma [simpl_adbmal_subst_eoss_closed_jsv];
   - 2. [X] closes part (possible all) of [Y] 
        --> lemma [simpl_adbmal_subst_eoss_open].

  First we define an auxiliary function [adbmal_subst_eoss_aux],
  to express substitution in the [eoss] case;
  the [J]-argument records the [y]s jumped by the top of [X].
  See subsequent lemma [adbmal_subst_eq_adbmal_subst_eoss_aux].
*)

Fixpoint adbmal_subst_eoss_aux [M,N:Adbmal;x:name;Z,Y,J,X:stack] : Adbmal :=
Cases X of 
| nil         => (adbmal_subst Z Y M x N)
|(cons x0 xs) => 
 (Fix aux {aux/1 : stack->stack->Adbmal :=
  [l,k] Cases l of
        | nil => [k':=(reverse k)]
          Cases (eq_dec x x0) of
          |(left _) => (eoss k' (eoss Z (eoss xs M)))
          | _       => (eoss k' (eoss Z (eos x0 (eoss xs M))))
          end
        |(cons y l') =>
          Cases (eq_dec x0 y) of
          |(left _) => (eos x0 (adbmal_subst_eoss_aux M N x Z l' Nil xs))
          | _       => (aux l' (cons y k))
          end
        end } Y J)
 end.

Lemma adbmal_subst_eq_adbmal_subst_eoss_aux :
 (M,N:Adbmal;X,Y,Z:stack;x:name)
  (adbmal_subst Z Y (eoss X M) x N)
   =(adbmal_subst_eoss_aux M N x Z Y Nil X).
Proof.
NewInduction X; Intros Y Z x; Simpl.
Reflexivity.
Assert h : (W:stack)
            (Fix aux
               {aux [l:stack] : stack->Adbmal :=
                  [k:stack]
                   Cases (l) of
                     nil => 
                      Cases (eq_dec x a) of
                        (left _) => 
                         (eoss (reverse k) (eoss Z (eoss X M)))
                      | (right _) => 
                         (eoss (reverse k) (eoss Z (eos a (eoss X M))))
                      end
                   | (cons z l') => 
                      Cases (eq_dec a z) of
                        (left _) => 
                         (eos a (adbmal_subst Z l' (eoss X M) x N))
                      | (right _) => (aux l' (cons z k))
                      end
                   end} Y W)
             =(Fix aux
                 {aux [l:stack] : stack->Adbmal :=
                    [k:stack]
                     Cases (l) of
                       nil => 
                        Cases (eq_dec x a) of
                          (left _) => 
                           (eoss (reverse k) (eoss Z (eoss X M)))
                        | (right _) => 
                           (eoss (reverse k)
                             (eoss Z (eos a (eoss X M))))
                        end
                     | (cons y l') => 
                        Cases (eq_dec a y) of
                          (left _) => 
                           (eos a
                             (adbmal_subst_eoss_aux M N x Z l'
                               (nil name) X))
                        | (right _) => (aux l' (cons y k))
                        end
                     end} Y W).
NewInduction Y; Intro W; Simpl.
Case (eq_dec x a); Intro; Reflexivity.
Case (eq_dec a a0); Intro h.
Rewrite IHX; Reflexivity.
Apply IHY.
Apply h.
Qed.

Lemma simpl_adbmal_subst_eoss_aux_closed_msv :
 (M,N:Adbmal;Z,Y,X,X',C,C',J,J',B,B':stack;x,x':name)
  (scope_subtract_rec Y X C J B) = ((neg,(cons x' X')),(C',(J',B')))
   ->(x=x')
    ->(eoss (reverse C) (adbmal_subst_eoss_aux M N x Z Y J X))
       = (eoss (reverse C') (eoss (reverse J') (eoss Z (eoss X' M)))).
Proof.
NewInduction Y; NewDestruct X; Simpl; Intros X' C C' J J' B B' x x' h h0.
Discriminate h.
Injection h; Intros h1 h2 h3 h4 h5.
Rewrite h5; Case (eq_dec x x'); Intro h6; [ Clear h6 | Elim (h6 h0) ].
Rewrite h2; Rewrite h3; Rewrite h4; Reflexivity.
Discriminate h.
NewDestruct (eq_dec n a).
Replace (eos n (adbmal_subst_eoss_aux M N x Z Y (nil name) l)) 
 with (eoss (cons n Nil)(adbmal_subst_eoss_aux M N x Z Y (nil name) l)).
2:Reflexivity.
Rewrite <- eoss_juxt.
Rewrite <- rev_cons_juxt.
Rewrite <- juxt_nil_end.
Exact (IHY l X' (cons n C) C' Nil J' (cons a B) B' x x' h h0).
Exact (IHY (cons n l) X' C C' (cons a J) J' (cons a B) B' x x' h h0).
Qed.

Lemma simpl_adbmal_subst_eoss_closed_msv :
 (M,N:Adbmal;Z,Y,X,X',C,J,B:stack;x,x':name)
  (scope_subtract Y X) = ((neg,(cons x' X')),(C,(J,B)))
   ->(x=x')
    ->(adbmal_subst Z Y (eoss X M) x N)
       = (eoss (reverse C) (eoss (reverse J) (eoss Z (eoss X' M)))).
Proof.
Intros M N Z Y X X' C J B x x' h h0.
Rewrite adbmal_subst_eq_adbmal_subst_eoss_aux.
Exact (simpl_adbmal_subst_eoss_aux_closed_msv M N Z h h0).
Qed.

Lemma simpl_adbmal_subst_eoss_aux_closed_jsv :
 (M,N:Adbmal;Z,Y,X,X',C,C',J,J',B,B':stack;x,x':name)
  (scope_subtract_rec Y X C J B) = ((neg,(cons x' X')),(C',(J',B')))
   ->~(x=x')
    ->(eoss (reverse C) (adbmal_subst_eoss_aux M N x Z Y J X))
       = (eoss (reverse C') (eoss (reverse J') (eoss Z (eos x' (eoss X' M))))).
Proof.
NewInduction Y; NewDestruct X; Simpl; Intros X' C C' J J' B B' x x' h h0.
Discriminate h.
Injection h; Intros h1 h2 h3 h4 h5.
Rewrite h5; Case (eq_dec x x'); Intro h6; [ Elim (h0 h6) | Clear h6 ].
Rewrite h2; Rewrite h3; Rewrite h4; Reflexivity.
Discriminate h.
NewDestruct (eq_dec n a).
Replace (eos n (adbmal_subst_eoss_aux M N x Z Y (nil name) l))
 with (eoss (cons n Nil) (adbmal_subst_eoss_aux M N x Z Y (nil name) l)).
2:Reflexivity.
Rewrite <- eoss_juxt.
Rewrite <- rev_cons_juxt.
Rewrite <- juxt_nil_end.
Exact (IHY l X' (cons n C) C' Nil J' (cons a B) B' x x' h h0).
Exact (IHY (cons n l) X' C C' (cons a J) J' (cons a B) B' x x' h h0).
Qed.

Lemma simpl_adbmal_subst_eoss_closed_jsv :
 (M,N:Adbmal;Z,Y,X,X',C,J,B:stack;x,x':name)
  (scope_subtract Y X) = ((neg,(cons x' X')),(C,(J,B)))
   ->~(x=x')
    ->(adbmal_subst Z Y (eoss X M) x N)
       = (eoss (reverse C) (eoss (reverse J) (eoss Z (eos x' (eoss X' M))))).
Proof.
Intros M N Z Y X X' C J B x x' h h0.
Rewrite adbmal_subst_eq_adbmal_subst_eoss_aux.
Exact (simpl_adbmal_subst_eoss_aux_closed_jsv M N Z h h0).
Qed.

Lemma simpl_adbmal_subst_eoss_aux_open :
 (M,N:Adbmal;Z,Y,Y',X,C,C',J,J',B,B':stack;x:name)
  (scope_subtract_rec Y X C J B)=((pos,Y'),(C',(J',B')))
   ->(adbmal_subst_eoss_aux M N x Z Y J X)
      = (eoss X (adbmal_subst Z Y' M x N)).
Proof.
NewInduction Y; NewDestruct X; Simpl; Intros C C' J J' B B' x h.
Injection h; Intros h1 h2 h3 h4.
Rewrite <- h4; Reflexivity.
Discriminate h.
Injection h; Intros h1 h2 h3 h4.
Rewrite h4; Reflexivity.
NewDestruct (eq_dec n a).
Apply feq.
Apply IHY with 1:=h.
Exact (IHY Y' (cons n l) C C' (cons a J) J' (cons a B) B' x h).
Qed.

Lemma simpl_adbmal_subst_eoss_open :
 (M,N:Adbmal;Z,Y,Y',X,C,J,B:stack;x:name)
  (scope_subtract Y X)=((pos,Y'),(C,(J,B)))
   ->(adbmal_subst Z Y (eoss X M) x N)
      = (eoss X (adbmal_subst Z Y' M x N)).
Proof.
Intros M N Z Y Y' X C J B x h.
Rewrite adbmal_subst_eq_adbmal_subst_eoss_aux.
Exact (simpl_adbmal_subst_eoss_aux_open M N Z x h).
Qed.

(** 
  Substitution Lemmata.

  Consider the critical pairs arising from (/Z.\y.\Y'.(/X.\x.\W'.s)t)u.
  Let L' denote (reverse L).
  We distinguish three cases.

- 1. scope_subtract(Y,X) = (neg, zX2, X1', J', Y'), (then X = X1zX2) 

	-- a. z matches y 	--> closed_subst_lemma_msv

	-- b. z jumps y 	--> closed_subst_lemma_jsv

- 2. scope_subtract(Y,X) = (pos, Y2, X', Nil, Y1'), (then Y = Y1Y2)

					    --> open_subst_lemma
*)

(**
  [closed_subst_lemma_msv] Closed Substitution Lemma (subst var matched);
  substitution variable y is closed in innermost redex (y in X).
  [[

  scope_subtract(X1zX2,Y) = (neg, zX2, X1', J', Y') /\ (y=z)
   ->
    s[X1zX2,x:=t,W][Z,y:=u,WY] = s[X1JZX2,x:=t[Z,y:=u,Y],W]

  ]]
*)

Lemma closed_subst_lemma_msv :
 (s,t,u:Adbmal;Y,X1,X2,W,Z,J:stack;x,y,z:name)
  [X1':=(reverse X1);J':=(reverse J);Y':=(reverse Y)]
  (scope_subtract Y (juxt X1 (cons z X2))) = ((neg,(cons z X2)),(X1',(J',Y')))
   ->(y=z)
    ->(adbmal_subst Z (juxt W Y) (adbmal_subst (juxt X1 (cons z X2)) W s x t) y u)
       = (adbmal_subst (juxt X1 (juxt J (juxt Z X2))) W s x (adbmal_subst Z Y t y u)).
Proof.
NewInduction s; Intros t u Y X1 X2 W Z J x y z X1' J' Y' h e.

(* var *)
Simpl.
Case (in_dec n W); Intro h0; Simpl.
Case (in_dec n (juxt W Y)); Intro h1.
Reflexivity.
Elim h1; Apply in_or_juxt; Left; Exact h0.
Case (eq_dec x n); Intro h1; Simpl.
Apply subst_eoss.
Rewrite subst_eoss.
Apply feq.
Rewrite (simpl_adbmal_subst_eoss_closed_msv (var n) u Z h e).
Rewrite eoss_juxt; Rewrite eoss_juxt; Rewrite eoss_juxt.
Unfold J'; Rewrite rev_rev; Unfold X1'; Rewrite rev_rev; Reflexivity.

(* abs *)
Simpl; Apply feq.
Exact (IHs t u Y X1 X2 (cons n W) Z J x y z h e).

(* eos *)
Case (in_dec n W); Intro h0.
(* (In n W) *)
Elim (in_split eq_dec h0); Intros W1 h1; Elim h1; Intros W2 h2;
Elim h2; Clear h1 h2; Intros h1 h2.
Rewrite h1.
Rewrite (adbmal_subst_eos_clause1 s t x (juxt X1 (cons z X2)) W2 h2).
Rewrite (adbmal_subst_eos_clause1 s (adbmal_subst Z Y t y u) x (juxt X1 (juxt J (juxt Z X2))) W2 h2).
Rewrite juxt_ass.
Replace (juxt (cons n W2) Y) with (cons n (juxt W2 Y)).
2:Reflexivity.
Rewrite (adbmal_subst_eos_clause1 (adbmal_subst (juxt X1 (cons z X2)) W2 s x t) u y Z (juxt W2 Y) h2).
Apply feq; Exact (IHs t u Y X1 X2 W2 Z J x y z h e).
(* ~(In n W) *)
Case (eq_dec x n); Intro h1.
(* x = n *)
Rewrite (adbmal_subst_eos_clause2 s t (juxt X1 (cons z X2)) h1 h0).
Rewrite (adbmal_subst_eos_clause2 s (adbmal_subst Z Y t y u) (juxt X1 (juxt J (juxt Z X2))) h1 h0).
Rewrite subst_eoss.
Apply feq.
Rewrite (simpl_adbmal_subst_eoss_closed_msv s u Z h e).
Unfold X1'; Rewrite rev_rev; Unfold J'; Rewrite rev_rev.
Rewrite eoss_juxt; Rewrite eoss_juxt; Rewrite eoss_juxt; Reflexivity.
(* ~(x = n) *)
Rewrite (adbmal_subst_eos_clause3 s t (juxt X1 (cons z X2)) h1 h0).
Rewrite (adbmal_subst_eos_clause3 s (adbmal_subst Z Y t y u) (juxt X1 (juxt J (juxt Z X2))) h1 h0).
Rewrite subst_eoss.
Apply feq.
Rewrite (simpl_adbmal_subst_eoss_closed_msv (eos n s) u Z h e).
Unfold X1'; Rewrite rev_rev; Unfold J'; Rewrite rev_rev.
Rewrite eoss_juxt; Rewrite eoss_juxt; Rewrite eoss_juxt; Reflexivity.

(* ap *)
Simpl.
Rewrite (IHs1 t u Y X1 X2 W Z J x y z h e).
Rewrite (IHs2 t u Y X1 X2 W Z J x y z h e).
Reflexivity.
Qed.


(**
  [closed_subst_lemma_jsv] Closed Substitution Lemma (subst var jumped),
  substitution variable y is jumped (by z in X).
  [[

  scope_subtract(X1zX2,Y) = (neg, zX2, X1', J', Y') /\ ~(y=z)
  -> s[X1zX2,x:=t,W][Z,y:=u,WY] = s[X1JZX2,x:=t[Z,y:=u,Y],W]

  ]]
*)

Lemma closed_subst_lemma_jsv :
 (s,t,u:Adbmal;Y,X1,X2,W,Z,J:stack;x,y,z:name)
  [X1':=(reverse X1);J':=(reverse J);Y':=(reverse Y)]
  (scope_subtract Y (juxt X1 (cons z X2))) = ((neg,(cons z X2)),(X1',(J',Y')))
   ->~(y=z)
    ->(adbmal_subst Z (juxt W Y) (adbmal_subst (juxt X1 (cons z X2)) W s x t) y u)
       = (adbmal_subst (juxt X1 (juxt J (juxt Z (cons z X2)))) W s x (adbmal_subst Z Y t y u)).
Proof.
NewInduction s; Intros t u Y X1 X2 W Z J x y z X1' J' Y' h e.

(* var *)
Simpl.
Case (in_dec n W); Intro h0; Simpl.
Case (in_dec n (juxt W Y)); Intro h1.
Reflexivity.
Elim h1; Apply in_or_juxt; Left; Exact h0.
Case (eq_dec x n); Intro h1; Simpl.
Apply subst_eoss.
Rewrite subst_eoss.
Apply feq.
Rewrite (simpl_adbmal_subst_eoss_closed_jsv (var n) u Z h e).
Rewrite eoss_juxt; Rewrite eoss_juxt; Rewrite eoss_juxt.
Unfold J'; Rewrite rev_rev; Unfold X1'; Rewrite rev_rev; Reflexivity.

(* abs *)
Simpl; Apply feq.
Exact (IHs t u Y X1 X2 (cons n W) Z J x y z h e).

(* eos *)
Case (in_dec n W); Intro h0.
(* (In n W) *)
Elim (in_split eq_dec h0); Intros W1 h1; Elim h1; Intros W2 h2;
Elim h2; Clear h1 h2; Intros h1 h2.
Rewrite h1.
Rewrite (adbmal_subst_eos_clause1 s t x (juxt X1 (cons z X2)) W2 h2).
Rewrite (adbmal_subst_eos_clause1 s (adbmal_subst Z Y t y u) x (juxt X1 (juxt J (juxt Z (cons z X2)))) W2 h2).
Rewrite juxt_ass.
Replace (juxt (cons n W2) Y) with (cons n (juxt W2 Y)).
2:Reflexivity.
Rewrite (adbmal_subst_eos_clause1 (adbmal_subst (juxt X1 (cons z X2)) W2 s x t) u y Z (juxt W2 Y) h2).
Apply feq; Exact (IHs t u Y X1 X2 W2 Z J x y z h e).
(* ~(In n W) *)
Case (eq_dec x n); Intro h1.
(* x = n *)
Rewrite (adbmal_subst_eos_clause2 s t (juxt X1 (cons z X2)) h1 h0).
Rewrite (adbmal_subst_eos_clause2 s (adbmal_subst Z Y t y u) (juxt X1 (juxt J (juxt Z (cons z X2)))) h1 h0).
Rewrite subst_eoss.
Apply feq.
Rewrite (simpl_adbmal_subst_eoss_closed_jsv s u Z h e).
Unfold X1'; Rewrite rev_rev; Unfold J'; Rewrite rev_rev.
Rewrite eoss_juxt; Rewrite eoss_juxt; Rewrite eoss_juxt; Reflexivity.
(* ~(x = n) *)
Rewrite (adbmal_subst_eos_clause3 s t (juxt X1 (cons z X2)) h1 h0).
Rewrite (adbmal_subst_eos_clause3 s (adbmal_subst Z Y t y u) (juxt X1 (juxt J (juxt Z (cons z X2)))) h1 h0).
Rewrite subst_eoss.
Apply feq.
Rewrite (simpl_adbmal_subst_eoss_closed_jsv (eos n s) u Z h e).
Unfold X1'; Rewrite rev_rev; Unfold J'; Rewrite rev_rev.
Rewrite eoss_juxt; Rewrite eoss_juxt; Rewrite eoss_juxt; Reflexivity.

(* ap *)
Simpl.
Rewrite (IHs1 t u Y X1 X2 W Z J x y z h e).
Rewrite (IHs2 t u Y X1 X2 W Z J x y z h e).
Reflexivity.
Qed.


(** 
  [open_subst_lemma] Open Substitution Lemma.
  [[

  scope_subtract(Y1Y2,X) = (pos, Y2, X', Nil, Y1')
  -> s[X,x:=t,W][Z,y:=u,WY1Y2] = s[Z,y:=u,WxY2][X,x:=t[Z,y:=u,Y1Y2],W]

  ]]
*)

Lemma open_subst_lemma :
 (s,t,u:Adbmal;X,Y1,Y2,W,Z:stack;x,y:name)
  [X':=(reverse X);Y1':=(reverse Y1)]
  (scope_subtract (juxt Y1 Y2) X) = ((pos,Y2),(X',(Nil,Y1')))
   ->(adbmal_subst Z (juxt W (juxt Y1 Y2)) (adbmal_subst X W s x t) y u)
     = (adbmal_subst X W (adbmal_subst Z (juxt W (cons x Y2)) s y u) x 
                              (adbmal_subst Z (juxt Y1 Y2) t y u)).
Proof.
NewInduction s; Intros t u X Y1 Y2 W Z x y X' Y1' h.

(* var *)
Simpl.
Case (in_dec n W); Intro h0; Simpl.
Case (in_dec n (juxt W (juxt Y1 Y2))); Intro h1; Simpl.
Case (in_dec n (juxt W (cons x Y2))); Intro h2; Simpl.
Case (in_dec n W); Intro h3.
Reflexivity.
Elim (h3 h0).
Elim h2; Apply in_or_juxt; Left; Exact h0.
Elim h1; Apply in_or_juxt; Left; Exact h0.
Case (eq_dec x n); Intro h1; Simpl.
Case (in_dec n (juxt W (cons x Y2))); Intro h2; Simpl.
Case (in_dec n W); Intro h3; Simpl.
Elim (h0 h3).
Case (eq_dec x n); Intro h4; Simpl.
Apply subst_eoss.
Elim (h4 h1).
Elim h2; Apply in_or_juxt; Right; Left; Exact h1.
Case (in_dec n (juxt W (cons x Y2))); Intro h2; Simpl.
Case (in_dec n W); Intro h3; Simpl.
Elim (h0 h3).
Case (eq_dec x n); Intro h4; Simpl.
Elim (h1 h4).
Rewrite subst_eoss.
Apply feq.
Rewrite (simpl_adbmal_subst_eoss_open (var n) u Z y h); Simpl.
Case (in_dec n Y2); Intro h5; Simpl.
Reflexivity.
Elim h5.
Elim (in_juxt_or h2); Intro h6.
Elim (h0 h6).
Elim h6; Intro h7.
Elim (h4 h7).
Exact h7.
Case (eq_dec y n); Intro h3; Simpl.
Rewrite subst_eoss.
Pattern 2 W; Rewrite (juxt_nil_end W).
Rewrite eoss_juxt.
Rewrite subst_eoss.
Apply feq; Simpl.
Case (eq_dec x x); Intro h4.
Rewrite (simpl_adbmal_subst_eoss_open (var n) u Z y h).
Simpl.
Case (in_dec n Y2); Intro h5; Simpl.
Elim h2; Apply in_or_juxt; Right; Right; Exact h5.
Case (eq_dec y n); Intro h6; Simpl.
Reflexivity.
Elim (h6 h3).
Elim h4; Reflexivity.
Rewrite subst_eoss.
Pattern 2 W; Rewrite (juxt_nil_end W).
Rewrite eoss_juxt; Rewrite subst_eoss.
Apply feq; Simpl.
Case (eq_dec x x); Intro h4; Simpl.
Rewrite (simpl_adbmal_subst_eoss_open (var n) u Z y h); Simpl.
Case (in_dec n Y2); Intro h5; Simpl.
Elim h2; Apply in_or_juxt; Right; Right; Exact h5.
Case (eq_dec y n); Intro h6; Simpl.
Elim (h3 h6).
Reflexivity.
Elim h4; Reflexivity.

(* abs *)
Simpl; Apply feq.
Exact (IHs t u X Y1 Y2 (cons n W) Z x y h).

(* eos *)
Case (in_dec n W); Intro h0.
(* (In n W) *)
Elim (in_split eq_dec h0); Intros W1 h1; Elim h1; Intros W2 h2;
Elim h2; Clear h1 h2; Intros h1 h2.
Rewrite h1.
Rewrite (adbmal_subst_eos_clause1 s t x X W2 h2).
Rewrite juxt_ass.
Replace (juxt (cons n W2) (juxt Y1 Y2)) with (cons n (juxt W2 (juxt Y1 Y2))).
2:Reflexivity.
Rewrite (adbmal_subst_eos_clause1 (adbmal_subst X W2 s x t) u y Z (juxt W2 (juxt Y1 Y2)) h2).
Rewrite juxt_ass.
Replace (juxt (cons n W2) (cons x Y2)) with (cons n (juxt W2 (cons x Y2))).
2:Reflexivity.
Rewrite (adbmal_subst_eos_clause1 s u y Z (juxt W2 (cons x Y2)) h2).
Rewrite (adbmal_subst_eos_clause1 (adbmal_subst Z (juxt W2 (cons x Y2)) s y u) 
             (adbmal_subst Z (juxt Y1 Y2) t y u) x X W2 h2).
Apply feq.
Apply IHs.
Exact h.
(* ~(In n W) *)
Case (eq_dec x n); Intro h1.
(* x = n *)
Rewrite (adbmal_subst_eos_clause2 s t X h1 h0).
Rewrite h1.
Rewrite (adbmal_subst_eos_clause1 s u y Z Y2 h0).
Rewrite (adbmal_subst_eos_clause2 (adbmal_subst Z Y2 s y u)
             (adbmal_subst Z (juxt Y1 Y2) t y u) 
             X (refl_equal name n) h0).
Rewrite subst_eoss.
Apply feq.
Exact (simpl_adbmal_subst_eoss_open s u Z y h).
(* ~(x = n) *)
Rewrite (adbmal_subst_eos_clause3 s t X h1 h0).
Rewrite subst_eoss.
Rewrite (simpl_adbmal_subst_eoss_open (eos n s) u Z y h).
Case (in_dec n Y2); Intro h2. (* !? *)
(* (In n Y2) *)
Elim (in_split eq_dec h2); Intros Y2a h3; Elim h3; Intros Y2b h4;
Elim h4; Clear h3 h4; Intros h3 h4.
Rewrite h3.
Replace (juxt W (cons x (juxt Y2a (cons n Y2b)))) with (juxt (juxt W (cons x Y2a)) (cons n Y2b)).
Assert h5 : ~(In n (juxt W (cons x Y2a))).
Intro h5; Elim (in_juxt_or h5); Intro h6.
Exact (h0 h6).
Elim h6; Intro h7.
Exact (h1 h7).
Exact (h4 h7).
Rewrite (adbmal_subst_eos_clause1 s u y Z Y2b h5).
Rewrite (adbmal_subst_eos_clause3 (adbmal_subst Z Y2b s y u)
             (adbmal_subst Z (juxt Y1 (juxt Y2a (cons n Y2b))) t y u)
             X h1 h0).
Apply feq; Apply feq.
Exact (adbmal_subst_eos_clause1 s u y Z Y2b h4).
Rewrite juxt_ass; Reflexivity.
(* ~(In n Y2) *)
Assert h3 : ~(In n (juxt W (cons x Y2))).
Intro h3; Elim (in_juxt_or h3); Intro h4.
Exact (h0 h4).
Elim h4; Intro h5.
Exact (h1 h5).
Exact (h2 h5).
Case (eq_dec y n); Intro h4.
(* y = n *)
Rewrite (adbmal_subst_eos_clause2 s u Z h4 h3).
Rewrite eoss_juxt.
Pattern 2 W; Rewrite (juxt_nil_end W); Rewrite subst_eoss.
Apply feq.
Rewrite (adbmal_subst_eos_clause2 s u Z h4 h2).
Simpl; Case (eq_dec x x); Intro h5; [ Reflexivity | Elim h5; Reflexivity ].
(* ~(y = n) *)
Rewrite (adbmal_subst_eos_clause3 s u Z h4 h3).
Rewrite eoss_juxt.
Pattern 2 W; Rewrite (juxt_nil_end W); Rewrite subst_eoss.
Apply feq.
Rewrite (adbmal_subst_eos_clause3 s u Z h4 h2).
Simpl; Case (eq_dec x x); Intro h5; [ Reflexivity | Elim h5; Reflexivity ].

(* ap *)
Simpl.
Rewrite (IHs1 t u X Y1 Y2 W Z x y h).
Rewrite (IHs2 t u X Y1 Y2 W Z x y h).
Reflexivity.
Qed.

(** 
  [multistep_subst_lemma] Multi-step Substitution Lemma.
  [[

   t==>t' -> u==>u' -> t[X,x:=u,Y]==>t'[X,x:=u',Y]

  ]]
*)

Lemma multistep_subst_lemma : (t,t',u,u':Adbmal)
 (multistep t t')
  ->(multistep u u')
   ->(X,Y:stack;x:name)
      (multistep (adbmal_subst X Y t x u)(adbmal_subst X Y t' x u')).
Proof.
Intros t t' u u' mt mu.
Elim mt; Clear mt t t'; Simpl.

(* var *)
Intros y X Y x.
Case (in_dec y Y); Intro h.
Apply multistep_var.
Case (eq_dec x y); Intro h0.
Apply multistep_eoss.
Exact mu.
Apply multistep_refl.

(* abs *)
Intros t t' y mt ih X Y x.
Apply multistep_abs.
Exact (ih X (cons y Y) x).

(* eos *)
Intros t t' y mt ih X Y x.
LetTac
 aux:=[t,u]
       Fix aux
         {aux [l:stack] : stack->Adbmal :=
            [k:stack]
             Cases (l) of
               nil => 
                Cases (eq_dec x y) of
                  (left _) => (eoss (reverse k) (eoss X t))
                | (right _) => (eoss (reverse k) (eoss X (eos y t)))
                end
             | (cons z l') => 
                Cases (eq_dec y z) of
                  (left _) => (eos y (adbmal_subst X l' t x u))
                | (right _) => (aux l' (cons z k))
                end
             end}.
Fold (aux t u).
Fold (aux t' u').
Assert h : (Z:stack)(multistep (aux t u Y Z) (aux t' u' Y Z)).
NewInduction Y; Intro Z; Simpl.
Case (eq_dec x y); Intro h0; Apply multistep_eoss; Apply multistep_eoss; 
 [ Exact mt | Apply multistep_eos; Exact mt ].
Case (eq_dec y a); Intro h0.
Apply multistep_eos; Apply ih.
Apply IHY.
Apply h.

(* beta *)
Intros s s' t t' x X ms ihs mt iht Y Y' y.
Elim (scope_subtract_dec X Y'); Intro h.
(* X scope_subtract Y' *)
Elim h; Intros x' h0; Elim h0; Intros X' h1; Elim h1; Intros C h2; Elim h2; Intros J h3;
 Elim h3; Clear h h0 h1 h2 h3; Intros h h0.
Case (eq_dec y x'); Intro h1.
(* y = x' *)
Rewrite (simpl_adbmal_subst_eoss_closed_msv (abs x s) u Y h h1). 
Rewrite <- eoss_juxt; Rewrite <- eoss_juxt; Rewrite <- eoss_juxt.
Rewrite juxt_ass; Rewrite juxt_ass.
Rewrite h0.
Rewrite h0 in h.
Pattern 2 Y'; Replace Y' with (juxt Nil Y').
2:Reflexivity.
Assert h2 : (scope_subtract Y' (juxt (reverse C) (cons x' X')))
             =((neg,(cons x' X')),
               ((reverse (reverse C)),
                ((reverse (reverse J)),(reverse Y')))).
Rewrite rev_rev; Rewrite rev_rev; Exact h.
Rewrite (closed_subst_lemma_msv s' t' u' Nil Y x h2 h1).
Exact (multistep_beta x (juxt (reverse C) (juxt (reverse J) (juxt Y X'))) ms (iht Y Y' y)).
(* ~(y = x') *)
Rewrite (simpl_adbmal_subst_eoss_closed_jsv (abs x s) u Y h h1).
Rewrite <- eoss_juxt.
Rewrite <- eoss_juxt.
Rewrite juxt_ass.
Replace (eos x' (eoss X' (abs x s))) with (eoss (cons x' X') (abs x s)).
2:Reflexivity.
Rewrite <- eoss_juxt.
Rewrite juxt_ass.
Rewrite juxt_ass.
Assert h2 : (scope_subtract Y' X)
             =((neg,(cons x' X')),
               ((reverse (reverse C)),
                ((reverse (reverse J)),(reverse Y')))).
Rewrite rev_rev; Rewrite rev_rev; Exact h.
Pattern 2 Y'; Replace Y' with (juxt Nil Y').
2:Reflexivity.
Rewrite h0 in h2.
Rewrite h0.
Rewrite (closed_subst_lemma_jsv s' t' u' Nil Y x h2 h1).
Exact (multistep_beta x (juxt (reverse C) (juxt (reverse J) (juxt Y (cons x' X')))) ms (iht Y Y' y)).
(* X doesn't jump Y' *)
Elim h; Intros Y'1 h0; Elim h0; Intros Y'2 h1; Elim h1; Clear h h0 h1;
Intros h h0.
Rewrite h0; Rewrite h0 in h.
Rewrite (simpl_adbmal_subst_eoss_open (abs x s) u Y y h); Simpl.
Pattern 2 (juxt (reverse Y'2) Y'1); 
 Replace (juxt (reverse Y'2) Y'1) with (juxt Nil (juxt (reverse Y'2) Y'1)).
2:Reflexivity.
Assert h1 : (scope_subtract (juxt (reverse Y'2) Y'1) X)
             =((pos,Y'1),((reverse X),((nil name),(reverse (reverse Y'2))))).
Rewrite rev_rev; Exact h.
Rewrite (open_subst_lemma s' t' u' Nil Y x y h1).
Exact (multistep_beta x X (ihs Y (cons x Y'1) y) (iht Y (juxt (reverse Y'2) Y'1) y)).

(* ap *)
Intros M1 M2 N1 N2 hM IHM hN IHN X Y x.
Apply multistep_ap.
Exact (IHM X Y x).
Exact (IHN X Y x).

Qed.

End substitution_lemmas.
