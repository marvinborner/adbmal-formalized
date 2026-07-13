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

Fixpoint adbmal_subst_eoss_aux
  (M N : Adbmal) (x : name) (Z Y J X : stack) {struct X} : Adbmal :=
  match X with
  | nil => adbmal_subst Z Y M x N
  | cons x0 xs =>
      let fix aux (l k : stack) {struct l} : Adbmal :=
        match l with
        | nil =>
            let k' := reverse k in
            match eq_dec x x0 with
            | left _ => eoss k' (eoss Z (eoss xs M))
            | right _ => eoss k' (eoss Z (eos x0 (eoss xs M)))
            end
        | cons y l' =>
            match eq_dec x0 y with
            | left _ =>
                eos x0 (adbmal_subst_eoss_aux M N x Z l' Nil xs)
            | right _ => aux l' (cons y k)
            end
        end
      in aux Y J
  end.

Lemma adbmal_subst_eq_adbmal_subst_eoss_aux :
 forall (M N : Adbmal) (X Y Z : stack) (x : name),
  adbmal_subst Z Y (eoss X M) x N
   = adbmal_subst_eoss_aux M N x Z Y Nil X.
Proof.
induction X; intros Y Z x; simpl.
reflexivity.
assert (h : forall W : stack,
  (let fix aux (l k : stack) {struct l} : Adbmal :=
     match l with
     | nil =>
         match eq_dec x a with
         | left _ => eoss (reverse k) (eoss Z (eoss X M))
         | right _ => eoss (reverse k) (eoss Z (eos a (eoss X M)))
         end
     | cons z l' =>
         match eq_dec a z with
         | left _ => eos a (adbmal_subst Z l' (eoss X M) x N)
         | right _ => aux l' (cons z k)
         end
     end
   in aux Y W)
  =
  (let fix aux (l k : stack) {struct l} : Adbmal :=
     match l with
     | nil =>
         match eq_dec x a with
         | left _ => eoss (reverse k) (eoss Z (eoss X M))
         | right _ => eoss (reverse k) (eoss Z (eos a (eoss X M)))
         end
     | cons y l' =>
         match eq_dec a y with
         | left _ =>
             eos a (adbmal_subst_eoss_aux M N x Z l' (@nil name) X)
         | right _ => aux l' (cons y k)
         end
     end
   in aux Y W)).
induction Y; intro W; simpl.
destruct (eq_dec x a); reflexivity.
destruct (eq_dec a a0) as [h|h].
rewrite IHX; reflexivity.
apply IHY.
apply h.
Qed.

Lemma simpl_adbmal_subst_eoss_aux_closed_msv :
 forall (M N : Adbmal) (Z Y X X' C C' J J' B B' : stack)
   (x x' : name),
  (scope_subtract_rec Y X C J B) = ((neg,(cons x' X')),(C',(J',B')))
   ->(x=x')
    ->(eoss (reverse C) (adbmal_subst_eoss_aux M N x Z Y J X))
       = (eoss (reverse C') (eoss (reverse J') (eoss Z (eoss X' M)))).
Proof.
induction Y as [|a Y IHY]; destruct X as [|n l]; simpl;
  intros X' C C' J J' B B' x x' h h0.
discriminate h.
injection h; intros h1 h2 h3 h4 h5.
rewrite h5; destruct (eq_dec x x') as [h6|h6]; [ clear h6 | elim (h6 h0) ].
rewrite h2; rewrite h3; rewrite h4; reflexivity.
discriminate h.
destruct (eq_dec n a).
replace (eos n (adbmal_subst_eoss_aux M N x Z Y (@nil name) l)) 
 with (eoss (cons n Nil)(adbmal_subst_eoss_aux M N x Z Y (@nil name) l)).
2:reflexivity.
rewrite <- eoss_juxt.
rewrite <- rev_cons_juxt.
rewrite <- juxt_nil_end.
exact (IHY l X' (cons n C) C' Nil J' (cons a B) B' x x' h h0).
exact (IHY (cons n l) X' C C' (cons a J) J' (cons a B) B' x x' h h0).
Qed.

Lemma simpl_adbmal_subst_eoss_closed_msv :
 forall (M N : Adbmal) (Z Y X X' C J B : stack) (x x' : name),
  (scope_subtract Y X) = ((neg,(cons x' X')),(C,(J,B)))
   ->(x=x')
    ->(adbmal_subst Z Y (eoss X M) x N)
       = (eoss (reverse C) (eoss (reverse J) (eoss Z (eoss X' M)))).
Proof.
intros M N Z Y X X' C J B x x' h h0.
rewrite adbmal_subst_eq_adbmal_subst_eoss_aux.
exact (@simpl_adbmal_subst_eoss_aux_closed_msv
  M N Z Y X X' Nil C Nil J Nil B x x' h h0).
Qed.

Lemma simpl_adbmal_subst_eoss_aux_closed_jsv :
 forall (M N : Adbmal) (Z Y X X' C C' J J' B B' : stack)
   (x x' : name),
  (scope_subtract_rec Y X C J B) = ((neg,(cons x' X')),(C',(J',B')))
   ->~(x=x')
    ->(eoss (reverse C) (adbmal_subst_eoss_aux M N x Z Y J X))
       = (eoss (reverse C') (eoss (reverse J') (eoss Z (eos x' (eoss X' M))))).
Proof.
induction Y as [|a Y IHY]; destruct X as [|n l]; simpl;
  intros X' C C' J J' B B' x x' h h0.
discriminate h.
injection h; intros h1 h2 h3 h4 h5.
rewrite h5; destruct (eq_dec x x') as [h6|h6]; [ elim (h0 h6) | clear h6 ].
rewrite h2; rewrite h3; rewrite h4; reflexivity.
discriminate h.
destruct (eq_dec n a).
replace (eos n (adbmal_subst_eoss_aux M N x Z Y (@nil name) l))
 with (eoss (cons n Nil) (adbmal_subst_eoss_aux M N x Z Y (@nil name) l)).
2:reflexivity.
rewrite <- eoss_juxt.
rewrite <- rev_cons_juxt.
rewrite <- juxt_nil_end.
exact (IHY l X' (cons n C) C' Nil J' (cons a B) B' x x' h h0).
exact (IHY (cons n l) X' C C' (cons a J) J' (cons a B) B' x x' h h0).
Qed.

Lemma simpl_adbmal_subst_eoss_closed_jsv :
 forall (M N : Adbmal) (Z Y X X' C J B : stack) (x x' : name),
  (scope_subtract Y X) = ((neg,(cons x' X')),(C,(J,B)))
   ->~(x=x')
    ->(adbmal_subst Z Y (eoss X M) x N)
       = (eoss (reverse C) (eoss (reverse J) (eoss Z (eos x' (eoss X' M))))).
Proof.
intros M N Z Y X X' C J B x x' h h0.
rewrite adbmal_subst_eq_adbmal_subst_eoss_aux.
exact (@simpl_adbmal_subst_eoss_aux_closed_jsv
  M N Z Y X X' Nil C Nil J Nil B x x' h h0).
Qed.

Lemma simpl_adbmal_subst_eoss_aux_open :
 forall (M N : Adbmal) (Z Y Y' X C C' J J' B B' : stack) (x : name),
  (scope_subtract_rec Y X C J B)=((pos,Y'),(C',(J',B')))
   ->(adbmal_subst_eoss_aux M N x Z Y J X)
      = (eoss X (adbmal_subst Z Y' M x N)).
Proof.
induction Y as [|a Y IHY]; destruct X as [|n l]; simpl;
  intros C C' J J' B B' x h.
injection h; intros h1 h2 h3 h4.
rewrite <- h4; reflexivity.
discriminate h.
injection h; intros h1 h2 h3 h4.
rewrite h4; reflexivity.
destruct (eq_dec n a).
apply feq.
apply IHY with (1:=h).
exact (IHY Y' (cons n l) C C' (cons a J) J' (cons a B) B' x h).
Qed.

Lemma simpl_adbmal_subst_eoss_open :
 forall (M N : Adbmal) (Z Y Y' X C J B : stack) (x : name),
  (scope_subtract Y X)=((pos,Y'),(C,(J,B)))
   ->(adbmal_subst Z Y (eoss X M) x N)
      = (eoss X (adbmal_subst Z Y' M x N)).
Proof.
intros M N Z Y Y' X C J B x h.
rewrite adbmal_subst_eq_adbmal_subst_eoss_aux.
exact (@simpl_adbmal_subst_eoss_aux_open
  M N Z Y Y' X Nil C Nil J Nil B x h).
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
 forall (s t u : Adbmal) (Y X1 X2 W Z J : stack) (x y z : name),
  let X1' := reverse X1 in
  let J' := reverse J in
  let Y' := reverse Y in
  (scope_subtract Y (juxt X1 (cons z X2))) = ((neg,(cons z X2)),(X1',(J',Y')))
   ->(y=z)
    ->(adbmal_subst Z (juxt W Y) (adbmal_subst (juxt X1 (cons z X2)) W s x t) y u)
       = (adbmal_subst (juxt X1 (juxt J (juxt Z X2))) W s x (adbmal_subst Z Y t y u)).
Proof.
induction s; intros t u Y X1 X2 W Z J x y z X1' J' Y' h e.

(* var *)
simpl.
destruct (in_dec n W) as [h0|h0]; simpl.
destruct (in_dec n (juxt W Y)) as [h1|h1].
reflexivity.
elim h1; apply in_or_juxt; left; exact h0.
destruct (eq_dec x n) as [h1|h1]; simpl.
apply subst_eoss.
rewrite subst_eoss.
apply feq.
rewrite (@simpl_adbmal_subst_eoss_closed_msv
  (var n) u Z Y (juxt X1 (cons z X2)) X2
  X1' J' Y' y z h e).
rewrite eoss_juxt; rewrite eoss_juxt; rewrite eoss_juxt.
unfold J'; rewrite rev_rev; unfold X1'; rewrite rev_rev; reflexivity.

(* abs *)
simpl; apply feq.
exact (IHs t u Y X1 X2 (cons n W) Z J x y z h e).

(* eos *)
destruct (in_dec n W) as [h0|h0].
(* (In n W) *)
elim (in_split eq_dec n W h0); intros W1 h1; elim h1; intros W2 h2;
elim h2; clear h1 h2; intros h1 h2.
rewrite h1.
rewrite (adbmal_subst_eos_clause1 s t x n
  (juxt X1 (cons z X2)) W1 W2 h2).
rewrite (adbmal_subst_eos_clause1 s (adbmal_subst Z Y t y u) x n
  (juxt X1 (juxt J (juxt Z X2))) W1 W2 h2).
rewrite juxt_ass.
replace (juxt (cons n W2) Y) with (cons n (juxt W2 Y)).
2:reflexivity.
rewrite (adbmal_subst_eos_clause1
  (adbmal_subst (juxt X1 (cons z X2)) W2 s x t) u y n
  Z W1 (juxt W2 Y) h2).
apply feq; exact (IHs t u Y X1 X2 W2 Z J x y z h e).
(* ~(In n W) *)
destruct (eq_dec x n) as [h1|h1].
(* x = n *)
rewrite (adbmal_subst_eos_clause2 s t (juxt X1 (cons z X2)) W h1 h0).
rewrite (adbmal_subst_eos_clause2 s (adbmal_subst Z Y t y u)
  (juxt X1 (juxt J (juxt Z X2))) W h1 h0).
rewrite subst_eoss.
apply feq.
rewrite (@simpl_adbmal_subst_eoss_closed_msv
  s u Z Y (juxt X1 (cons z X2)) X2
  X1' J' Y' y z h e).
unfold X1'; rewrite rev_rev; unfold J'; rewrite rev_rev.
rewrite eoss_juxt; rewrite eoss_juxt; rewrite eoss_juxt; reflexivity.
(* ~(x = n) *)
rewrite (adbmal_subst_eos_clause3 s t (juxt X1 (cons z X2)) W h1 h0).
rewrite (adbmal_subst_eos_clause3 s (adbmal_subst Z Y t y u)
  (juxt X1 (juxt J (juxt Z X2))) W h1 h0).
rewrite subst_eoss.
apply feq.
rewrite (@simpl_adbmal_subst_eoss_closed_msv
  (eos n s) u Z Y (juxt X1 (cons z X2)) X2
  X1' J' Y' y z h e).
unfold X1'; rewrite rev_rev; unfold J'; rewrite rev_rev.
rewrite eoss_juxt; rewrite eoss_juxt; rewrite eoss_juxt; reflexivity.

(* ap *)
simpl.
rewrite (IHs1 t u Y X1 X2 W Z J x y z h e).
rewrite (IHs2 t u Y X1 X2 W Z J x y z h e).
reflexivity.
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
 forall (s t u : Adbmal) (Y X1 X2 W Z J : stack) (x y z : name),
  let X1' := reverse X1 in
  let J' := reverse J in
  let Y' := reverse Y in
  (scope_subtract Y (juxt X1 (cons z X2))) = ((neg,(cons z X2)),(X1',(J',Y')))
   ->~(y=z)
    ->(adbmal_subst Z (juxt W Y) (adbmal_subst (juxt X1 (cons z X2)) W s x t) y u)
       = (adbmal_subst (juxt X1 (juxt J (juxt Z (cons z X2)))) W s x (adbmal_subst Z Y t y u)).
Proof.
induction s; intros t u Y X1 X2 W Z J x y z X1' J' Y' h e.

(* var *)
simpl.
destruct (in_dec n W) as [h0|h0]; simpl.
destruct (in_dec n (juxt W Y)) as [h1|h1].
reflexivity.
elim h1; apply in_or_juxt; left; exact h0.
destruct (eq_dec x n) as [h1|h1]; simpl.
apply subst_eoss.
rewrite subst_eoss.
apply feq.
rewrite (@simpl_adbmal_subst_eoss_closed_jsv
  (var n) u Z Y (juxt X1 (cons z X2)) X2
  X1' J' Y' y z h e).
rewrite eoss_juxt; rewrite eoss_juxt; rewrite eoss_juxt.
unfold J'; rewrite rev_rev; unfold X1'; rewrite rev_rev; reflexivity.

(* abs *)
simpl; apply feq.
exact (IHs t u Y X1 X2 (cons n W) Z J x y z h e).

(* eos *)
destruct (in_dec n W) as [h0|h0].
(* (In n W) *)
elim (in_split eq_dec n W h0); intros W1 h1; elim h1; intros W2 h2;
elim h2; clear h1 h2; intros h1 h2.
rewrite h1.
rewrite (adbmal_subst_eos_clause1 s t x n
  (juxt X1 (cons z X2)) W1 W2 h2).
rewrite (adbmal_subst_eos_clause1 s (adbmal_subst Z Y t y u) x n
  (juxt X1 (juxt J (juxt Z (cons z X2)))) W1 W2 h2).
rewrite juxt_ass.
replace (juxt (cons n W2) Y) with (cons n (juxt W2 Y)).
2:reflexivity.
rewrite (adbmal_subst_eos_clause1
  (adbmal_subst (juxt X1 (cons z X2)) W2 s x t) u y n
  Z W1 (juxt W2 Y) h2).
apply feq; exact (IHs t u Y X1 X2 W2 Z J x y z h e).
(* ~(In n W) *)
destruct (eq_dec x n) as [h1|h1].
(* x = n *)
rewrite (adbmal_subst_eos_clause2 s t (juxt X1 (cons z X2)) W h1 h0).
rewrite (adbmal_subst_eos_clause2 s (adbmal_subst Z Y t y u)
  (juxt X1 (juxt J (juxt Z (cons z X2)))) W h1 h0).
rewrite subst_eoss.
apply feq.
rewrite (@simpl_adbmal_subst_eoss_closed_jsv
  s u Z Y (juxt X1 (cons z X2)) X2
  X1' J' Y' y z h e).
unfold X1'; rewrite rev_rev; unfold J'; rewrite rev_rev.
rewrite eoss_juxt; rewrite eoss_juxt; rewrite eoss_juxt; reflexivity.
(* ~(x = n) *)
rewrite (adbmal_subst_eos_clause3 s t (juxt X1 (cons z X2)) W h1 h0).
rewrite (adbmal_subst_eos_clause3 s (adbmal_subst Z Y t y u)
  (juxt X1 (juxt J (juxt Z (cons z X2)))) W h1 h0).
rewrite subst_eoss.
apply feq.
rewrite (@simpl_adbmal_subst_eoss_closed_jsv
  (eos n s) u Z Y (juxt X1 (cons z X2)) X2
  X1' J' Y' y z h e).
unfold X1'; rewrite rev_rev; unfold J'; rewrite rev_rev.
rewrite eoss_juxt; rewrite eoss_juxt; rewrite eoss_juxt; reflexivity.

(* ap *)
simpl.
rewrite (IHs1 t u Y X1 X2 W Z J x y z h e).
rewrite (IHs2 t u Y X1 X2 W Z J x y z h e).
reflexivity.
Qed.


(** 
  [open_subst_lemma] Open Substitution Lemma.
  [[

  scope_subtract(Y1Y2,X) = (pos, Y2, X', Nil, Y1')
  -> s[X,x:=t,W][Z,y:=u,WY1Y2] = s[Z,y:=u,WxY2][X,x:=t[Z,y:=u,Y1Y2],W]

  ]]
*)

Lemma open_subst_lemma :
 forall (s t u : Adbmal) (X Y1 Y2 W Z : stack) (x y : name),
  let X' := reverse X in
  let Y1' := reverse Y1 in
  (scope_subtract (juxt Y1 Y2) X) = ((pos,Y2),(X',(Nil,Y1')))
   ->(adbmal_subst Z (juxt W (juxt Y1 Y2)) (adbmal_subst X W s x t) y u)
     = (adbmal_subst X W (adbmal_subst Z (juxt W (cons x Y2)) s y u) x 
                              (adbmal_subst Z (juxt Y1 Y2) t y u)).
Proof.
induction s; intros t u X Y1 Y2 W Z x y X' Y1' h.

(* var *)
simpl.
destruct (in_dec n W) as [h0|h0]; simpl.
destruct (in_dec n (juxt W (juxt Y1 Y2))) as [h1|h1]; simpl.
destruct (in_dec n (juxt W (cons x Y2))) as [h2|h2]; simpl.
destruct (in_dec n W) as [h3|h3].
reflexivity.
elim (h3 h0).
elim h2; apply in_or_juxt; left; exact h0.
elim h1; apply in_or_juxt; left; exact h0.
destruct (eq_dec x n) as [h1|h1]; simpl.
destruct (in_dec n (juxt W (cons x Y2))) as [h2|h2]; simpl.
destruct (in_dec n W) as [h3|h3]; simpl.
elim (h0 h3).
destruct (eq_dec x n) as [h4|h4]; simpl.
apply subst_eoss.
elim (h4 h1).
elim h2; apply in_or_juxt; right; left; exact h1.
destruct (in_dec n (juxt W (cons x Y2))) as [h2|h2]; simpl.
destruct (in_dec n W) as [h3|h3]; simpl.
elim (h0 h3).
destruct (eq_dec x n) as [h4|h4]; simpl.
elim (h1 h4).
rewrite subst_eoss.
apply feq.
rewrite (@simpl_adbmal_subst_eoss_open
  (var n) u Z (juxt Y1 Y2) Y2 X X' Nil Y1' y h); simpl.
destruct (in_dec n Y2) as [h5|h5]; simpl.
reflexivity.
elim h5.
elim (in_juxt_or W (cons x Y2) n h2); intro h6.
elim (h0 h6).
elim h6; intro h7.
elim (h4 h7).
exact h7.
destruct (eq_dec y n) as [h3|h3]; simpl.
rewrite subst_eoss.
pattern W at 2; rewrite (juxt_nil_end W).
rewrite eoss_juxt.
rewrite subst_eoss.
apply feq; simpl.
destruct (eq_dec x x) as [h4|h4].
rewrite (@simpl_adbmal_subst_eoss_open
  (var n) u Z (juxt Y1 Y2) Y2 X X' Nil Y1' y h).
simpl.
destruct (in_dec n Y2) as [h5|h5]; simpl.
elim h2; apply in_or_juxt; right; right; exact h5.
destruct (eq_dec y n) as [h6|h6]; simpl.
reflexivity.
elim (h6 h3).
elim h4; reflexivity.
rewrite subst_eoss.
pattern W at 2; rewrite (juxt_nil_end W).
rewrite eoss_juxt; rewrite subst_eoss.
apply feq; simpl.
destruct (eq_dec x x) as [h4|h4]; simpl.
rewrite (@simpl_adbmal_subst_eoss_open
  (var n) u Z (juxt Y1 Y2) Y2 X X' Nil Y1' y h); simpl.
destruct (in_dec n Y2) as [h5|h5]; simpl.
elim h2; apply in_or_juxt; right; right; exact h5.
destruct (eq_dec y n) as [h6|h6]; simpl.
elim (h3 h6).
reflexivity.
elim h4; reflexivity.

(* abs *)
simpl; apply feq.
exact (IHs t u X Y1 Y2 (cons n W) Z x y h).

(* eos *)
destruct (in_dec n W) as [h0|h0].
(* (In n W) *)
elim (in_split eq_dec n W h0); intros W1 h1; elim h1; intros W2 h2;
elim h2; clear h1 h2; intros h1 h2.
rewrite h1.
rewrite (adbmal_subst_eos_clause1 s t x n X W1 W2 h2).
rewrite juxt_ass.
replace (juxt (cons n W2) (juxt Y1 Y2)) with (cons n (juxt W2 (juxt Y1 Y2))).
2:reflexivity.
rewrite (adbmal_subst_eos_clause1 (adbmal_subst X W2 s x t) u y n
  Z W1 (juxt W2 (juxt Y1 Y2)) h2).
rewrite juxt_ass.
replace (juxt (cons n W2) (cons x Y2)) with (cons n (juxt W2 (cons x Y2))).
2:reflexivity.
rewrite (adbmal_subst_eos_clause1 s u y n Z W1
  (juxt W2 (cons x Y2)) h2).
rewrite (adbmal_subst_eos_clause1
  (adbmal_subst Z (juxt W2 (cons x Y2)) s y u)
  (adbmal_subst Z (juxt Y1 Y2) t y u) x n X W1 W2 h2).
apply feq.
apply IHs.
exact h.
(* ~(In n W) *)
destruct (eq_dec x n) as [h1|h1].
(* x = n *)
rewrite (adbmal_subst_eos_clause2 s t X W h1 h0).
rewrite h1.
rewrite (adbmal_subst_eos_clause1 s u y n Z W Y2 h0).
rewrite (adbmal_subst_eos_clause2 (adbmal_subst Z Y2 s y u)
             (adbmal_subst Z (juxt Y1 Y2) t y u) 
             X W (eq_refl n) h0).
rewrite subst_eoss.
apply feq.
exact (@simpl_adbmal_subst_eoss_open
  s u Z (juxt Y1 Y2) Y2 X X' Nil Y1' y h).
(* ~(x = n) *)
rewrite (adbmal_subst_eos_clause3 s t X W h1 h0).
rewrite subst_eoss.
rewrite (@simpl_adbmal_subst_eoss_open
  (eos n s) u Z (juxt Y1 Y2) Y2 X X' Nil Y1' y h).
destruct (in_dec n Y2) as [h2|h2]. (* !? *)
(* (In n Y2) *)
elim (in_split eq_dec n Y2 h2); intros Y2a h3; elim h3; intros Y2b h4;
elim h4; clear h3 h4; intros h3 h4.
rewrite h3.
replace (juxt W (cons x (juxt Y2a (cons n Y2b)))) with (juxt (juxt W (cons x Y2a)) (cons n Y2b)).
assert (h5 : ~(In n (juxt W (cons x Y2a)))).
intro h5; elim (in_juxt_or W (cons x Y2a) n h5); intro h6.
exact (h0 h6).
elim h6; intro h7.
exact (h1 h7).
exact (h4 h7).
rewrite (adbmal_subst_eos_clause1 s u y n Z
  (juxt W (cons x Y2a)) Y2b h5).
rewrite (adbmal_subst_eos_clause3 (adbmal_subst Z Y2b s y u)
             (adbmal_subst Z (juxt Y1 (juxt Y2a (cons n Y2b))) t y u)
             X W h1 h0).
apply feq; apply feq.
exact (adbmal_subst_eos_clause1 s u y n Z Y2a Y2b h4).
rewrite juxt_ass; reflexivity.
(* ~(In n Y2) *)
assert (h3 : ~(In n (juxt W (cons x Y2)))).
intro h3; elim (in_juxt_or W (cons x Y2) n h3); intro h4.
exact (h0 h4).
elim h4; intro h5.
exact (h1 h5).
exact (h2 h5).
destruct (eq_dec y n) as [h4|h4].
(* y = n *)
rewrite (adbmal_subst_eos_clause2 s u Z (juxt W (cons x Y2)) h4 h3).
rewrite eoss_juxt.
pattern W at 2; rewrite (juxt_nil_end W); rewrite subst_eoss.
apply feq.
rewrite (adbmal_subst_eos_clause2 s u Z Y2 h4 h2).
simpl; destruct (eq_dec x x) as [h5|h5]; [ reflexivity | elim h5; reflexivity ].
(* ~(y = n) *)
rewrite (adbmal_subst_eos_clause3 s u Z (juxt W (cons x Y2)) h4 h3).
rewrite eoss_juxt.
pattern W at 2; rewrite (juxt_nil_end W); rewrite subst_eoss.
apply feq.
rewrite (adbmal_subst_eos_clause3 s u Z Y2 h4 h2).
simpl; destruct (eq_dec x x) as [h5|h5]; [ reflexivity | elim h5; reflexivity ].

(* ap *)
simpl.
rewrite (IHs1 t u X Y1 Y2 W Z x y h).
rewrite (IHs2 t u X Y1 Y2 W Z x y h).
reflexivity.
Qed.

(** 
  [multistep_subst_lemma] Multi-step Substitution Lemma.
  [[

   t==>t' -> u==>u' -> t[X,x:=u,Y]==>t'[X,x:=u',Y]

  ]]
*)

Lemma multistep_subst_lemma : forall t t' u u' : Adbmal,
 multistep t t'
   ->(multistep u u')
    -> forall (X Y : stack) (x : name),
      (multistep (adbmal_subst X Y t x u)(adbmal_subst X Y t' x u')).
Proof.
intros t t' u u' mt mu.
elim mt; clear mt t t'; simpl.

(* var *)
intros y X Y x.
destruct (in_dec y Y) as [h|h].
apply multistep_var.
destruct (eq_dec x y) as [h0|h0].
apply multistep_eoss.
exact mu.
apply multistep_refl.

(* abs *)
intros t t' y mt ih X Y x.
apply multistep_abs.
exact (ih X (cons y Y) x).

(* eos *)
intros t t' y mt ih X Y x.
set (aux := fun t u =>
  let fix go (l k : stack) {struct l} : Adbmal :=
    match l with
    | nil =>
        match eq_dec x y with
        | left _ => eoss (reverse k) (eoss X t)
        | right _ => eoss (reverse k) (eoss X (eos y t))
        end
    | cons z l' =>
        match eq_dec y z with
        | left _ => eos y (adbmal_subst X l' t x u)
        | right _ => go l' (cons z k)
        end
    end
  in go).
fold (aux t u).
fold (aux t' u').
assert (h : forall Z : stack,
  multistep (aux t u Y Z) (aux t' u' Y Z)).
induction Y; intro Z; simpl.
destruct (eq_dec x y) as [h0|h0]; apply multistep_eoss; apply multistep_eoss; 
 [ exact mt | apply multistep_eos; exact mt ].
destruct (eq_dec y a) as [h0|h0].
apply multistep_eos; apply ih.
apply IHY.
apply h.

(* beta *)
intros s s' t t' x X ms ihs mt iht Y Y' y.
elim (scope_subtract_dec X Y'); intro h.
(* X scope_subtract Y' *)
elim h; intros x' h0; elim h0; intros X' h1; elim h1; intros C h2; elim h2; intros J h3;
 elim h3; clear h h0 h1 h2 h3; intros h h0.
destruct (eq_dec y x') as [h1|h1].
(* y = x' *)
rewrite (@simpl_adbmal_subst_eoss_closed_msv
  (abs x s) u Y Y' X X' C J (reverse Y')
  y x' h h1).
rewrite <- eoss_juxt; rewrite <- eoss_juxt; rewrite <- eoss_juxt.
rewrite juxt_ass; rewrite juxt_ass.
rewrite h0.
rewrite h0 in h.
pattern Y' at 2; replace Y' with (juxt Nil Y').
2:reflexivity.
assert (h2 : (scope_subtract Y' (juxt (reverse C) (cons x' X')))
             =((neg,(cons x' X')),
               ((reverse (reverse C)),
                ((reverse (reverse J)),(reverse Y'))))).
rewrite rev_rev; rewrite rev_rev; exact h.
rewrite (@closed_subst_lemma_msv
  s' t' u' Y' (reverse C) X' Nil Y (reverse J) x y x' h2 h1).
exact (multistep_beta x (juxt (reverse C) (juxt (reverse J) (juxt Y X'))) ms (iht Y Y' y)).
(* ~(y = x') *)
rewrite (@simpl_adbmal_subst_eoss_closed_jsv
  (abs x s) u Y Y' X X' C J (reverse Y')
  y x' h h1).
rewrite <- eoss_juxt.
rewrite <- eoss_juxt.
rewrite juxt_ass.
replace (eos x' (eoss X' (abs x s))) with (eoss (cons x' X') (abs x s)).
2:reflexivity.
rewrite <- eoss_juxt.
rewrite juxt_ass.
rewrite juxt_ass.
assert (h2 : (scope_subtract Y' X)
             =((neg,(cons x' X')),
               ((reverse (reverse C)),
                ((reverse (reverse J)),(reverse Y'))))).
rewrite rev_rev; rewrite rev_rev; exact h.
pattern Y' at 2; replace Y' with (juxt Nil Y').
2:reflexivity.
rewrite h0 in h2.
rewrite h0.
rewrite (@closed_subst_lemma_jsv
  s' t' u' Y' (reverse C) X' Nil Y (reverse J) x y x' h2 h1).
exact (multistep_beta x (juxt (reverse C) (juxt (reverse J) (juxt Y (cons x' X')))) ms (iht Y Y' y)).
(* X doesn't jump Y' *)
elim h; intros Y'1 h0; elim h0; intros Y'2 h1; elim h1; clear h h0 h1;
intros h h0.
rewrite h0; rewrite h0 in h.
rewrite (@simpl_adbmal_subst_eoss_open
  (abs x s) u Y (juxt (reverse Y'2) Y'1) Y'1 X
  (reverse X) Nil Y'2 y h); simpl.
pattern (juxt (reverse Y'2) Y'1) at 2;
 replace (juxt (reverse Y'2) Y'1) with (juxt Nil (juxt (reverse Y'2) Y'1)).
2:reflexivity.
assert (h1 : (scope_subtract (juxt (reverse Y'2) Y'1) X)
             =((pos,Y'1),((reverse X),((@nil name),(reverse (reverse Y'2)))))).
rewrite rev_rev; exact h.
rewrite (@open_subst_lemma
  s' t' u' X (reverse Y'2) Y'1 Nil Y x y h1).
exact (multistep_beta x X (ihs Y (cons x Y'1) y) (iht Y (juxt (reverse Y'2) Y'1) y)).

(* ap *)
intros M1 M2 N1 N2 hM IHM hN IHN X Y x.
apply multistep_ap.
exact (IHM X Y x).
exact (IHN X Y x).

Qed.

End substitution_lemmas.
