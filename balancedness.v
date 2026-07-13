Require Export adbmal.

Set Implicit Arguments.

Section scope_balancedness.

(* M is scope-balanced if <>M, defined by
 <X>x                    (* var *)
 <X>\x.M if <xX>M        (* lam *)
 <xX>/x.M if <X>M        (* eos *)
 <X>MN  if <X>M and <X>N (* ap *)
*)

Inductive scb : stack->Adbmal->Prop :=
| scb_var : forall (X:stack) (x:name), scb X (var x)
| scb_abs : forall (X:stack) (x:name) (M:Adbmal),
    scb (cons x X) M -> scb X (abs x M)
| scb_eos : forall (X:stack) (x:name) (M:Adbmal),
    scb X M -> scb (cons x X) (eos x M)
| scb_ap  : forall (X:stack) (M N:Adbmal),
    scb X M -> scb X N -> scb X (ap M N).

Definition scope_balanced := scb nil.

Lemma scb_eoss : forall (X Y:stack) (t:Adbmal),
  scb Y t -> scb (juxt X Y) (eoss X t).
Proof.
intros X Y t h.
induction X as [|x X' ih]; simpl.
- exact h.
- apply scb_eos. exact ih.
Qed.

Lemma scb_abs_inv : forall (X:stack) (x:name) (t:Adbmal),
 (scb X (abs x t))->(scb (cons x X) t).
Proof.
intros X x t H.
inversion H. assumption.
Qed.

Lemma scb_eos_inv : forall (X:stack) (x y:name) (t:Adbmal),
 (scb (cons x X)(eos y t))->y=x/\(scb X t).
Proof.
intros X x y t H.
inversion H. split; [reflexivity | assumption].
Qed.

Lemma scb_eos_inv2 : forall (X:stack) (x:name) (t:Adbmal),
 scb X (eos x t) ->
 exists X':stack, X = cons x X' /\ scb X' t.
Proof.
intros X x t h.
inversion h. exists X0. split; [reflexivity | assumption].
Qed.

Lemma scb_ap_inv : forall (X:stack) (t u:Adbmal),
 (scb X (ap t u))->(scb X t)/\(scb X u).
Proof.
intros X t u H.
inversion H. split; assumption.
Qed.

Lemma scb_eoss_inv : forall (X1 X:stack) (t:Adbmal),
 scb X (eoss X1 t) ->
 exists X2:stack, juxt X1 X2 = X /\ scb X2 t.
Proof.
induction X1 as [|a l ih]; simpl.
- intros X t bt. exists X. split; [reflexivity | exact bt].
- intros X t bt.
  destruct (scb_eos_inv2 bt) as [m [h0 h1]].
  rewrite h0.
  destruct (ih m t h1) as [X2 [h3 h4]].
  exists X2. split.
  + rewrite h3. reflexivity.
  + exact h4.
Qed.

Lemma scb_eoss_inv2 : 
 forall (M:Adbmal) (X Y:stack),
  (scb (juxt X Y)(eoss X M))
   ->(scb Y M).
Proof.
intros M X Y h.
destruct (@scb_eoss_inv X (juxt X Y) M h) as [X2 [h0 h1]].
apply juxt_inj in h0.
subst X2.
exact h1.
Qed.

Fixpoint mk_scb (X:stack) (t:Adbmal) {struct t} : Adbmal :=
match t with
| var x => var x
| abs x t' => abs x (mk_scb (cons x X) t')
| eos x t' =>
    let fix F (l:stack) {struct l} : Adbmal :=
      match l with
      | nil => mk_scb nil t'
      | cons y l' =>
          match eq_dec x y with
          | left _ => eos x (mk_scb l' t')
          | right _ => eos y (F l')
          end
      end
    in F X
| ap t1 t2 => ap (mk_scb X t1) (mk_scb X t2)
end.

Lemma mk_scb_is_scb : forall (t:Adbmal) (X:stack),
  scb X (mk_scb X t).
Proof.
induction t as [n|n t' ih|x t' ih|t1 ih1 t2 ih2]; intros X; simpl.
- apply scb_var.
- apply scb_abs. apply ih.
- induction X as [|y X' ihX]; simpl.
  + apply ih.
  + destruct (eq_dec x y) as [h|h].
    * subst y. apply scb_eos. apply ih.
    * apply scb_eos. exact ihX.
- apply scb_ap.
  + apply ih1.
  + apply ih2.
Qed.

End scope_balancedness.

Section balancedness.

(* M is balanced if <>M, defined by
 <xX>x                   (* var *) (* diff scb: <X>x *)
 <X>\x.M if <xX>M        (* lam *)
 <xX>/x.M if <X>M        (* eos *)
 <X>MN  if <X>M and <X>N (* ap *)
*)

Inductive bal : stack->Adbmal->Prop :=
| bal_var : forall (X:stack) (x:name), bal (cons x X) (var x)
| bal_abs : forall (X:stack) (x:name) (M:Adbmal),
    bal (cons x X) M -> bal X (abs x M)
| bal_eos : forall (X:stack) (x:name) (M:Adbmal),
    bal X M -> bal (cons x X) (eos x M)
| bal_ap  : forall (X:stack) (M N:Adbmal),
    bal X M -> bal X N -> bal X (ap M N).

Definition balanced := bal nil.

Lemma bal_eoss : forall (X Y:stack) (t:Adbmal),
 (bal Y t) -> (bal (juxt X Y) (eoss X t)).
Proof.
intros X Y t h.
induction X as [|a X' ih]; simpl.
- assumption.
- apply bal_eos. exact ih.
Qed.

Lemma bal_var_inv : forall (X:stack) (x:name),
 bal X (var x) -> exists X':stack, X = cons x X'.
Proof.
intros X x H.
inversion H. exists X0. reflexivity.
Qed.

Lemma bal_abs_inv : forall (X:stack) (x:name) (t:Adbmal),
 (bal X (abs x t))->(bal (cons x X) t).
Proof.
intros X x t H.
inversion H. assumption.
Qed.

Lemma bal_eos_inv : forall (X:stack) (x y:name) (t:Adbmal),
 (bal (cons x X)(eos y t))->y=x/\(bal X t).
Proof.
intros X x y t H.
inversion H. split; [reflexivity | assumption].
Qed.

Lemma bal_eos_inv2 :
 forall (X:stack) (x:name) (t:Adbmal),
 (bal X (eos x t))
  -> exists X':stack, X = cons x X' /\ bal X' t.
Proof.
intros X x t h.
inversion h. exists X0. split; [reflexivity | assumption].
Qed.

Lemma bal_ap_inv : forall (X:stack) (t u:Adbmal),
 (bal X (ap t u))->(bal X t)/\(bal X u).
Proof.
intros X t u H.
inversion H. split; assumption.
Qed.

Lemma bal_eoss_inv : forall (X1 X:stack) (t:Adbmal),
 bal X (eoss X1 t) ->
 exists X2:stack, juxt X1 X2 = X /\ bal X2 t.
Proof.
induction X1 as [|a l ih]; simpl.
- intros X t bt. exists X. split; [reflexivity | exact bt].
- intros X t bt.
  destruct (bal_eos_inv2 bt) as [m [h0 h1]].
  rewrite h0.
  destruct (ih m t h1) as [X2 [h3 h4]].
  exists X2. split.
  + rewrite h3. reflexivity.
  + exact h4.
Qed.

End balancedness.

Lemma bal2scb : forall (X:stack) (M:Adbmal), bal X M -> scb X M.
Proof.
intros X M h.
induction h.
- apply scb_var.
- apply scb_abs. exact IHh.
- apply scb_eos. exact IHh.
- apply scb_ap; assumption.
Qed.
