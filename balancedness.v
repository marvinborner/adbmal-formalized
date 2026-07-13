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
| scb_var : (X:stack;x:name)(scb X (var x))
| scb_abs : (X:stack;x:name;M:Adbmal)(scb (cons x X) M)->(scb X (abs x M))
| scb_eos : (X:stack;x:name;M:Adbmal)(scb X M)->(scb (cons x X)(eos x M))
| scb_ap  : (X:stack;M,N:Adbmal)(scb X M)->(scb X N)->(scb X (ap M N)).

Definition scope_balanced := (scb (nil name)).

Lemma scb_eoss : (X,Y:stack;t:Adbmal)(scb Y t)->(scb (juxt X Y)(eoss X t)).
Proof.
Intros X Y t h.
Elim X.
Exact h.
Intros x X' ih.
Simpl.
Apply scb_eos.
Exact ih.
Qed.

Lemma scb_abs_inv : (X:stack;x:name;t:Adbmal)
 (scb X (abs x t))->(scb (cons x X) t).
Proof.
Intros X x t H.
Inversion_clear H.
Assumption.
Qed.

Lemma scb_eos_inv : (X:stack;x,y:name;t:Adbmal)
 (scb (cons x X)(eos y t))->y=x/\(scb X t).
Proof.
Intros X x y t H.
Inversion_clear H.
Split.
Reflexivity.
Assumption.
Qed.

Lemma scb_eos_inv2 : (X:stack;x:name;t:Adbmal)
 (scb X (eos x t))->(EX X':stack | X=(cons x X')/\(scb X' t)).
Proof.
Intros X x t h.
Inversion_clear h.
Exists X0.
Split.
Reflexivity.
Assumption.
Qed.

Lemma scb_ap_inv : (X:stack;t,u:Adbmal)
 (scb X (ap t u))->(scb X t)/\(scb X u).
Proof.
Intros X t u H.
Inversion_clear H.
Split; Assumption.
Qed.

Lemma scb_eoss_inv : (X1,X:stack;t:Adbmal)
 (scb X (eoss X1 t)) -> (EX X2 | (juxt X1 X2)=X /\ (scb X2 t)).
Proof.
Induction X1; Simpl.
Intros X t bt.
Exists X.
Split.
Reflexivity.
Exact bt.
Intros a l ih X t bt.
Elim scb_eos_inv2 with 1:=bt.
Intros m h.
Elim h.
Intros h0 h1.
Rewrite h0.
Elim (ih m t h1).
Intros X2 h2.
Elim h2.
Intros h3 h4.
Exists X2.
Split.
Rewrite h3.
Reflexivity.
Exact h4.
Qed.

Lemma scb_eoss_inv2 : 
 (M:Adbmal;X,Y:stack)
  (scb (juxt X Y)(eoss X M))
   ->(scb Y M).
Proof.
NewInduction M; Simpl; Intros X Y h.
Apply scb_var.
Apply scb_abs.
NewInduction X; Simpl in h.
Exact (scb_abs_inv h).
Apply IHX.
Elim (scb_eos_inv h); Intros h0 h1; Exact h1.
NewInduction X; Simpl in h.
Exact h.
Apply IHX.
Elim (scb_eos_inv h); Intros h0 h1; Exact h1.
Apply scb_ap; NewInduction X; Simpl in h.
Elim (scb_ap_inv h); Intros h0 h1; Exact h0.
Apply IHX.
Elim (scb_eos_inv h); Intros h0 h1; Exact h1.
Elim (scb_ap_inv h); Intros h0 h1; Exact h1.
Apply IHX.
Elim (scb_eos_inv h); Intros h0 h1; Exact h1.
Qed.

Fixpoint mk_scb [X:stack;t:Adbmal] : Adbmal :=
Cases t of 
|(var x)    => (var x)
|(abs x t') => (abs x (mk_scb (cons x X) t'))
|(eos x t') => 
   (Fix F {F/1 : stack->Adbmal :=
    [l]Cases l of
    | nil        => (mk_scb (nil name) t')
    |(cons y l') =>
       Cases (eq_dec x y) of 
       |(left _) => (eos x (mk_scb l' t'))
       | _       => (eos y (F l'))
       end
    end} X)
|(ap t1 t2) => (ap (mk_scb X t1)(mk_scb X t2))
end.

Lemma mk_scb_is_scb : (t:Adbmal;X:stack)(scb X (mk_scb X t)).
Proof.
Induction t; Simpl.
Intros n X.
Apply scb_var.
Intros n t' ih X.
Apply scb_abs.
Apply ih.
Intros x t' ih.
Induction X.
Apply ih.
Intros y X' ih2.
Case (eq_dec x y); Intro h.
Rewrite h.
Apply scb_eos.
Apply ih.
Apply scb_eos.
Exact ih2.
Intros t1 ih1 t2 ih2 X.
Apply scb_ap.
Apply ih1.
Apply ih2.
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
| bal_var : (X:stack;x:name)(bal (cons x X)(var x))
| bal_abs : (X:stack;x:name;M:Adbmal)(bal (cons x X) M)->(bal X (abs x M))
| bal_eos : (X:stack;x:name;M:Adbmal)(bal X M)->(bal (cons x X)(eos x M))
| bal_ap  : (X:stack;M,N:Adbmal)(bal X M)->(bal X N)->(bal X (ap M N)).

Definition balanced := (bal (nil name)).

Lemma bal_eoss : (X,Y:stack;t:Adbmal)
 (bal Y t) -> (bal (juxt X Y) (eoss X t)).
Proof.
Intros X Y t h.
Elim X.
Assumption.
Intros a X' ih.
Simpl.
Apply bal_eos.
Exact ih.
Qed.

Lemma bal_var_inv : (X:stack;x:name)
 (bal X (var x)) -> (EX X' | X = (cons x X')).
Proof.
Intros X x H.
Inversion_clear H.
Exists X0.
Reflexivity.
Qed.

Lemma bal_abs_inv : (X:stack;x:name;t:Adbmal)
 (bal X (abs x t))->(bal (cons x X) t).
Proof.
Intros X x t H.
Inversion_clear H.
Assumption.
Qed.

Lemma bal_eos_inv : (X:stack;x,y:name;t:Adbmal)
 (bal (cons x X)(eos y t))->y=x/\(bal X t).
Proof.
Intros X x y t H.
Inversion_clear H.
Split.
Reflexivity.
Assumption.
Qed.

Lemma bal_eos_inv2 :
 (X:stack;x:name;t:Adbmal)
 (bal X (eos x t))
  -> (EX X' | X=(cons x X') /\ (bal X' t)).
Proof.
Intros X x t h.
Inversion_clear h.
Exists X0.
Split.
Reflexivity.
Assumption.
Qed.

Lemma bal_ap_inv : (X:stack;t,u:Adbmal)
 (bal X (ap t u))->(bal X t)/\(bal X u).
Proof.
Intros X t u H.
Inversion_clear H.
Split; Assumption.
Qed.

Lemma bal_eoss_inv : (X1,X:stack;t:Adbmal)
 (bal X (eoss X1 t)) -> (EX X2 | (juxt X1 X2)=X /\ (bal X2 t)).
Proof.
Induction X1; Simpl.
Intros X t bt.
Exists X.
Split.
Reflexivity.
Exact bt.
Intros a l ih X t bt.
Elim bal_eos_inv2 with 1:=bt.
Intros m h.
Elim h.
Intros h0 h1.
Rewrite h0.
Elim (ih m t h1).
Intros X2 h2.
Elim h2.
Intros h3 h4.
Exists X2.
Split.
Rewrite h3.
Reflexivity.
Exact h4.
Qed.

End balancedness.

Lemma bal2scb : (X:stack;M:Adbmal)(bal X M)->(scb X M).
Proof.
NewInduction 1.
Apply scb_var.
Exact (scb_abs IHbal).
Exact (scb_eos x IHbal).
Exact (scb_ap IHbal1 IHbal2).
Qed.
