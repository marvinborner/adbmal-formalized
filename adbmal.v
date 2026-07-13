Require Export name.

Infix 4 "-->" adbmal_beta .
Infix 4 "==>" multistep .

Set Implicit Arguments.

(** Definition of adbmal-terms and substitution, adbmal_beta, multistep and
    unary contexts for adbmal-terms
*)

Section adbmal_calculus.

Inductive Adbmal : Set :=
| var : name -> Adbmal              (** variable *)
| abs : name -> Adbmal -> Adbmal    (** abstraction *)
| eos : name -> Adbmal -> Adbmal    (** end-of-scope *)
| ap  : Adbmal -> Adbmal -> Adbmal. (** application *)

(**
  Unary contexts (built from abs,eos,ap).
*)

Inductive cxt : (Adbmal->Adbmal)->Prop :=
| cxt_id  : (cxt [t]t)
| cxt_comp: (c,c':Adbmal->Adbmal)(cxt c)->(cxt c')->(cxt [t](c (c' t)))
| cxt_abs : (x:name)(cxt (abs x))
| cxt_eos : (x:name)(cxt (eos x))
| cxt_apl : (u:Adbmal)(cxt [t](ap t u))
| cxt_apr : (t:Adbmal)(cxt [u](ap t u)).

(** 
  Vectors of end-of-scopes.
*)

Fixpoint eoss [l:stack] : Adbmal->Adbmal :=
[t] Cases l of
| nil    => t
|(cons x l') => (eos x (eoss l' t))
end.

Lemma cxt_eoss : (X:stack)(cxt (eoss X)).
Proof.
Induction X; Simpl.
Exact cxt_id.
Intros x X' ih.
Exact (cxt_comp (cxt_eos x) ih).
Qed.

Definition feq : (f:(Adbmal->Adbmal);x,y:Adbmal)x=y->(f x)=(f y) := (f_equal Adbmal Adbmal).

Lemma eoss_juxt : (X,Y:stack;M:Adbmal)(eoss (juxt X Y) M)=(eoss X (eoss Y M)).
Proof.
Intros X Y M.
Elim X.
Reflexivity.
Intros a X' IH.
Simpl.
Apply feq.
Exact IH.
Qed.

(** 
  Substitution [M[X,x:=N,Y]] defined by [(adbmal_subst X Y M x N)].
  Note that scope_subtract _within_ the body [M] remain untouched; 
  balance only if necessary.
*)

Fixpoint adbmal_subst [X,Y:stack;M:Adbmal] : name->Adbmal->Adbmal :=
[x;N] Cases M of
|(var y) => Cases (in_dec y Y) of
       |(left _)(*In y Y*) => (var y)
       | _     (*~In y Y*) => Cases (eq_dec x y) of
          |(left _)(*x=y*) => (eoss Y N)
          | _     (*~x=y*) => (eoss Y (eoss X (var y)))
           end
       end
|(abs y m) => (abs y (adbmal_subst X (cons y Y) m x N))
|(eos y m) => 
 (Fix aux {aux/1 : stack->stack->Adbmal :=
  [l,k] Cases l of
        | nil => [k':=(reverse k)]
          Cases (eq_dec x y) of
          |(left _)(*x=y*) => (eoss k' (eoss X m))
          | _     (*~x=y*) => (eoss k' (eoss X (eos y m)))
          end
        |(cons z l') =>
          Cases (eq_dec y z) of
          |(left _)(*y=z*) => (eos y (adbmal_subst X l' m x N))
          | _     (*~y=z*) => (aux l' (cons z k))
          end
        end } Y Nil)
|(ap m1 m2) => (ap (adbmal_subst X Y m1 x N)(adbmal_subst X Y m2 x N))
end.

(**
  We prove more readable and more convenient-to-work-with 
  substitution clauses for the [eos]-cases:
  [adbmal_subst_eos_clause1], [adbmal_subst_eos_clause2] 
  and [adbmal_subst_eos_clause3].
*)

Lemma adbmal_subst_eos_clause1_aux :
 (M,N:Adbmal;x,y:name;X,Y,Y',Z:stack)
  ~(In y Y)
   ->
   (Fix aux
      {aux [l:stack] : stack->Adbmal :=
         [k:stack]
          Cases l of
            nil => 
             Cases (eq_dec x y) of
               (left _) => (eoss (reverse k) (eoss X M))
             | (right _) => (eoss (reverse k) (eoss X (eos y M)))
             end
          | (cons z l') => 
             Cases (eq_dec y z) of
               (left _) => (eos y (adbmal_subst X l' M x N))
             | (right _) => (aux l' (cons z k))
             end
          end} (juxt Y (cons y Y')) Z)
    =(eos y (adbmal_subst X Y' M x N)).
Proof.
NewInduction Y; Intros Y' Z h; Simpl.
Case (eq_dec y y); Intro h0.
Reflexivity.
Elim h0; Reflexivity.
Case (eq_dec y a); Intro h0.
Elim h; Left; Symmetry; Exact h0.
Apply IHY.
Intro h1; Apply h; Right; Exact h1.
Qed.

Lemma adbmal_subst_eos_clause1 :
 (M,N:Adbmal;x,y:name;X,Y,Y':stack)
  ~(In y Y)
   ->(adbmal_subst X (juxt Y (cons y Y')) (eos y M) x N) 
     = (eos y (adbmal_subst X Y' M x N)).
Proof.
Intros M N x y X Y Y' h; Simpl.
Exact (adbmal_subst_eos_clause1_aux M N x X Y' Nil h).
Qed.

Lemma adbmal_subst_eos_clause2_aux :
 (M,N:Adbmal;x,y:name;X,Y:stack)
  ~(In y Y)
   ->(Z:stack)
  (Fix aux
      {aux [l:stack] : stack->Adbmal :=
         [k:stack]
          Cases l of
            nil => (eoss (reverse k) (eoss X M))
          | (cons z l') => 
             Cases (eq_dec y z) of
               (left _) => (eos y (adbmal_subst X l' M x N))
             | (right _) => (aux l' (cons z k))
             end
          end} Y Z)=(eoss (reverse Z)(eoss Y (eoss X M))).
Proof.
NewInduction Y; Intros h Z; Simpl.
Reflexivity.
Case (eq_dec y a); Intro h0; Simpl.
Elim h; Left; Symmetry; Exact h0.
Replace (eoss (reverse Z) (eos a (eoss Y (eoss X M))))
 with (eoss (reverse (cons a Z)) (eoss Y (eoss X M))).
Apply IHY.
Intro h1; Apply h; Right; Exact h1.
Rewrite <- eoss_juxt.
Rewrite rev_cons_juxt.
Rewrite eoss_juxt; Reflexivity.
Qed.

Lemma adbmal_subst_eos_clause2 :
 (M,N:Adbmal;x,y:name;X,Y:stack)
  x=y
   ->~(In y Y)
    ->(adbmal_subst X Y (eos y M) x N) = (eoss Y (eoss X M)).
Proof.
Intros M N x y X Y h h0; Simpl.
Case (eq_dec x y); Intro h1; Simpl.
Exact (adbmal_subst_eos_clause2_aux M N x X h0 Nil).
Elim (h1 h).
Qed.

Lemma adbmal_subst_eos_clause3_aux : 
 (M,N:Adbmal;x,y:name;X,Y:stack)
  ~(In y Y)
   ->(Z:stack)
   (Fix aux
      {aux [l:stack] : stack->Adbmal :=
         [k:stack]
          Cases l of
            nil => (eoss (reverse k) (eoss X (eos y M)))
          | (cons z l') => 
             Cases (eq_dec y z) of
               (left _) => (eos y (adbmal_subst X l' M x N))
             | (right _) => (aux l' (cons z k))
             end
          end} Y Z)=(eoss (reverse Z)(eoss Y (eoss X (eos y M)))).
Proof.
NewInduction Y; Simpl.
Reflexivity.
Intros h.
Case (eq_dec y a); Intro h0.
Elim h; Left; Symmetry; Exact h0.
Intro Z.
Replace (eoss (reverse Z) (eos a (eoss Y (eoss X (eos y M)))))
 with (eoss (reverse (cons a Z)) (eoss Y (eoss X (eos y M)))).
Apply IHY.
Intro h1; Apply h; Right; Exact h1.
Rewrite <- eoss_juxt.
Rewrite rev_cons_juxt.
Rewrite eoss_juxt.
Reflexivity.
Qed.

Lemma adbmal_subst_eos_clause3 : 
 (M,N:Adbmal;x,y:name;X,Y:stack)
  ~x=y
   ->~(In y Y)
    ->(adbmal_subst X Y (eos y M) x N) = (eoss Y (eoss X (eos y M))).
Proof.
Intros M N x y X Y h h0; Simpl.
Case (eq_dec x y); Intro h1.
Elim (h h1).
Simpl.
Exact (adbmal_subst_eos_clause3_aux M N x X h0 Nil).
Qed.

(** 
  (One steps) beta reduction [-->] defined as 
  the compatible closure of the adbmal_beta_rule. 
*)

Inductive adbmal_beta : Adbmal->Adbmal->Prop :=
| beta_abs : (M,N:Adbmal;x:name) M-->N -> (abs x M)-->(abs x N)
| beta_eos : (M,N:Adbmal;x:name) M-->N -> (eos x M)-->(eos x N)
| beta_apl : (M,M',N:Adbmal) M-->M' -> (ap M N)-->(ap M' N)
| beta_apr : (M,M',N:Adbmal) M-->M' -> (ap N M)-->(ap N M')
| beta_rule: (M,N:Adbmal;x:name;X:stack)
              (ap (eoss X (abs x M)) N)-->(adbmal_subst X (nil name) M x N).

(** 
  Parallel beta reduction [==>] defined as 
  the multi-step closure of adbmal_beta_rule. 
*)

Inductive multistep : Adbmal->Adbmal->Prop :=
| multistep_var : (x:name)(var x)==>(var x)
| multistep_abs : (M,N:Adbmal;x:name) M==>N -> (abs x M)==>(abs x N)
| multistep_eos : (M,N:Adbmal;x:name) M==>N -> (eos x M)==>(eos x N)
| multistep_beta: (M1,M2,N1,N2:Adbmal;x:name;X:stack)
      M1==>M2 -> N1==>N2 ->
       (ap (eoss X (abs x M1)) N1)==>(adbmal_subst X (nil name) M2 x N2)
| multistep_ap : (M1,M2,N1,N2:Adbmal) M1==>M2 -> N1==>N2 -> (ap M1 N1)==>(ap M2 N2).


(** [(/Y.M)[X,x:=N,YY'] = /Y[X,x:=N,Y']]*)

Lemma subst_eoss :
 (M,N:Adbmal;X,Y,Y':stack;x:name)
 (adbmal_subst X (juxt Y Y') (eoss Y M) x N)=(eoss Y (adbmal_subst X Y' M x N)).
Proof.
Induction Y.
Reflexivity.
Intros a Y1 IH Y' x.
Simpl.
Case (eq_dec a a); Intro H.
Apply feq.
Apply IH.
Apply False_ind.
Apply H.
Reflexivity.
Qed.

Lemma multistep_refl : (t:Adbmal)(multistep t t).
Proof.
Induction t; Clear t.
Exact multistep_var.
Intros x t ih.
Apply multistep_abs.
Exact ih.
Intros x t ih.
Apply multistep_eos.
Exact ih.
Intros t1 ih1 t2 ih2.
Apply multistep_ap.
Exact ih1.
Exact ih2.
Qed.

Lemma multistep_eoss : (M,N:Adbmal; X:stack)
 (multistep M N)->(multistep (eoss X M) (eoss X N)).
Proof.
Intros M N X h.
Elim X; Simpl.
Exact h.
Intros x X' ih.
Apply multistep_eos.
Exact ih.
Qed.

Lemma multistep_var_inv : (x:name;t:Adbmal)(multistep (var x) t)->t=(var x).
Proof.
Intros x t h.
Inversion_clear h.
Reflexivity.
Qed.

Lemma multistep_abs_inv : (x:name;t,u:Adbmal)
 (multistep (abs x t) u)->(EX t' | u=(abs x t')/\(multistep t t')).
Proof.
Intros x t u h.
Inversion_clear h.
Exists N.
Split.
Reflexivity.
Exact H.
Qed.

Lemma multistep_eos_inv : (x:name;t,u:Adbmal)
 (multistep (eos x t) u)->(EX t' | u=(eos x t')/\(multistep t t')).
Proof.
Intros x t u h.
Inversion_clear h.
Exists N.
Split.
Reflexivity.
Exact H.
Qed.

Lemma multistep_eoss_inv : (X:stack;t,u:Adbmal)
 (multistep (eoss X t) u)->(EX t' | u=(eoss X t')/\(multistep t t')).
Proof.
Induction X; Simpl.
Intros t u h; Exists u; Split; [ Reflexivity | Exact h ].
Intros x X' ih t u h.
Elim (multistep_eos_inv h); Intros v h0; Elim h0; Clear h0; Intros h1 h2.
Rewrite h1.
Elim (ih t v h2); Intros t' h3; Elim h3; Clear h3; Intros h3 h4.
Exists t'.
Split.
Apply feq.
Exact h3.
Exact h4.
Qed.

Lemma eoss_abs_inj : (X,X':stack;x,x':name;t,t':Adbmal)
 (eoss X (abs x t))=(eoss X' (abs x' t'))->X=X'/\x=x'/\t=t'.
Proof.
Induction X; Simpl.
Destruct X'; Simpl.
Intros x x' t t' h.
Injection h; Intros h0 h1. Rewrite h0; Rewrite h1.
Split; [ Reflexivity | Split; Reflexivity ].
Intros a l x x' t t' h.
Discriminate h.
Intros a l ih.
Destruct X'; Simpl.
Intros x x' t t' h.
Discriminate h.
Intros a' l' x x' t t' h.
Injection h; Intros h0 h1.
Elim (ih l' x x' t t' h0); Intros h2 h3; Elim h3; Clear h3; Intros h3 h4.
Rewrite h1.
Rewrite h2.
Rewrite h3.
Rewrite h4.
Split; [ Reflexivity | Split; Reflexivity ].
Qed.

Lemma eoss_inj2 : (X:stack;t,t':Adbmal)(eoss X t)=(eoss X t')->t=t'.
Proof.
Induction X; Simpl.
Trivial.
Intros x X' ih t t' h.
Injection h; Intro h0; Exact (ih t t' h0).
Qed.

End adbmal_calculus.
