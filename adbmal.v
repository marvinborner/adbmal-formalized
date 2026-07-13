Require Export name.

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
| cxt_id  : cxt (fun t => t)
| cxt_comp: forall c c':Adbmal->Adbmal,
    cxt c -> cxt c' -> cxt (fun t => c (c' t))
| cxt_abs : forall x:name, cxt (abs x)
| cxt_eos : forall x:name, cxt (eos x)
| cxt_apl : forall u:Adbmal, cxt (fun t => ap t u)
| cxt_apr : forall t:Adbmal, cxt (fun u => ap t u).

(** 
  Vectors of end-of-scopes.
*)

Fixpoint eoss (l:stack) (t:Adbmal) : Adbmal :=
match l with
| nil => t
| cons x l' => eos x (eoss l' t)
end.

Lemma cxt_eoss : forall X:stack, cxt (eoss X).
Proof.
induction X as [|x X' ih]; simpl.
- exact cxt_id.
- exact (cxt_comp (cxt_eos x) ih).
Qed.

Definition feq : forall (f:Adbmal->Adbmal) (x y:Adbmal),
  x = y -> f x = f y := @f_equal Adbmal Adbmal.

Lemma eoss_juxt : forall (X Y:stack) (M:Adbmal),
  eoss (juxt X Y) M = eoss X (eoss Y M).
Proof.
intros X Y M.
induction X as [|a X' IH]; simpl.
- reflexivity.
- apply feq. exact IH.
Qed.

(** 
  Substitution [M[X,x:=N,Y]] defined by [(adbmal_subst X Y M x N)].
  Note that scope_subtract _within_ the body [M] remain untouched; 
  balance only if necessary.
*)

Fixpoint adbmal_subst (X Y:stack) (M:Adbmal) (x:name) (N:Adbmal) : Adbmal :=
match M with
| var y =>
    match in_dec y Y with
    | left _ (*In y Y*) => var y
    | right _ (*~In y Y*) =>
        match eq_dec x y with
        | left _ (*x=y*) => eoss Y N
        | right _ (*~x=y*) => eoss Y (eoss X (var y))
        end
    end
| abs y m => abs y (adbmal_subst X (cons y Y) m x N)
| eos y m =>
    let fix aux (l k:stack) {struct l} : Adbmal :=
      match l with
      | nil =>
          let k' := reverse k in
          match eq_dec x y with
          | left _ (*x=y*) => eoss k' (eoss X m)
          | right _ (*~x=y*) => eoss k' (eoss X (eos y m))
          end
      | cons z l' =>
          match eq_dec y z with
          | left _ (*y=z*) => eos y (adbmal_subst X l' m x N)
          | right _ (*~y=z*) => aux l' (cons z k)
          end
      end
    in aux Y nil
| ap m1 m2 => ap (adbmal_subst X Y m1 x N)
                  (adbmal_subst X Y m2 x N)
end.

(**
  We prove more readable and more convenient-to-work-with 
  substitution clauses for the [eos]-cases:
  [adbmal_subst_eos_clause1], [adbmal_subst_eos_clause2] 
  and [adbmal_subst_eos_clause3].
*)

Lemma adbmal_subst_eos_clause1_aux :
 forall (M N:Adbmal) (x y:name) (X Y Y' Z:stack),
  ~(In y Y)
   ->
   (let fix aux (l:stack) (k:stack) {struct l} : Adbmal :=
      match l with
      | nil =>
          match eq_dec x y with
          | left _ => eoss (reverse k) (eoss X M)
          | right _ => eoss (reverse k) (eoss X (eos y M))
          end
      | cons z l' =>
          match eq_dec y z with
          | left _ => eos y (adbmal_subst X l' M x N)
          | right _ => aux l' (cons z k)
          end
      end
    in aux (juxt Y (cons y Y')) Z)
    =(eos y (adbmal_subst X Y' M x N)).
Proof.
intros M N x y X Y.
induction Y as [|a Y IHY]; intros Y' Z h; simpl.
- destruct (eq_dec y y) as [_|h0].
  + reflexivity.
  + exfalso; apply h0; reflexivity.
- destruct (eq_dec y a) as [h0|h0].
  + exfalso. apply h. left. symmetry. exact h0.
  + apply IHY. intro h1. apply h. right. exact h1.
Qed.

Lemma adbmal_subst_eos_clause1 :
 forall (M N:Adbmal) (x y:name) (X Y Y':stack),
  ~(In y Y)
   ->(adbmal_subst X (juxt Y (cons y Y')) (eos y M) x N) 
     = (eos y (adbmal_subst X Y' M x N)).
Proof.
intros M N x y X Y Y' h; simpl.
exact (adbmal_subst_eos_clause1_aux M N x y X Y Y' nil h).
Qed.

Lemma adbmal_subst_eos_clause2_aux :
 forall (M N:Adbmal) (x y:name) (X Y:stack),
  ~(In y Y)
   -> forall Z:stack,
  (let fix aux (l:stack) (k:stack) {struct l} : Adbmal :=
     match l with
     | nil => eoss (reverse k) (eoss X M)
     | cons z l' =>
         match eq_dec y z with
         | left _ => eos y (adbmal_subst X l' M x N)
         | right _ => aux l' (cons z k)
         end
     end
   in aux Y Z) = eoss (reverse Z) (eoss Y (eoss X M)).
Proof.
intros M N x y X Y.
induction Y as [|a Y IHY]; intros h Z; simpl.
- reflexivity.
- destruct (eq_dec y a) as [h0|h0]; simpl.
  + exfalso. apply h. left. symmetry. exact h0.
  + replace (eoss (reverse Z) (eos a (eoss Y (eoss X M))))
      with (eoss (reverse (cons a Z)) (eoss Y (eoss X M))).
    * apply IHY. intro h1. apply h. right. exact h1.
    * rewrite <- eoss_juxt.
      rewrite rev_cons_juxt.
      rewrite eoss_juxt. reflexivity.
Qed.

Lemma adbmal_subst_eos_clause2 :
 forall (M N:Adbmal) (x y:name) (X Y:stack),
  x=y
   ->~(In y Y)
    ->(adbmal_subst X Y (eos y M) x N) = (eoss Y (eoss X M)).
Proof.
intros M N x y X Y h h0; simpl.
destruct (eq_dec x y) as [h1|h1]; simpl.
- exact (adbmal_subst_eos_clause2_aux M N x y X Y h0 nil).
- exfalso. exact (h1 h).
Qed.

Lemma adbmal_subst_eos_clause3_aux : 
 forall (M N:Adbmal) (x y:name) (X Y:stack),
  ~(In y Y)
   -> forall Z:stack,
   (let fix aux (l:stack) (k:stack) {struct l} : Adbmal :=
      match l with
      | nil => eoss (reverse k) (eoss X (eos y M))
      | cons z l' =>
          match eq_dec y z with
          | left _ => eos y (adbmal_subst X l' M x N)
          | right _ => aux l' (cons z k)
          end
      end
    in aux Y Z) = eoss (reverse Z) (eoss Y (eoss X (eos y M))).
Proof.
intros M N x y X Y.
induction Y as [|a Y IHY]; intros h Z; simpl.
- reflexivity.
- destruct (eq_dec y a) as [h0|h0].
  + exfalso. apply h. left. symmetry. exact h0.
  + replace (eoss (reverse Z) (eos a (eoss Y (eoss X (eos y M)))))
      with (eoss (reverse (cons a Z)) (eoss Y (eoss X (eos y M)))).
    * apply IHY. intro h1. apply h. right. exact h1.
    * rewrite <- eoss_juxt.
      rewrite rev_cons_juxt.
      rewrite eoss_juxt.
      reflexivity.
Qed.

Lemma adbmal_subst_eos_clause3 : 
 forall (M N:Adbmal) (x y:name) (X Y:stack),
  ~x=y
   ->~(In y Y)
    ->(adbmal_subst X Y (eos y M) x N) = (eoss Y (eoss X (eos y M))).
Proof.
intros M N x y X Y h h0; simpl.
destruct (eq_dec x y) as [h1|h1].
- exfalso. exact (h h1).
- simpl. exact (adbmal_subst_eos_clause3_aux M N x y X Y h0 nil).
Qed.

(** 
  (One steps) beta reduction [-->] defined as 
  the compatible closure of the adbmal_beta_rule. 
*)

Inductive adbmal_beta : Adbmal->Adbmal->Prop :=
| beta_abs : forall (M N:Adbmal) (x:name),
    adbmal_beta M N -> adbmal_beta (abs x M) (abs x N)
| beta_eos : forall (M N:Adbmal) (x:name),
    adbmal_beta M N -> adbmal_beta (eos x M) (eos x N)
| beta_apl : forall M M' N:Adbmal,
    adbmal_beta M M' -> adbmal_beta (ap M N) (ap M' N)
| beta_apr : forall M M' N:Adbmal,
    adbmal_beta M M' -> adbmal_beta (ap N M) (ap N M')
| beta_rule: forall (M N:Adbmal) (x:name) (X:stack),
    adbmal_beta (ap (eoss X (abs x M)) N)
                (adbmal_subst X nil M x N).

Infix "-->" := adbmal_beta (at level 40).

(** 
  Parallel beta reduction [==>] defined as 
  the multi-step closure of adbmal_beta_rule. 
*)

Inductive multistep : Adbmal->Adbmal->Prop :=
| multistep_var : forall x:name, multistep (var x) (var x)
| multistep_abs : forall (M N:Adbmal) (x:name),
    multistep M N -> multistep (abs x M) (abs x N)
| multistep_eos : forall (M N:Adbmal) (x:name),
    multistep M N -> multistep (eos x M) (eos x N)
| multistep_beta: forall (M1 M2 N1 N2:Adbmal) (x:name) (X:stack),
    multistep M1 M2 -> multistep N1 N2 ->
    multistep (ap (eoss X (abs x M1)) N1)
              (adbmal_subst X nil M2 x N2)
| multistep_ap : forall M1 M2 N1 N2:Adbmal,
    multistep M1 M2 -> multistep N1 N2 ->
    multistep (ap M1 N1) (ap M2 N2).

Infix "==>" := multistep (at level 40).


(** [(/Y.M)[X,x:=N,YY'] = /Y[X,x:=N,Y']]*)

Lemma subst_eoss :
 forall (M N:Adbmal) (X Y Y':stack) (x:name),
 (adbmal_subst X (juxt Y Y') (eoss Y M) x N)=(eoss Y (adbmal_subst X Y' M x N)).
Proof.
intros M N X Y.
induction Y as [|a Y1 IH]; intros Y' x; simpl.
- reflexivity.
- destruct (eq_dec a a) as [_|H].
  + apply feq. apply IH.
  + exfalso. apply H. reflexivity.
Qed.

Lemma multistep_refl : forall t:Adbmal, multistep t t.
Proof.
induction t as [x|x t ih|x t ih|t1 ih1 t2 ih2].
- exact (multistep_var x).
- apply multistep_abs. exact ih.
- apply multistep_eos. exact ih.
- apply multistep_ap; assumption.
Qed.

Lemma multistep_eoss : forall (M N:Adbmal) (X:stack),
 (multistep M N)->(multistep (eoss X M) (eoss X N)).
Proof.
intros M N X h.
induction X as [|x X' ih]; simpl.
- exact h.
- apply multistep_eos. exact ih.
Qed.

Lemma multistep_var_inv : forall (x:name) (t:Adbmal),
  multistep (var x) t -> t = var x.
Proof.
intros x t h.
inversion h.
reflexivity.
Qed.

Lemma multistep_abs_inv : forall (x:name) (t u:Adbmal),
 multistep (abs x t) u ->
 exists t':Adbmal, u = abs x t' /\ multistep t t'.
Proof.
intros x t u h.
inversion h; subst.
exists N. split; [reflexivity | assumption].
Qed.

Lemma multistep_eos_inv : forall (x:name) (t u:Adbmal),
 multistep (eos x t) u ->
 exists t':Adbmal, u = eos x t' /\ multistep t t'.
Proof.
intros x t u h.
inversion h; subst.
exists N. split; [reflexivity | assumption].
Qed.

Lemma multistep_eoss_inv : forall (X:stack) (t u:Adbmal),
 multistep (eoss X t) u ->
 exists t':Adbmal, u = eoss X t' /\ multistep t t'.
Proof.
induction X as [|x X' ih]; simpl.
- intros t u h. exists u. split; [reflexivity | exact h].
- intros t u h.
  destruct (multistep_eos_inv h) as [v [h1 h2]].
  rewrite h1.
  destruct (ih t v h2) as [t' [h3 h4]].
  exists t'. split.
  + apply feq. exact h3.
  + exact h4.
Qed.

Lemma eoss_abs_inj : forall (X X':stack) (x x':name) (t t':Adbmal),
 (eoss X (abs x t))=(eoss X' (abs x' t'))->X=X'/\x=x'/\t=t'.
Proof.
induction X as [|a X ih]; intros X' x x' t t'; destruct X' as [|a' X'];
  simpl; intro h; try discriminate.
- inversion h. repeat split; reflexivity.
- injection h as h0 h1.
  destruct (ih X' x x' t t' h1) as [h2 [h3 h4]].
  subst. repeat split; reflexivity.
Qed.

Lemma eoss_inj2 : forall (X:stack) (t t':Adbmal),
  eoss X t = eoss X t' -> t = t'.
Proof.
induction X as [|x X' ih]; simpl.
- trivial.
- intros t t' h. injection h as h0. exact (ih t t' h0).
Qed.

End adbmal_calculus.
