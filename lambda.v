Require Export name.

Set Implicit Arguments.

Section lambda_calculus.

Inductive Lambda : Set :=
| var_l : name->Lambda            (* variable    *)
| abs_l : name->Lambda->Lambda    (* abstraction *)
| ap_l  : Lambda->Lambda->Lambda. (* application *)

Fixpoint FV_l_rec [t:Lambda] : stack->stack :=
[X] Cases t of
|(var_l x)     => Cases (in_dec x X) of  (left _) => Nil | _ => (cons x Nil) end
|(abs_l x t')  => (FV_l_rec t' (cons x X))
|(ap_l t1 t2)  => (juxt (FV_l_rec t1 X)(FV_l_rec t2 X))
end.

Definition FV_l := [M](FV_l_rec M Nil).

Fixpoint rename_l [M:Lambda] : name->name->Lambda :=
[x,y] Cases M of
|(var_l z)   => Cases (eq_dec z x) of
               |(left _) => (var_l y)
               | _       => (var_l z)
               end
|(abs_l z m) => Cases (eq_dec z x) of
               |(left _) => (abs_l z m) (* no renaming *)
               | _       => (abs_l z (rename_l m x y))
               end
|(ap_l m n)  => (ap_l (rename_l m x y)(rename_l n x y))
end.

Fixpoint names_l [M:Lambda] : stack :=
Cases M of
|(var_l x)   => (cons x Nil)
|(abs_l x t) => (cons x (names_l t))
|(ap_l t u)  => (juxt (names_l t)(names_l u))
end.

Inductive skel_l : Set :=
| skel_l_var : skel_l
| skel_l_abs : skel_l->skel_l
| skel_l_ap  : skel_l->skel_l->skel_l.

Fixpoint skeleton_l [M:Lambda] : skel_l :=
Cases M of 
|(var_l x)   => skel_l_var
|(abs_l x m) => (skel_l_abs (skeleton_l m))
|(ap_l m n)  => (skel_l_ap (skeleton_l m)(skeleton_l n))
end.

Lemma rename_l_skel_eq : 
 (M:Lambda;x,y:name)
  (skeleton_l (rename_l M x y))=(skeleton_l M).
Proof.
NewInduction M; Intros x y; Simpl.
Case (eq_dec n x); Reflexivity.
Case (eq_dec n x); Intro h; Simpl.
Reflexivity.
Rewrite IHM; Reflexivity.
Rewrite IHM1; Rewrite IHM2; Reflexivity.
Qed.

(* discriminable equalities *)

Definition skel_l_discr_var_abs : 
 (A:Set;s:skel_l) skel_l_var=(skel_l_abs s)->A.
Proof. Intros A s h; Discriminate h. Defined.

Definition skel_l_discr_var_ap : 
 (A:Set;s1,s2:skel_l)  skel_l_var=(skel_l_ap s1 s2)->A.
Proof. Intros A s1 s2 h; Discriminate h. Defined.

Definition skel_l_discr_abs_var : 
 (A:Set;s:skel_l) (skel_l_abs s)=skel_l_var->A.
Proof. Intros A s h; Discriminate h. Defined.

Definition skel_l_discr_abs_ap : 
 (A:Set;s,s1,s2:skel_l) (skel_l_abs s)=(skel_l_ap s1 s2)->A.
Proof. Intros A s s1 s2 h; Discriminate h. Defined.

Definition skel_l_discr_ap_var : 
 (A:Set;s1,s2:skel_l) (skel_l_ap s1 s2)=skel_l_var->A.
Proof. Intros A s1 s2 h; Discriminate h. Defined.

Definition skel_l_discr_ap_abs : 
 (A:Set;s,s1,s2:skel_l) (skel_l_ap s1 s2)=(skel_l_abs s)->A.
Proof. Intros A s s1 s2 h; Discriminate h. Defined.

Definition skel_l_inj_abs : 
 (s,s':skel_l)(skel_l_abs s)=(skel_l_abs s') -> s=s'.
Proof. Intros s s' h; Injection h; Intro h0; Exact h0. Defined.

Definition skel_l_inj_ap : 
 (s1,s2,t1,t2:skel_l)
  (skel_l_ap s1 s2)=(skel_l_ap t1 t2) -> s1=t1/\s2=t2.
Proof. Intros s1 s2 t1 t2 h; Injection h; Intros h0 h1; Exact (conj ?? h1 h0). 
Defined.

Definition in_10 := 
 [y:name;l:stack] Cases (in_dec y l) of (left _) => (S O) | _ => O end.

Unset Implicit Arguments.

(** 
Substitution M[x:=N], main call:
[[

(lambda_subst M x N) 
 = (lambda_subst_skel_rec M (skeleton_l M) x N Nil (refl_equal skel_l (skeleton_l M)))

]]
recursive in skeleton of [M] (skeleton of [(rename_l M y y' Nil)] equals skeleton of [M].)
Capture of free variables in N is avoided by renaming lambda's 'on the fly':
 [[

(\y.M)[x:=N] = (\y'.M[y:=y'])[x:=N] if y free in N, for y' fresh w.r.t. FV(MN)

]] 
*)

Fixpoint lambda_subst_skel_rec [t:Lambda;s:skel_l] : name->Lambda->(skeleton_l t)=s->Lambda := 
[x;u]
<[s:skel_l](skeleton_l t)=s->Lambda> 
Cases s of 
| skel_l_var => 
 <[t:Lambda](skeleton_l t)=skel_l_var->Lambda> 
 Cases t of
 |(var_l y)   => [_] Cases (eq_dec y x) of (left _) => u | _ => (var_l y) end
 |(abs_l _ _) => [h](skel_l_discr_abs_var ? h)
 |(ap_l _ _)  => [h](skel_l_discr_ap_var ? h)
 end
|(skel_l_abs s') => 
 <[t:Lambda](skeleton_l t)=(skel_l_abs s')->Lambda> 
 Cases t of
 |(var_l _)    => [h](skel_l_discr_var_abs ? h)
 |(abs_l y t') =>
   [h;FVu:=(FV_l u)]
    (Fix aux {aux [z:name;p:Lambda;d:(skeleton_l p)=s';n:nat] : Lambda :=
     Cases n of
     | O     => (abs_l z (lambda_subst_skel_rec p s' x u d))
     |(S m)  => [y':=(fresh (cons x (juxt (names_l p) FVu)))]   
                (aux y' (rename_l p z y')(trans_eq ???? (rename_l_skel_eq p z y') d) m)
     end}
    (*z*) y 
    (*p*) t'
    (*d*) (skel_l_inj_abs h)
    (*n*) (in_10 y (cons x FVu))
   )
 |(ap_l _ _)   => [h](skel_l_discr_ap_abs ? h)
 end
|(skel_l_ap s1 s2) =>
 <[t:Lambda](skeleton_l t)=(skel_l_ap s1 s2)->Lambda> 
 Cases t of
 |(var_l _)     => [h](skel_l_discr_var_ap ? h)
 |(abs_l _ _)   => [h](skel_l_discr_abs_ap ? h)
 |(ap_l t1 t2)  => [h;c:=(skel_l_inj_ap h)]
                   (ap_l (lambda_subst_skel_rec t1 s1 x u (proj1 ?? c))
                         (lambda_subst_skel_rec t2 s2 x u (proj2 ?? c)))
 end
end.

Set Implicit Arguments.

Definition lambda_subst := [t;x;u](lambda_subst_skel_rec t (skeleton_l t) x u (refl_equal ??)).

Lemma lambda_subst_skel_rec_repl_skel :
 (s:skel_l;t,u:Lambda;x:name;d:(skeleton_l t)=s;s':skel_l;d':(skeleton_l t)=s')
  (lambda_subst_skel_rec t s x u d)
   =(lambda_subst_skel_rec t s' x u d').
NewInduction s; NewDestruct t; Intros u x d.
NewDestruct s'; Simpl; Intro d'.
Reflexivity.
Discriminate d'.
Discriminate d'.
Discriminate d.
Discriminate d.
Discriminate d.
Rename l into t; Clear l.
NewDestruct s'; Simpl; Intro d'.
Discriminate d'.
Unfold in_10.
Case (in_dec n (cons x (FV_l u))); Intro h.
LetTac y':=(fresh (cons x (juxt (names_l t) (FV_l u)))).
Apply (f_equal ?? (abs_l y')); Apply IHs.
Apply (f_equal ?? (abs_l n)); Apply IHs.
Discriminate d'.
Discriminate d.
Discriminate d.
Discriminate d.
Rename l into t1; Clear l.
Rename l0 into t2; Clear l0.
NewDestruct s'; Intro d'.
Discriminate d'.
Discriminate d'.
Simpl; Fold skeleton_l.
Assert h1 := (IHs1 t1 u x (proj1 ?? (skel_l_inj_ap d)) s (proj1 ?? (skel_l_inj_ap d')) );
 Fold skeleton_l in h1.
Assert h2 := (IHs2 t2 u x (proj2 ?? (skel_l_inj_ap d)) s0 (proj2 ?? (skel_l_inj_ap d')) );
 Fold skeleton_l in h2.
Rewrite h1; Rewrite h2; Reflexivity.
Qed.

Lemma subst_l_var1 : 
 (y,x:name;N:Lambda) 
  y = x 
   -> (lambda_subst (var_l y) x N) = N.
Proof.
Intros y x N h; Unfold lambda_subst; Simpl.
Case (eq_dec y x); Intro h0.
Reflexivity.
Elim (h0 h).
Qed.

Lemma subst_l_var2 : 
 (y,x:name;N:Lambda)
  ~(y = x)
   -> (lambda_subst (var_l y) x N) = (var_l y).
Proof.
Intros y x N h; Unfold lambda_subst; Simpl.
Case (eq_dec y x); Intro h0.
Elim (h h0).
Reflexivity.
Qed.

Lemma subst_l_abs1 : 
 (y:name;M:Lambda;x:name;N:Lambda)[y':=(fresh (cons x (juxt (names_l M)(FV_l N))))]
  (In y (cons x (FV_l N)))
   -> (lambda_subst (abs_l y M) x N) = (lambda_subst (abs_l y' (rename_l M y y')) x N).
Proof.
Intros y M x N y' h; Unfold lambda_subst; Simpl (* --> body of skeleton_l unfolded, why? *);
 Unfold in_10; Fold skeleton_l.
Case (in_dec y (cons x (FV_l N))); Intro h0.
Fold y'.
Case (in_dec y' (cons x (FV_l N))); Intro h1.
Assert h2 : (In y' (cons x (juxt (names_l M) (FV_l N)))).
Elim h1; Intro h2.
Left; Exact h2.
Right; Apply in_or_juxt; Right; Exact h2.
Elim (fresh_not_in h2).
LetTac d := 
 (trans_eq skel_l (skeleton_l (rename_l M y y')) (skeleton_l M)
  (skeleton_l M) (rename_l_skel_eq M y y')
  (refl_equal skel_l (skeleton_l M))).
LetTac d' := (refl_equal skel_l (skeleton_l (rename_l M y y'))).
Rewrite (lambda_subst_skel_rec_repl_skel N x d d'); Reflexivity.
Elim (h0 h).
Qed.

Lemma subst_l_abs2 : 
 (y:name;M:Lambda;x:name;N:Lambda)
  ~(In y (cons x (FV_l N)))
    -> (lambda_subst (abs_l y M) x N) = (abs_l y (lambda_subst M x N)).
Proof.
Intros y M x N h; Unfold lambda_subst; Simpl; Unfold in_10; Fold skeleton_l.
Case (in_dec y (cons x (FV_l N))); Intro h0.
Elim (h h0).
Reflexivity.
Qed.

Lemma subst_l_ap : 
 (M1,M2:Lambda;x:name;N:Lambda)
  (lambda_subst (ap_l M1 M2) x N) = (ap_l (lambda_subst M1 x N)(lambda_subst M2 x N)).
Proof.
Intros M1 M2 x N.
Unfold lambda_subst; Simpl; Fold skeleton_l.
LetTac d1 := (proj1 ?? (skel_l_inj_ap (refl_equal ? (skel_l_ap (skeleton_l M1) (skeleton_l M2))))).
LetTac d2 := (proj2 ?? (skel_l_inj_ap (refl_equal ? (skel_l_ap (skeleton_l M1) (skeleton_l M2))))).
LetTac d1' := (refl_equal ? (skeleton_l M1)).
LetTac d2' := (refl_equal ? (skeleton_l M2)).
Rewrite (lambda_subst_skel_rec_repl_skel N x d1 d1').
Rewrite (lambda_subst_skel_rec_repl_skel N x d2 d2').
Reflexivity.
Qed.

(* closure of adbmal_beta-rule (lambda_beta_rule) under Adbmal-constructors *)

Inductive lambda_beta : Lambda->Lambda->Prop :=
| lambda_beta_abs : (M,N:Lambda;x:name)(lambda_beta M N)->(lambda_beta (abs_l x M)(abs_l x N))
| lambda_beta_apl : (M,M',N:Lambda)(lambda_beta M M')->(lambda_beta (ap_l M N)(ap_l M' N))
| lambda_beta_apr : (M,M',N:Lambda)(lambda_beta M M')->(lambda_beta (ap_l N M)(ap_l N M'))
| lambda_beta_rule: (M,N:Lambda;x:name)(lambda_beta (ap_l (abs_l x M) N)(lambda_subst M x N)).


(*----------------------------------------------------------------*)

Require Export alpha.

Fixpoint emb [M:Lambda] : Adbmal :=
Cases M of
|(var_l x)     => (var x)
|(abs_l x m)   => (abs x (emb m))
|(ap_l m1 m2) => (ap (emb m1)(emb m2))
end.

Lemma lambda_eos_free : (M:Lambda)(eos_free (emb M)).
NewInduction M.
Exact I.
Exact IHM.
Split; [ Exact IHM1 | Exact IHM2 ].
Qed.

Lemma lambda_scope_balanced : (M:Lambda)(scope_balanced (emb M)).
Proof [M](eos_free_scb Nil (lambda_eos_free M)).

Lemma FV_l2s : (M:Lambda;X:stack)(FV (emb M) X)=(FV_l_rec M X).
Proof.
NewInduction M; Intro X.
Reflexivity.
Exact (IHM (cons n X)).
Simpl; Rewrite IHM1; Rewrite IHM2; Reflexivity.
Qed.

Lemma rename_l2s : 
 (x,y:name;M:Lambda;X:stack)
  ~(In x X)
   ->(emb (rename_l M x y)) = (rename (emb M) x y X).
Proof.
NewInduction M; Intros X h; Simpl.
Case (in_dec n X); Intro h0; Case (eq_dec n x); Intro h1.
Elim h; Rewrite <- h1; Exact h0.
Reflexivity.
Reflexivity.
Reflexivity.
Case (eq_dec n x); Intro h0.
Rewrite rename_eos_free_in_stack.
Reflexivity.
Apply lambda_eos_free.
Left; Exact h0.
Rewrite <- IHM.
Reflexivity.
Intro h1; Elim h1; [ Exact h0 | Exact h ].
Rewrite (IHM1 X h); Rewrite (IHM2 X h); Reflexivity.
Qed.

Lemma names_l2s : (M:Lambda)(names_l M)=(names (emb M)).
Proof.
NewInduction M; Simpl.
Reflexivity.
Rewrite IHM; Reflexivity.
Rewrite IHM1; Rewrite IHM2; Reflexivity.
Qed.

Lemma FV_lambda_subst_skel_rec_sub :
 (x:name;N:Lambda;s:skel_l;M:Lambda;d:(skeleton_l M)=s;Y:stack)
  (sub (FV_l_rec (lambda_subst_skel_rec M s x N d) Y) (juxt (FV_l_rec M Y) (FV_l N))).
Proof.
NewInduction s; NewDestruct M; Intros d Y; Simpl.
Assert a : (sub (FV_l_rec N Y) (FV_l N)).
Unfold FV_l; Rewrite <- FV_l2s; Rewrite <- FV_l2s.
Rewrite (juxt_nil_end Y).
Exact (FV_sub1 1!(emb N) 2!Nil 3!Y 4!Nil).
Case (eq_dec n x); Intro h; Simpl; Case (in_dec n Y); Intro h0.
Exact a.
Intros u h1; Right; Exact (a u h1).
Apply sub_nil.
Intros u h1; Left; Elim h1; Intro h2.
Exact h2.
Elim h2.
Discriminate d.
Discriminate d.
Discriminate d.
Unfold in_10; Case (in_dec n (cons x (FV_l N))); Intros h.
Simpl.
Rename l into t; Clear l.
LetTac d':=
(trans_eq skel_l
           (skeleton_l
             (rename_l t n (fresh (cons x (juxt (names_l t) (FV_l N))))))
           (skeleton_l t) s
           (rename_l_skel_eq t n
             (fresh (cons x (juxt (names_l t) (FV_l N)))))
           (skel_l_inj_abs d)).
LetTac y':=(fresh (cons x (juxt (names_l t) (FV_l N)))).
Assert h0 := (IHs (rename_l t n y') d' (cons y' Y)).
Assert h1 : (kahrs' (emb t) (cons n Y) (rename (emb t) n y' Nil) (cons y' Y)).
 Assert h1 : ~(In y' (names_l t)).
 Intro h1.
 Apply (fresh_not_in 1!(cons x (juxt (names_l t) (FV_l N)))).
 Fold y'.
 Right; Apply in_or_juxt; Left; Exact h1.
 Rewrite names_l2s in h1.
Exact (kahrs_rename n Y 5!Nil [f]f h1).
Rewrite (juxt_nil_end (cons n Y)) in h1.
Rewrite (juxt_nil_end (cons y' Y)) in h1.
Assert h2 := (kahrs_FV_eq 3!(cons n Y) 4!(cons y' Y) 5!Nil h1).
Rewrite <- (FV_l2s t (cons n Y)).
Rewrite h2.
Rewrite <- rename_l2s.
Rewrite FV_l2s.
Exact h0.
Exact [f]f.
Simpl; Apply IHs.
Discriminate d.
Discriminate d.
Discriminate d.
Fold skeleton_l.
Intros u h0; Apply in_or_juxt.
Elim (in_juxt_or h0); Intro h1.
Elim (in_juxt_or (IHs1 ???? h1)); Intros h2.
Left; Apply in_or_juxt; Left; Exact h2.
Right; Exact h2.
Elim (in_juxt_or (IHs2 ???? h1)); Intros h2.
Left; Apply in_or_juxt; Right; Exact h2.
Right; Exact h2.
Qed.

Lemma FV_subst_l_sub : (x:name;M,N:Lambda)(sub (FV_l (lambda_subst M x N)) (juxt (FV_l M) (FV_l N))).
Proof [x;M,N;y;h](FV_lambda_subst_skel_rec_sub h).

Lemma lambda_subst_skel_rec_not_in :
 (x:name;N:Lambda;s:skel_l;M:Lambda;d:(skeleton_l M)=s;Z,Y:stack)
  ~(In x Y)
   ->~(In x (FV (emb M) Y))
    ->(kahrs' (emb (lambda_subst_skel_rec M s x N d)) (juxt Y Z) (emb M) (juxt Y Z)).
Proof.
NewInduction s; NewDestruct M; Intros d Z Y h; Simpl.
Case (in_dec n Y); Intro h0.
Intro h1; Clear h1.
Case (eq_dec n x); Intro h1.
Elim h; Rewrite <- h1; Exact h0.
Apply kahrs_refl.
Intro h1.
Case (eq_dec n x); Intro h2.
Elim h1; Left; Exact h2.
Apply kahrs_refl.
Discriminate d.
Discriminate d.
Discriminate d.
Intro h0.
Rename l into M; Clear l.
Rename n into y; Clear n.
Unfold in_10; Case (in_dec y (cons x (FV_l N))); Intro h1; Simpl.
LetTac y':=(fresh (cons x (juxt (names_l M) (FV_l N)))).
LetTac d':=(trans_eq skel_l (skeleton_l (rename_l M y y')) (skeleton_l M) s
            (rename_l_skel_eq M y y') (skel_l_inj_abs d)).
Assert h2 := (fresh_not_in 1!(cons x (juxt (names_l M) (FV_l N)))).
Fold y' in h2.
Simpl in h2; Elim (dmx h2); Clear h2; Intros h2 h3.
Elim (dmx [o](h3 (in_or_juxt o))); Clear h3; Intros h3 h4.
Rewrite names_l2s in h3.
Assert h5 := (kahrs_rename y 2!y' 3!(emb M) (juxt Y Z) 5!Nil [z]z h3).
Simpl in h5.
Assert a1 : (kahrs' (abs y' (emb (lambda_subst_skel_rec (rename_l M y y') s x N d'))) (juxt Y Z)
                    (abs y' (emb (rename_l M y y'))) (juxt Y Z)).
Apply kahrs_abs.
Apply (IHs (rename_l M y y') d' Z (cons y' Y)).
Intro h6; Elim h6; Intro h7.
Apply h2; Symmetry; Exact h7.
Exact (h h7).
Rewrite (rename_l2s 1!y y' M 4!Nil [z]z).
Rewrite <- (kahrs_FV_eq 3!(cons y Y) 4!(cons y' Y) h5).
Exact h0.
Assert a2 : (kahrs' (abs y' (emb (rename_l M y y'))) (juxt Y Z) (abs y (emb M)) (juxt Y Z)).
Apply kahrs_abs.
Apply kahrs_symm.
Rewrite (rename_l2s 1!y y' M 4!Nil [z:?]z).
Exact h5.
Exact (kahrs_trans a1 a2).
Apply kahrs_abs; Apply (IHs M (skel_l_inj_abs d) Z (cons y Y)).
Intro h2; Elim h2; Intro h3.
Apply h1; Left; Symmetry; Exact h3.
Exact (h h3).
Exact h0.
Discriminate d.
Discriminate d.
Discriminate d.
Fold skeleton_l. 
Intro h0.
Elim (dmx [o](h0 (in_or_juxt o))); Intros h1 h2.
Apply kahrs_ap.
Exact (IHs1 l (proj1 ?? (skel_l_inj_ap d)) Z Y h h1).
Exact (IHs2 l0 (proj2 ?? (skel_l_inj_ap d)) Z Y h h2).
Qed.

Lemma subst_l_not_in :
 (M,N:Lambda;x:name;Y,Z:stack)
  ~(In x Y)
   ->~(In x (FV (emb M) Y))
    ->(kahrs' (emb (lambda_subst M x N)) (juxt Y Z) (emb M) (juxt Y Z)).
Proof [M,N;x;Y,Z;h;h0](lambda_subst_skel_rec_not_in N (refl_equal ? (skeleton_l M)) Z h h0).

End lambda_calculus.
