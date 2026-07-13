Require Export balancedness.
Require Export ars.

Set Implicit Arguments.

(** We define alpha equality in three ways: [kahrs], [church] and [schroer]
    and prove them equivalent. *)

Section Alpha.

Inductive kahrs' : Adbmal -> stack -> Adbmal -> stack -> Prop :=
| kahrs_var1 : (x:name)(kahrs' (var x) Nil (var x) Nil)
| kahrs_var2 : (x,y:name;X,Y:stack)
   (length X)=(length Y)->(kahrs' (var x)(cons x X)(var y)(cons y Y))
| kahrs_var3 : (x,x',y,y':name;X,Y:stack)
   ~(x=x') -> ~(y=y') -> (kahrs' (var x) X (var y) Y)
    -> (kahrs' (var x) (cons x' X) (var y) (cons y' Y))
| kahrs_abs : (x,y:name;M,N:Adbmal;X,Y:stack)
   (kahrs' M (cons x X) N (cons y Y))
    -> (kahrs' (abs x M) X (abs y N) Y)
| kahrs_eos1 : (x:name;M,N:Adbmal)
   (kahrs' M Nil N Nil) -> (kahrs' (eos x M) Nil (eos x N) Nil)
| kahrs_eos2 : (x,y:name;M,N:Adbmal;X,Y:stack)
   (kahrs' M X N Y) -> (kahrs' (eos x M)(cons x X)(eos y N)(cons y Y))
| kahrs_eos3 : (x,x',y,y':name;M,N:Adbmal;X,Y:stack)
   ~(x=x') -> ~(y=y') -> (kahrs' (eos x M) X (eos y N) Y) 
    -> (kahrs' (eos x M)(cons x' X)(eos y N)(cons y' Y))
| kahrs_ap : (M1,M2,N1,N2:Adbmal;X,Y:stack)
   (kahrs' M1 X N1 Y) -> (kahrs' M2 X N2 Y) 
    -> (kahrs' (ap M1 M2) X (ap N1 N2) Y).

Definition kahrs := [M,N:Adbmal](kahrs' M Nil N Nil).

Inductive skel : Set :=
| var_skel : skel
| abs_skel : skel->skel
| eos_skel : skel->skel
| ap_skel  : skel->skel->skel.

Fixpoint skeleton [M:Adbmal] : skel :=
Cases M of 
|(var _)   => var_skel
|(abs _ m) => (abs_skel (skeleton m))
|(eos _ m) => (eos_skel (skeleton m))
|(ap m n)  => (ap_skel (skeleton m)(skeleton n))
end.

Lemma kahrs_skel : 
 (M,N:Adbmal;X,Y:stack)(kahrs' M X N Y)->(skeleton M)=(skeleton N).
Proof.
Intros M N X Y h; Elim h; Clear h M N X Y; Simpl.
Reflexivity.
Reflexivity.
Reflexivity.
Intros x y M N X Y h ih; Rewrite ih; Reflexivity.
Intros x M N h ih; Rewrite ih; Reflexivity.
Intros x y M N X Y h ih; Rewrite ih; Reflexivity.
Intros x x' y y' M N X Y h h0 h1 ih; Rewrite ih; Reflexivity.
Intros M1 M2 N1 N2 X Y h1 ih1 h2 ih2; Rewrite ih1; Rewrite ih2; Reflexivity.
Qed.

Lemma kahrs_list_length : 
 (M,N:Adbmal;X,Y:stack)(kahrs' M X N Y)->(length X)=(length Y).
Proof.
NewInduction 1; Simpl.
Reflexivity.
Rewrite H; Reflexivity.
Rewrite IHkahrs'; Reflexivity.
Injection IHkahrs'; Intro H0; Exact H0.
Reflexivity.
Rewrite IHkahrs'; Reflexivity.
Rewrite IHkahrs'; Reflexivity.
Exact IHkahrs'1.
Qed.

(* scope-balancedness is closed under alpha-equivalence *)

Lemma kahrs_scb : 
 (M,N:Adbmal;X,Y:stack)
  (kahrs' M X N Y)
   ->(scb X M)
    ->(scb Y N).
Proof.
Intros M N X Y h; Elim h; Clear h M N X Y; Simpl.
Exact [x;h]h.
Intros x y X Y h h0.
Apply scb_var.
Intros x x' y y' X Y e1 e2 a ih b.
Apply scb_var.
Intros x y M N X Y a ih b.
Apply scb_abs.
Apply ih.
Exact (scb_abs_inv b).
Intros x M N a ih b.
Apply False_ind.
Inversion b.
Intros x y M N X Y a ih b.
Apply scb_eos.
Apply ih.
Elim (scb_eos_inv b); Intros e b'.
Exact b'.
Intros x x' y y' M N X Y e1 e2 a ih b.
Apply False_ind.
Apply e1.
Elim (scb_eos_inv b); Intros e3 b'.
Exact e3.
Intros M1 M2 N1 N2 X Y a1 ih1 a2 ih2 b.
Elim (scb_ap_inv b); Intros b1 b2.
Apply scb_ap.
Exact (ih1 b1).
Exact (ih2 b2).
Qed.

Lemma kahrs_scope_balanced : 
 (M,N:Adbmal)
  (kahrs M N)
   ->(scope_balanced M)
    ->(scope_balanced N).
Proof [M,N;a;b](kahrs_scb a b).

Lemma kahrs_refl : (M:Adbmal;X:stack)(kahrs' M X M X).
Proof.
Induction M.
Intros x X.
Elim X.
Apply kahrs_var1.
Intros x' X' ih.
Case (eq_dec x x'); Intro e.
Rewrite e.
Apply kahrs_var2.
Reflexivity.
Apply (kahrs_var3 e e ih).
Intros x t ih X.
Apply kahrs_abs.
Apply ih.
Intros x t ih X.
Elim X.
Apply kahrs_eos1.
Apply ih.
Intros x' X' a.
Case (eq_dec x x'); Intro e.
Rewrite e.
Apply kahrs_eos2.
Apply ih.
Exact (kahrs_eos3 e e a).
Intros t1 ih1 t2 ih2 X.
Apply kahrs_ap.
Apply ih1.
Apply ih2.
Qed.

Lemma kahrs_symm : 
 (M,N:Adbmal;X,Y:stack)(kahrs' M X N Y)->(kahrs' N Y M X).
Proof.
Intros M N X Y h.
Elim h; Clear h M N X Y.
Intro x.
Apply kahrs_var1.
Intros x y X Y h.
Apply kahrs_var2.
Symmetry; Exact h.
Intros x x' y y' X Y e1 e2 a ih.
Exact (kahrs_var3 e2 e1 ih).
Intros x y M N X Y a ih.
Exact (kahrs_abs ih).
Intros x M N a ih.
Exact (kahrs_eos1 x ih).
Intros x y M N X Y a ih.
Exact (kahrs_eos2 y x ih).
Intros x x' y y' M N X Y e1 e2 a ih.
Exact (kahrs_eos3 e2 e1 ih).
Intros M1 M2 N1 N2 X Y a1 ih1 a2 ih2.
Exact (kahrs_ap ih1 ih2).
Qed.

Lemma kahrs_trans : 
 (M,N:Adbmal;X,Y:stack)
 (kahrs' M X N Y)
  ->(P:Adbmal;Z:stack)(kahrs' N Y P Z)->(kahrs' M X P Z).
Proof.
Intros M N X Y h.
Elim h; Clear h M X N Y.
Exact [x;P;Z;h]h.
Intros x y X Y h P Z h0.
Inversion_clear h0.
Apply kahrs_var2.
Transitivity (length Y); Assumption.
Apply False_ind.
Apply H.
Reflexivity.
Intros x x' y y' X Y e1 e2 a1 ih P Z a2.
Inversion a2.
Apply False_ind.
Apply e2.
Assumption.
Apply kahrs_var3.
Exact e1.
Assumption.
Apply ih; Assumption.
Intros x y M N X Y a1 ih P Z a2.
Inversion a2.
Apply kahrs_abs.
Apply ih; Assumption.
Intros x M N a1 ih P Z a2.
Inversion a2.
Apply kahrs_eos1.
Apply ih; Assumption.
Intros x y M N X Y a1 ih P Z a2.
Inversion a2.
Apply kahrs_eos2.
Apply ih; Assumption.
Apply False_ind.
Apply H3.
Reflexivity.
Intros x x' y y' M N X Y e1 e2 a1 ih P Z a2.
Inversion a2.
Apply False_ind.
Apply e2.
Assumption.
Apply kahrs_eos3.
Exact e1.
Assumption.
Apply ih; Assumption.
Intros M1 M2 N1 N2 X Y a1 ih1 a2 ih2 P Z a3.
Inversion a3.
Apply kahrs_ap.
Apply ih1; Assumption.
Apply ih2; Assumption.
Qed.

Lemma kahrs_snoc1 :
 (M,N:Adbmal;X,Y:stack;z:name)
  (kahrs' M X N Y)->(kahrs' M (snoc z X) N (snoc z Y)).
Proof.
Intros M N X Y z h.
Elim h; Clear h M N X Y; Simpl.
Intro x. (* Apply kahrs_refl. *)
Case (eq_dec x z); Intro e.
Rewrite e; Apply kahrs_var2.
Reflexivity.
Exact (kahrs_var3 e e (kahrs_var1 x)).
Intros x y X Y h.
Apply kahrs_var2.
Rewrite length_snoc.
Rewrite length_snoc.
Rewrite h.
Reflexivity.
Intros x x' y y' X Y e1 e2 a ih.
Exact (kahrs_var3 e1 e2 ih).
Intros x y M N X Y a ih.
Exact (kahrs_abs ih).
Intros x M N a ih.
Case (eq_dec x z); Intro e.
Rewrite e.
Exact (kahrs_eos2 z z a).
Exact (kahrs_eos3 e e (kahrs_eos1 x a)).
Intros x y M N X Y a ih.
Exact (kahrs_eos2 x y ih).
Intros x x' y y' M N X Y e1 e2 a ih.
Exact (kahrs_eos3 e1 e2 ih).
Intros M1 M2 N1 N2 X Y a1 ih1 a2 ih2.
Exact (kahrs_ap ih1 ih2).
Qed.

Lemma kahrs_var_snoc2 :
 (x,y,z:name;X,Y:stack)
  (kahrs' (var x)(snoc z X)(var y)(snoc z Y))
   ->(kahrs' (var x) X (var y) Y).
Proof.
NewInduction X; NewDestruct Y; Simpl.
Intro h; Inversion h.
Apply kahrs_var1.
Assumption.
Intro h.
Assert h0 := (kahrs_list_length h).
Simpl in h0; Injection h0; Rewrite length_snoc; Intro h1; Discriminate h1.
Intro h.
Assert h0 := (kahrs_list_length h).
Simpl in h0; Injection h0; Rewrite length_snoc; Intro h1; Discriminate h1.
Intro h; Inversion_clear h.
Apply kahrs_var2.
Simpl in H; Rewrite length_snoc in H; Rewrite length_snoc in H;
Injection H; Exact [h]h.
Apply kahrs_var3.
Exact H.
Exact H0.
Apply IHX.
Assumption.
Qed.

Lemma kahrs_eos_snoc2 :
 (M,N:Adbmal;x,y,z:name)
  ((X,Y:stack)
   (kahrs' M (snoc z X) N (snoc z Y))->(kahrs' M X N Y))
   ->(X,Y:stack)
      (kahrs' (eos x M)(snoc z X)(eos y N)(snoc z Y))
       ->(kahrs' (eos x M) X (eos y N) Y).
Proof.
Intros M N x y z ihM.
Induction X.
Destruct Y; Simpl.
(* nil nil *)
Intro h; Inversion h.
Apply kahrs_eos1.
Assumption.
Assumption.
(* nil cons *)
Intros y' Y' h.
Assert h0 := (kahrs_list_length h).
Simpl in h0; Rewrite length_snoc in h0; Discriminate h0.
Intros x' X' ihX.
Destruct Y; Simpl.
(* cons nil *)
Intro h.
Assert h0 := (kahrs_list_length h).
Simpl in h0; Rewrite length_snoc in h0; Discriminate h0.
(* cons cons *)
Intros y' Y' h.
Inversion h.
Apply kahrs_eos2.
Apply ihM; Assumption.
Apply kahrs_eos3.
Assumption.
Assumption.
Apply ihX; Assumption.
Qed.

Lemma kahrs_snoc2 :
 (M,N:Adbmal;X,Y:stack;z:name)
  (kahrs' M (snoc z X) N (snoc z Y))->(kahrs' M X N Y).
(* Messy *) Proof.
Induction M.
Intros x N X Y z h.
Inversion h.
Exact (snoc_not_nil ? H).
Rewrite <- H2 in h; Exact (kahrs_var_snoc2 h).
Rewrite <- H4 in h; Exact (kahrs_var_snoc2 h).
Intros x t ih N X Y z h.
Inversion_clear h.
Apply kahrs_abs.
Apply ih with z:=z.
Exact H.
Intros x t ih N X Y z h.
Inversion h.
Exact (snoc_not_nil ? H2).
NewDestruct X.
Simpl in H2; Injection H2; Intros h1 h2.
NewDestruct Y.
Simpl in H4; Injection H4; Intros h3 h4.
Rewrite h2; Rewrite h4; Apply kahrs_eos1.
Rewrite h1 in H3; Rewrite h3 in H3; Exact H3.
Simpl in H4; Injection H4; Intros h3 h4.
Rewrite h1 in H3; Rewrite h3 in H3.
Assert h5 := (kahrs_list_length H3).
Rewrite length_snoc in h5; Discriminate h5.
Simpl in H2; Injection H2; Intros h1 h2.
NewDestruct Y.
Simpl in H4; Injection H4; Intros h3 h4.
Rewrite h1 in H3; Rewrite h3 in H3.
Assert h5 := (kahrs_list_length H3).
Rewrite length_snoc in h5.
Discriminate h5.
Simpl in H4; Injection H4; Intros h3 h4.
Rewrite h2; Rewrite h4.
Apply kahrs_eos2.
Rewrite h1 in H3; Rewrite h3 in H3.
Apply ih with 1:=H3.
NewDestruct X; Simpl.
Injection H1; Intros h1 h2.
NewDestruct Y; Simpl.
Injection H2; Intros h3 h4.
Rewrite h1 in H6; Rewrite h3 in H6; Exact H6.
Simpl in H2; Injection H2; Intros h3 h4.
Rewrite h1 in H6; Rewrite h3 in H6.
Assert h5 := (kahrs_list_length H6).
Rewrite length_snoc in h5.
Discriminate h5.
Simpl in H1; Injection H1; Intros h1 h2.
NewDestruct Y; Simpl.
Injection H2; Intros h3 h4.
Rewrite h1 in H6; Rewrite h3 in H6.
Assert h5 := (kahrs_list_length H6).
Rewrite length_snoc in h5.
Discriminate h5.
Simpl in H2; Injection H2; Intros h3 h4.
Rewrite h1 in H6; Rewrite h3 in H6.
Apply kahrs_eos3.
Intro h5; Apply H3; Rewrite h2; Exact h5.
Intro h5; Apply H5; Rewrite h4; Exact h5.
Exact (kahrs_eos_snoc2 [X,Y](ih N0 X Y z) H6).
Intros t1 ih1 t2 ih2 N X Y z h.
Inversion h.
Apply kahrs_ap.
Apply ih1 with 1:=H1.
Apply ih2 with 1:=H5.
Qed.

Lemma kahrs_cxt_congr : 
 (c:Adbmal->Adbmal)
  (cxt c) 
   ->(t,t':Adbmal)(kahrs t t')
                 ->(kahrs (c t)(c t')). 
Proof. 
Intros c h; Elim h; Clear h c. 
Exact [t,t';h]h. 
Exact [c,d;hc;ihc;hd;ihd;t,t';a](ihc (d t)(d t')(ihd t t' a)). 
Exact [x;t,t';a](kahrs_abs (kahrs_snoc1 x a)). 
Exact [x;t,t';a](kahrs_eos1 x a). 
Exact [u,t,t';a](kahrs_ap a (kahrs_refl u Nil)). 
Exact [u,t,t';a](kahrs_ap (kahrs_refl u Nil) a). 
Qed.

Lemma kahrs_eos3_gen :
 (x,y:name;M,N:Adbmal;X',Y',X,Y:stack)
  ~(In x X')
   ->~(In y Y')
    ->(length X')=(length Y')
    ->(kahrs' (eos x M) X (eos y N) Y)
     ->(kahrs' (eos x M) (juxt X' X) (eos y N) (juxt Y' Y)).
Proof.
NewInduction X'; NewDestruct Y'; Simpl; Intros X Y h h0 h1 h2.
Exact h2.
Discriminate h1.
Discriminate h1.
Elim (dmx h); Intros h3 h4.
Elim (dmx h0); Intros h5 h6.
Apply kahrs_eos3.
Intro h7; Apply h3; Symmetry; Exact h7.
Intro h7; Apply h5; Symmetry; Exact h7.
Injection h1; Clear h1; Intro h1.
Exact (IHX' l X Y h4 h6 h1 h2).
Qed.

(** Definition of renaming; write [M[x:=y,Z]] for  [(rename M x y Z)].*)

Fixpoint rename [M:Adbmal] : name->name->stack->Adbmal :=
[x,y;Z] Cases M of
|(var z)   => Cases (in_dec z Z) of
              |(left _) => (var z)
              | _       => Cases (eq_dec z x) of
                                |(left _) => (var y)
                                | _       => (var z)
                                end
              end
|(abs z m) => (abs z (rename m x y (cons z Z)))
|(eos z m) => (Fix aux {aux [l:stack] : Adbmal :=
              Cases l of
              | nil         =>  Cases (eq_dec x z) of 
                                |(left _) => (eos y m) 
                                | _       => (eos z m)  
                                end
              |(cons z' l') => Cases (eq_dec z z') of
                                |(left _) => (eos z (rename m x y l')) 
                                | _       => (aux l')  
                                end
              end} Z)
|(ap m n)  => (ap (rename m x y Z)(rename n x y Z))
end.

Lemma rename_eoss :
 (M:Adbmal;X,Y:stack;x,z:name)
  (rename (eoss X M) x z (juxt X Y))
   =(eoss X (rename M  x z Y)).
Proof.
NewInduction X; Intros Y x z; Simpl.
Reflexivity.
Case (eq_dec a a); Intro h; Simpl.
Rewrite IHX; Reflexivity.
Elim h; Reflexivity.
Qed.

Lemma scb_rename : 
 (M:Adbmal;x,z:name;X1,X2:stack)
  (scb (juxt X1 (cons x X2)) M)
   ->(scb (juxt X1 (cons z X2))(rename M x z X1)).
Proof.
NewInduction M; Intros x z X1 X2 h.
Simpl.
Case (in_dec n X1); Intro h0.
Apply scb_var.
Case (eq_dec n x); Intro h1; Apply scb_var.
Simpl.
Assert h0 := (scb_abs_inv h).
Apply scb_abs.
Exact (IHM x z (cons n X1) X2 h0).
NewInduction X1; Simpl in h; Simpl.
Elim (scb_eos_inv h); Intros h1 h2.
Case (eq_dec x n); Intro h3; Simpl.
Apply scb_eos; Exact h2.
Elim h3; Symmetry; Exact h1.
Elim (scb_eos_inv h); Intros h1 h2.
Case (eq_dec n a); Intro h0; Simpl.
Rewrite h0.
Apply scb_eos; Apply IHM; Exact h2.
Elim (h0 h1).
Elim (scb_ap_inv h); Intros h1 h2.
Simpl.
Apply scb_ap.
Apply IHM1; Exact h1.
Apply IHM2; Exact h2.
Qed.

Fixpoint names [M:Adbmal] : stack :=
Cases M of
|(var x)   => (cons x Nil)
|(abs x t) => (cons x (names t))
|(eos x t) => (cons x (names t))
|(ap t u)  => (juxt (names t)(names u))
end.

Lemma in_eoss :
(N:Adbmal;Y:stack;z:name)
  (In z (names (eoss Y N)))
   ->(In z Y)\/(In z (names N)).
Proof.
Intros N Y z h.
NewInduction Y; Simpl.
Right; Exact h.
Simpl in h; Elim h; Intro h0.
Left; Left; Exact h0.
Elim (IHY h0); Intro h1.
Left; Right; Exact h1.
Right; Exact h1.
Qed.

Lemma in_eoss1 : 
 (M:Adbmal;X:stack;z:name)(In z X)->(In z (names (eoss X M))).
Proof.
Intros M X z h.
NewInduction X; Simpl.
Elim h.
Elim h; Intro h0.
Left; Exact h0.
Right; Exact (IHX h0).
Qed.

Lemma in_eoss2 : 
 (M:Adbmal;X:stack;z:name)(In z (names M))->(In z (names (eoss X M))).
Proof.
Intros M X z h.
NewInduction X; Simpl.
Exact h.
Right; Exact IHX.
Qed.

Lemma subst_eq_rename_bal :
 (M:Adbmal;Z,W:stack;x,y:name)
  (bal (juxt Z (cons x W)) M)
   ->~(In y Z)
   ->~(In y (names M))
   ->(adbmal_subst (cons y Nil) Z M x (var y)) = (rename M x y Z).
Proof.
NewInduction M; Intros Z W x y b d1 d2.
Elim (bal_var_inv b); Intros Z' e.
NewDestruct Z; Simpl in e; Injection e; Intros e1 e2.
Simpl.
Case (in_dec n Nil); Intro h; [ Elim h | Clear h ].
Rewrite e2; Case (eq_dec n n); Intro h;
[ Clear h | Elim h; Reflexivity ].
Reflexivity.
Simpl.
Case (in_dec n (cons n0 l)); Intro h.
Reflexivity.
Elim h; Left; Exact e2.
Simpl.
Rewrite (IHM (cons n Z) W x y (bal_abs_inv b)).
Reflexivity.
Intro h; Elim h; Intro h0.
Apply d2; Left; Exact h0.
Exact (d1 h0).
Intro h; Apply d2; Right; Exact h.
NewDestruct Z.
Simpl.
Simpl in b.
Elim (bal_eos_inv b); Intros h h0.
Rewrite h; Case (eq_dec x x); Intro h1;
[ Clear h1 | Elim h1; Reflexivity ].
Reflexivity.
Simpl in b; Elim (bal_eos_inv b); Intros h h0.
Simpl.
Rewrite h; Case (eq_dec n0 n0); Intros h1;
[ Clear h1 | Elim h1; Reflexivity ].
Rewrite (IHM l W x y h0).
Reflexivity.
Intro h1; Apply d1; Right; Exact h1.
Intro h1; Apply d2; Right; Exact h1.
Elim (bal_ap_inv b); Intros b1 b2.
Assert h1 : ~(In y (names M1)).
Intro h; Apply d2; Simpl; Apply in_or_juxt; Left; Exact h.
Assert h2 : ~(In y (names M2)).
Intro h; Apply d2; Simpl; Apply in_or_juxt; Right; Exact h.
Simpl.
Rewrite (IHM1 Z W x y b1 d1 h1); Rewrite (IHM2 Z W x y b2 d1 h2);
Reflexivity.
Qed.

Lemma not_in_subst : 
 (M,N:Adbmal;X,Y:stack;x,z:name)
  ~(In z (names M))
   ->~(In z (names N))
    ->~(In z X)
     ->~(In z Y)
       ->~(In z (names (adbmal_subst X Y M x N))).
Proof.
NewInduction M; Intros N X Y x z h h0 h1 h2.
Simpl.
Case (in_dec n Y); Intro h3.
Exact h.
Case (eq_dec x n); Intro h4.
Intro h5; Apply h0.
Elim (in_eoss h5); Intro h6.
Elim (h2 h6).
Exact h6.
Intro h5; Elim (in_eoss h5); Intro h6.
Exact (h2 h6).
Elim (in_eoss h6); Intro h7.
Exact (h1 h7).
Exact (h h7).
Intro h3; Elim h3; Intro h4.
Apply h; Left; Exact h4.
Apply IHM with 2:=h0 3:=h1 5:=h4.
Intro h5; Apply h; Right; Exact h5.
Intro h5; Elim h5; Intro h6.
Apply h; Left; Exact h6.
Exact (h2 h6).
Case (in_dec n Y); Intro h3.
Elim (in_split eq_dec h3); Intros Y1 h4; Elim h4; Intros Y2 h5;
Elim h5; Clear h4 h5; Intros h4 h5.
Rewrite h4.
Rewrite (adbmal_subst_eos_clause1 M N x X Y2 h5).
Intro h6; Elim h6; Intro h7.
Apply h; Left; Exact h7.
Apply IHM with 5:=h7.
Intro h8; Apply h; Right; Exact h8.
Exact h0.
Exact h1.
Intro h8; Apply h2; Rewrite h4; Apply in_or_juxt; Right; Right;
Exact h8.
Case (eq_dec x n); Intro h4.
Rewrite (adbmal_subst_eos_clause2 M N X h4 h3).
Intro h5; Elim (in_eoss h5); Intro h6.
Exact (h2 h6).
Elim (in_eoss h6); Intro h7.
Exact (h1 h7).
Apply h; Right; Exact h7.
Rewrite (adbmal_subst_eos_clause3 M N X h4 h3).
Intro h5; Elim (in_eoss h5); Intro h6.
Exact (h2 h6).
Elim (in_eoss h6); Intro h7.
Exact (h1 h7).
Exact (h h7).
Simpl; Intro h3; Elim (in_juxt_or h3); [ Apply IHM1 | Apply IHM2 ]; Auto;
 Intro h4; Apply h; Simpl; Apply in_or_juxt; [ Left | Right ]; Exact h4.
Qed.

Lemma not_in_beta : 
 (M,N:Adbmal;z:name)~(In z (names M))->(adbmal_beta M N)->~(In z (names N)).
Proof.
NewInduction M; Intros N z h h0.
Inversion h0.
Inversion_clear h0.
Intro h0; Elim h0; Intro h1.
Apply h; Left; Exact h1.
Apply IHM with 2:=H 3:=h1.
Intro h2; Apply h; Right; Exact h2.
Inversion_clear h0.
Intro h0; Elim h0; Intro h1.
Apply h; Left; Exact h1.
Apply IHM with 2:=H 3:=h1.
Intro h2; Apply h; Right; Exact h2.
Inversion h0.
Simpl; Intro h1; Elim (in_juxt_or h1); Intro h2.
Apply IHM1 with 2:=H2 3:=h2.
Intro h3; Apply h; Simpl; Apply in_or_juxt; Left; Exact h3.
Apply h; Simpl; Apply in_or_juxt; Right; Exact h2.
Simpl; Intro h1; Elim (in_juxt_or h1); Intro h2.
Apply h; Simpl; Apply in_or_juxt; Left; Exact h2.
Apply IHM2 with 2:=H2 3:=h2.
Intro h3; Apply h; Simpl; Apply in_or_juxt; Right; Exact h3.
Rewrite <- H0 in h.
Assert h1 : ~(In z X).
Intro h1; Apply h; Simpl; Apply in_or_juxt; Left; 
 Apply in_eoss1; Exact h1.
Assert h2 : ~(In z (names M)).
Intro h2; Apply h; Simpl; Apply in_or_juxt; Left; 
 Apply in_eoss2; Right; Exact h2.
Assert h3 : ~(In z (names M2)).
Intro h3; Apply h; Simpl; Apply in_or_juxt; Right; Exact h3.
Assert h4 : ~(In z Nil).
Exact [h]h.
Exact (not_in_subst h2 h3 h1 h4).
Qed.

Lemma rename_subst_commute_closed :
 (M,N:Adbmal;X0,X1,X2,Z:stack;x,y,z:name)
  (scb (juxt X0 (cons y Z)) M)
   ->(scb (juxt X1 (cons x (juxt X2 Z))) N)
    ->(rename (adbmal_subst (juxt X1 (cons x X2)) X0 M y N) x z (juxt X0 X1))
       =(adbmal_subst (juxt X1 (cons z X2)) X0 M y (rename N x z X1)).
Proof.
NewInduction M; Simpl; Intros N X0 X1 X2 Z x y z sm sn.
Case (in_dec n X0); Intro h; Simpl.
Case (in_dec n (juxt X0 X1)); Intro h0; Simpl.
Reflexivity.
Elim h0; Apply in_or_juxt; Left; Exact h.
Case (eq_dec y n); Intro h0; Simpl.
Rewrite rename_eoss; Reflexivity.
Rewrite rename_eoss.
Rewrite eoss_juxt.
Simpl.
Pattern 2 X1; Rewrite (juxt_nil_end X1).
Rewrite rename_eoss.
Simpl.
Case (eq_dec x x); Intro h1; Simpl.
Rewrite eoss_juxt.
Reflexivity.
Elim h1; Reflexivity.
Replace (cons n (juxt X0 X1)) with (juxt (cons n X0) X1);
[ Rewrite (IHM N (cons n X0) X1 X2 Z x y z (scb_abs_inv sm) sn) 
 | Reflexivity ].
Reflexivity.
NewInduction X0.
Simpl in sm.
Elim (scb_eos_inv sm); Intros h h0.
Case (eq_dec y n); Intro h1; Simpl.
Rewrite eoss_juxt.
Rewrite eoss_juxt.
Pattern 2 X1; Rewrite (juxt_nil_end X1).
Rewrite rename_eoss.
Simpl.
Case (eq_dec x x); Intro h2; Simpl.
Reflexivity.
Elim h2; Reflexivity.
Elim h1; Symmetry; Exact h.
Elim (scb_eos_inv sm); Intros h3 h4.
Case (eq_dec n a); Intro h; Simpl.
Case (eq_dec n a); Intro h0; Simpl.
Clear IHX0.
Rewrite (IHM N X0 X1 X2 Z x y z).
Reflexivity.
Exact h4.
Exact sn.
Elim (h0 h).
Elim (h h3).
Elim (scb_ap_inv sm); Intros sm1 sm2.
Rewrite (IHM1 N X0 X1 X2 Z x y z sm1 sn);
Rewrite (IHM2 N X0 X1 X2 Z x y z sm2 sn); Reflexivity.
Qed.

Lemma rename_subst_commute_open :
 (M,N:Adbmal;X0,X1,X2,X3:stack;x,y,z:name)
  ~(In z (names M))
    ->~(In z X0)
      ->~z=y
       ->(scb (juxt X0 (cons y (juxt X2 (cons x X3)))) M)
        ->(scb (juxt X1 (juxt X2 (cons x X3))) N)
         ->(rename (adbmal_subst X1 X0 M y N) x z (juxt X0 (juxt X1 X2)))
           =(adbmal_subst X1 X0 (rename M x z (juxt X0 (cons y X2))) 
                  y (rename N x z (juxt X1 X2))).
Proof.
NewInduction M; Intros N X0 X1 X2 X3 x y z h h1 h3 h4 h5; Simpl.
(* var n *)
Case (in_dec n (juxt X0 (cons y X2))); Intro h6; Simpl.
Case (in_dec n X0); Intro h7; Simpl.
Case (in_dec n (juxt X0 (juxt X1 X2))); Intro h8; Simpl.
Reflexivity.
Elim h8; Apply in_or_juxt; Left; Exact h7.
Case (eq_dec y n); Intro h8; Simpl.
Rewrite rename_eoss.
Reflexivity.
Rewrite rename_eoss.
Rewrite rename_eoss.
Simpl.
Case (in_dec n X2); Intro h9; Simpl.
Reflexivity.
Elim (in_juxt_or h6); Intro h10.
Elim (h7 h10).
Elim h10; Intro h11.
Elim (h8 h11).
Elim (h9 h11).
Case (eq_dec n x); Intro h7; Simpl.
Case (in_dec z X0); Intro h8.
Elim (h1 h8).
Case (eq_dec y z); Intro h9.
Elim h3; Symmetry; Exact h9.
Case (in_dec n X0); Intro h10; Simpl.
Elim h6; Apply in_or_juxt; Left; Exact h10.
Case (eq_dec y n); Intro h11.
Elim h6; Rewrite h11; Apply in_or_juxt; Right; Left; Reflexivity.
Rewrite rename_eoss.
Rewrite rename_eoss.
Simpl.
Case (in_dec n X2); Intro h12.
Elim h6; Apply in_or_juxt; Right; Right; Exact h12.
Case (eq_dec n x); Intro h13.
Reflexivity.
Elim (h13 h7).
Case (in_dec n X0); Intro h8; Simpl.
Elim h6; Apply in_or_juxt; Left; Exact h8.
Case (eq_dec y n); Intro h9.
Rewrite rename_eoss.
Reflexivity.
Rewrite rename_eoss.
Rewrite rename_eoss.
Simpl.
Case (in_dec n X2); Intro h10.
Elim h6; Apply in_or_juxt; Right; Right; Exact h10.
Case (eq_dec n x); Intro h11.
Elim (h7 h11).
Reflexivity.
(* abs n M *)
Assert h6 : ~(In z (cons n X0)).
Intro h6; Elim h6; Intro h7.
Apply h; Left; Exact h7.
Exact (h1 h7).
Assert h7 := (scb_abs_inv h4).
Assert h8 : ~(In z (names M)).
Intro h8; Apply h; Right; Exact h8.
Replace (cons n (juxt X0 (cons y X2)))
 with (juxt (cons n X0) (cons y X2)).
Replace (cons n (juxt X0 (juxt X1 X2)))
 with (juxt (cons n X0) (juxt X1 X2)).
Rewrite (IHM N (cons n X0) X1 X2 X3 x y z h8 h6 h3 h7 h5).
Reflexivity.
Reflexivity.
Reflexivity.
(* eos n M *)
NewDestruct X0; Simpl; Simpl in h4.
Elim (scb_eos_inv h4); Intros h6 h7.
Case (eq_dec n y); Intro h8.
Case (eq_dec y n); Intro h9; Simpl.
Case (eq_dec y n); Intro h10.
Rewrite rename_eoss.
Reflexivity.
Elim (h10 h9).
Elim h9; Symmetry; Exact h8.
Elim (h8 h6).
Elim (scb_eos_inv h4); Intros h6 h7.
Case (eq_dec n n0); Intro h8; Simpl.
Case (eq_dec n n0); Intro h9; Simpl.
Rewrite IHM with 4:=h7.
Reflexivity.
Intro h10; Apply h; Right; Exact h10.
Intro h10; Apply h1; Right; Exact h10.
Exact h3.
Exact h5.
Elim (h9 h8).
Elim (h8 h6).
(* ap M1 M2  *)
Elim (scb_ap_inv h4); Intros h6 h7.
Simpl in h.
Rewrite IHM1 with  4:=h6.
Rewrite IHM2 with  4:=h7.
Reflexivity.
Intro h8; Apply h; Apply in_or_juxt; Right; Exact h8.
Exact h1.
Exact h3.
Exact h5.
Intro h8; Apply h; Apply in_or_juxt; Left; Exact h8.
Exact h1.
Exact h3.
Exact h5.
Qed.

Lemma subst_rename_commute_open :
 (M,N:Adbmal;X,Y,X0,W:stack;x,y,z:name)
  ~(In z (names M))
   ->(scb (juxt X0 (cons y (juxt Y (cons x W)))) M)
    ->(rename (adbmal_subst X (juxt X0 (cons y Y)) M x N) y z X0)
       =(adbmal_subst X (juxt X0 (cons z Y))(rename M y z X0) x N).
Proof.
NewInduction M; Intros N X Y X0 W x y z d b.
Simpl.
NewDestruct (in_dec n X0); Simpl.
NewDestruct (in_dec n (juxt X0 (cons y Y))); Simpl.
NewDestruct (in_dec n X0); Simpl.
NewDestruct (in_dec n (juxt X0 (cons z Y))); Simpl.
Reflexivity.
Elim n0; Apply in_or_juxt; Left; Exact i.
Elim n0; Exact i.
Elim n0; Apply in_or_juxt; Left; Exact i.
NewDestruct (in_dec n (juxt X0 (cons y Y))); Simpl.
NewDestruct (in_dec n X0); Simpl.
Elim (n0 i0).
NewDestruct (eq_dec n y); Simpl.
NewDestruct (in_dec z (juxt X0 (cons z Y))); Simpl.
Reflexivity.
Elim n2; Apply in_or_juxt; Right; Left; Reflexivity.
NewDestruct (in_dec n (juxt X0 (cons z Y))); Simpl.
Reflexivity.
Elim n3; Apply in_or_juxt; Right; Right.
Elim (in_juxt_or i); Intro h.
Elim (n0 h).
Elim h; Intro h0.
Elim n2; Symmetry; Exact h0.
Exact h0.
NewDestruct (eq_dec x n); Simpl.
NewDestruct (eq_dec n y); Simpl.
Elim n1; Apply in_or_juxt; Right; Left; Symmetry; Exact e0.
NewDestruct (in_dec n (juxt X0 (cons z Y))); Simpl.
Elim (in_juxt_or i); Intro h.
Elim (n0 h).
Elim h; Intro h0.
Elim d; Left; Symmetry; Exact h0.
Elim n1; Apply in_or_juxt; Right; Right; Exact h0.
NewDestruct (eq_dec x n); Simpl.
Pattern 2 X0; Rewrite (juxt_nil_end X0).
Rewrite eoss_juxt; Rewrite rename_eoss.
Simpl.
NewDestruct (eq_dec y y).
Rewrite eoss_juxt; Reflexivity.
Elim n4; Reflexivity.
Elim (n4 e).
Simpl.
Pattern 2 X0; Rewrite (juxt_nil_end X0).
Rewrite eoss_juxt; Rewrite rename_eoss.
Simpl.
NewDestruct (eq_dec y y).
NewDestruct (eq_dec n y).
Elim n1; Apply in_or_juxt; Right; Left; Symmetry; Exact e0.
Simpl.
NewDestruct (in_dec n (juxt X0 (cons z Y))); Simpl.
Elim (in_juxt_or i); Intro h.
Elim (n0 h).
Elim h; Intro h0.
Elim d; Left; Symmetry; Exact h0.
Elim n1; Apply in_or_juxt; Right; Right; Exact h0.
NewDestruct (eq_dec x n); Simpl.
Elim (n2 e0).
Rewrite eoss_juxt; Reflexivity.
Elim n3; Reflexivity.
(* abs *)
Simpl.
Assert h : ~(In z (names M)).
Intro h; Apply d; Right; Exact h.
Apply (f_equal Adbmal).
Exact (IHM N X Y (cons n X0) W x y z h (scb_abs_inv b)).
(* eos *)
Elim (scb_eos_inv2 b); Intros U h; Elim h; Clear h; Intros h0 h1.
NewDestruct X0; Simpl; Simpl in h0; Injection h0; Intros h2 h3.
NewDestruct (eq_dec n y); Simpl.
NewDestruct (eq_dec y n); Simpl.
NewDestruct (eq_dec z z).
Reflexivity.
Elim n0; Reflexivity.
Elim (n0 h3).
Elim n0; Symmetry; Exact h3.
NewDestruct (eq_dec n n0); Simpl.
NewDestruct (eq_dec n n0); Simpl.
Rewrite <- h2 in h1.
Rewrite IHM with 2:=h1.
Reflexivity.
Intro h4; Apply d; Right; Exact h4.
Elim (n1 e).
Elim n1; Symmetry; Exact h3.
(* ap *)
Elim (scb_ap_inv b); Intros b1 b2.
Simpl.
Rewrite IHM1 with 2:=b1.
Rewrite IHM2 with 2:=b2.
Reflexivity.
Intro h; Apply d; Simpl; Apply in_or_juxt; Right; Exact h.
Intro h; Apply d; Simpl; Apply in_or_juxt; Left; Exact h.
Qed.

(* alpha conversion *)

Inductive alpha_conv : Adbmal->Adbmal->Prop :=
| alpha_conv_rule : (M:Adbmal;x,y:name)
    ~(In y (names M))->(alpha_conv (abs x M)(abs y (rename M x y Nil)))
| alpha_conv_abs : (M,N:Adbmal;x:name)
    (alpha_conv M N)->(alpha_conv (abs x M)(abs x N))
| alpha_conv_eos : (M,N:Adbmal;x:name)
    (alpha_conv M N)->(alpha_conv (eos x M)(eos x N))
| alpha_conv_apl : (M,M',N:Adbmal)
    (alpha_conv M M')->(alpha_conv (ap M N)(ap M' N))
| alpha_conv_apr : (M,M',N:Adbmal)
    (alpha_conv M M')->(alpha_conv (ap N M)(ap N M')).

(* equivalence closure of alpha_conv *)

Definition church := (Rhat alpha_conv).

Lemma alpha_conv_cxt_congr :
 (c:Adbmal->Adbmal)(cxt c)
   ->(t,t':Adbmal)(alpha_conv t t')->(alpha_conv (c t)(c t')).
Proof.
NewInduction 1.
Intros; Assumption.
Intros; Apply IHcxt1; Apply IHcxt2; Assumption.
Intros; Apply alpha_conv_abs; Assumption.
Intros; Apply alpha_conv_eos; Assumption.
Intros; Apply alpha_conv_apl; Assumption.
Intros; Apply alpha_conv_apr; Assumption.
Qed.

Lemma church_cxt_congr :
 (c:Adbmal->Adbmal)(cxt c)
   ->(t,t':Adbmal)(church t t')->(church (c t)(c t')).
Proof.
NewInduction 2; Red.
Apply Rhat_ext; Apply alpha_conv_cxt_congr; Assumption.
Apply Rhat_refl.
Apply Rhat_symm; Assumption.
Exact (Rhat_trans IHRhat1 IHRhat2).
Qed.

Lemma alpha_conv_rule_to_kahrs' :
 (M:Adbmal;x,y:name;Z:stack)
  ~(In y (names M))
   ->~(In y Z)
     ->(kahrs' M (snoc x Z) (rename M x y Z) (snoc y Z)).
Proof.
Induction M; Simpl.
Intros z x y Z h.
Assert h0 : ~z=y.
Intro h0; Apply h; Left; Exact h0.
Case (eq_dec z x); Intro h1; Simpl.
NewInduction Z; Simpl.
Case (in_dec z Nil); Intro h2; Simpl.
Elim h2.
Intro h3; Clear h2 h3.
Rewrite h1; Apply kahrs_var2; Reflexivity.
Intro h2.
Generalize IHZ; Clear IHZ.
Case (in_dec z Z); Intro h3; Simpl.
Intro ih.
Case (in_dec z (cons a Z)); Intro h4; Simpl.
Case (eq_dec z a); Intro h5.
Rewrite h5.
Apply kahrs_var2.
Rewrite length_snoc; Rewrite length_snoc; Reflexivity.
Apply kahrs_var3.
Exact h5.
Exact h5.
Apply ih.
Intro h6; Apply h2; Right; Exact h6.
Elim h4; Right; Exact h3.
Case (in_dec z (cons a Z)); Intro h4; Simpl.
Elim h4; Intro h5.
Rewrite h5.
Intro ih.
Apply kahrs_var2.
Rewrite length_snoc; Rewrite length_snoc; Reflexivity.
Elim h3; Exact h5.
Assert h6 : ~z=a.
Intro h5; Apply h4; Left; Symmetry; Exact h5.
Intro ih.
Apply kahrs_var3.
Exact h6.
Intro h5; Apply h2; Left; Symmetry; Exact h5.
Apply ih.
Intro h5; Apply h2; Right; Exact h5.
NewInduction Z; Simpl.
Case (in_dec z Nil); Intros h2 h3.
Elim h2.
Clear h2 h3.
Apply kahrs_var3.
Exact h1.
Exact h0.
Apply kahrs_var1.
Intro h2.
Assert h3 : ~(In y Z).
Intro h3; Apply h2; Right; Exact h3.
Generalize (IHZ h3); Clear IHZ.
Case (in_dec z Z); Intro h4.
Case (in_dec z (cons a Z)); Intro h5.
Intro ih.
Case (eq_dec z a); Intro h6.
Rewrite h6.
Apply kahrs_var2.
Rewrite length_snoc; Rewrite length_snoc; Reflexivity.
Apply kahrs_var3.
Exact h6.
Exact h6.
Exact ih.
Elim h5; Right; Exact h4.
Case (in_dec z (cons a Z)); Intro h5.
Intro ih.
Case (eq_dec z a); Intro h6.
Rewrite h6.
Apply kahrs_var2.
Rewrite length_snoc; Rewrite length_snoc; Reflexivity.
Elim h5; Intro h7.
Elim h6; Symmetry; Exact h7.
Elim h4; Exact h7.
Assert h6 : ~z=a.
Intro h6; Apply h5; Left; Symmetry; Exact h6.
Intro ih.
Apply kahrs_var3.
Exact h6.
Exact h6.
Exact ih.
Intros z t ih x y Z h h0.
Apply kahrs_abs.
Assert h1 : ~z=y.
Intro h2; Apply h; Left; Exact h2.
Assert h2 : ~(In y (names t)).
Intro h2; Apply h; Right; Exact h2.
Assert h3 : ~(In y (cons z Z)).
Intro h3; Elim h3; Intro h4.
Exact (h1 h4).
Exact (h0 h4).
Exact (ih x y (cons z Z) h2 h3).
Simpl; Intros z t ih x y Z h.
Assert h1 : ~(In y (names t)).
Intro h2; Apply h; Right; Exact h2.
Assert h2 : ~z=y.
Intro h2; Apply h; Left; Exact h2.
Elim Z; Simpl.
Intro h3; Clear h3.
Case (eq_dec x z); Intro h3.
Rewrite h3.
Apply kahrs_eos2.
Apply kahrs_refl.
Apply kahrs_eos3.
Intro h4; Apply h3; Symmetry; Exact h4.
Exact h2.
Apply kahrs_refl.
Intros z' Z'.
LetTac eos_y_z := (Fix aux
                     {aux [l:stack] : Adbmal :=
                        Cases (l) of
                          nil => 
                           Cases (eq_dec x z) of
                             (left _) => (eos y t)
                           | (right _) => (eos z t)
                           end
                        | (cons z'0 l') => 
                           Cases (eq_dec z z'0) of
                             (left _) => (eos z (rename t x y l'))
                           | (right _) => (aux l')
                           end
                        end} Z').
Intros ihZ' h3.
Assert h4 := [e](h3 (or_introl ?? e)).
Assert h5 := [i](h3 (or_intror ?? i)).
Case (eq_dec z z'); Intro h6.
Rewrite h6.
Apply kahrs_eos2.
Exact (ih x y Z' h1 h5).
(* M = (eos z t); Z = Z'z'; ~z=z' *)
Cut (EX t':Adbmal | eos_y_z=(eos y t')\/eos_y_z=(eos z t')).
Intro c; Elim c; Intros t' h7; Elim h7; Intro h8; Rewrite h8; 
 Rewrite h8 in ihZ'.
Apply kahrs_eos3.
Exact h6.
Intro h9; Apply h4; Symmetry; Exact h9.
Exact (ihZ' h5).
Exact (kahrs_eos3 h6 h6 (ihZ' h5)).
Lazy Delta.
Clear h6 h5 h4 h3 ihZ'.
Induction Z'.
Case (eq_dec x z); Intro h3.
Exists t; Left; Reflexivity.
Exists t; Right; Reflexivity.
Case (eq_dec z a); Intro.
Exists (rename t x y Z'); Right; Reflexivity.
Elim HrecZ'; Intros t' H.
Exists t'.
Elim H; Intro H0.
Left; Exact H0.
Right; Exact H0.
Simpl; Intros t1 ih1 t2 ih2 x y Z h h0.
Assert h1 : ~(In y (names t1))/\~(In y (names t2)).
Split; Intro h1; Apply h.
Apply in_or_juxt; Left; Exact h1.
Apply in_or_juxt; Right; Exact h1.
Elim h1; Clear h1; Intros h1 h2.
Apply kahrs_ap.
Exact (ih1 x y Z h1 h0).
Exact (ih2 x y Z h2 h0).
Qed.

Lemma alpha_conv_rule_to_kahrs :
   (M:Adbmal; x,y:name)
    ~(In y (names M))
    ->(kahrs (abs x M) (abs y (rename M x y Nil))).
Proof.
Intros M x y h.
Red; Apply kahrs_abs.
Assert h0 : ~(In y Nil). 
Exact [h']h'.
Exact (alpha_conv_rule_to_kahrs' x h h0).
Qed.  

Lemma alpha_conv_to_kahrs : (t,u:Adbmal)(alpha_conv t u)->(kahrs t u).
Proof.
Intros t u h; Red; Elim h; Clear h t u.
Exact alpha_conv_rule_to_kahrs.
Intros M N x h ih.
Apply kahrs_abs.
Exact (kahrs_snoc1 x ih).
Intros M N x h ih.
Apply kahrs_eos1.
Exact ih.
Intros M M' N h ih.
Apply kahrs_ap.
Exact ih.
Apply kahrs_refl.
Intros M M' N h ih.
Apply kahrs_ap.
Apply kahrs_refl.
Exact ih.
Qed.

Lemma church_to_kahrs : 
 (t,u:Adbmal)(church t u)->(kahrs t u).
Proof.
Intros t u h; Elim h.
Exact alpha_conv_to_kahrs.
Exact [x](kahrs_refl x Nil).
Exact [x,y;_;h](kahrs_symm h).
Exact [x,y,z;_;h1;_;h2](kahrs_trans h1 h2).
Qed.

Lemma rename_skel_eq : 
 (x,y:name;M:Adbmal;Z:stack)(skeleton M)=(skeleton (rename M x y Z)).
Proof.
NewInduction M; Intro Z; Simpl.
Case (eq_dec n x); Case (in_dec n Z); Reflexivity.
Rewrite (IHM (cons n Z)); Reflexivity.
Case (eq_dec x n); Intro h; Simpl; NewInduction Z.
Reflexivity.
Case (eq_dec n a); Intro h0; Simpl.
Rewrite (IHM Z); Reflexivity.
Exact IHZ.
Reflexivity.
Case (eq_dec n a); Intro h0; Simpl.
Rewrite (IHM Z); Reflexivity.
Exact IHZ.
Rewrite (IHM1 Z); Rewrite (IHM2 Z); Reflexivity.
Qed.

Lemma kahrs_to_church_skel_ind :
 (s:skel;t,u:Adbmal)
  (skeleton t)=s
   ->(kahrs t u)
    ->(church t u).
Proof. (* by induction on skeleton of t; use rename_skel_eq *)
Red. Induction s.
(* var_skel *)
Destruct t.
Intros x u p h; Inversion h; Apply Rhat_refl.
Intros n t' u p; Discriminate p.
Intros n t' u p; Discriminate p.
Intros t1 t2 u p; Discriminate p.
(* abs_skel *)
Intros s' ih t; Case t.
Intros x u p; Discriminate p.
Intros x t' u p h.
Inversion h.
Rewrite <- H2 in h.
Rewrite <- H1.
Rewrite <- H1 in p.
Rewrite <- H1 in h.
Rewrite <- H1 in H4.
Simpl in p; Injection p; Intro p'.
LetTac z := (fresh (names (ap M N))).
Assert h0 := (fresh_not_in 1!(names (ap M N))).
Assert h1 : ~(In z (names M))/\~(In z (names N)).
Split; Intro h1; Apply h0; Simpl; Apply in_or_juxt.
Left; Exact h1.
Right; Exact h1.
Elim h1; Clear h1; Intros h1 h2.
Assert h3 : (church (abs z (rename M x z Nil)) (abs x M)).
   Red; Apply Rhat_symm; Apply Rhat_ext; Apply alpha_conv_rule; Exact h1.
Assert h4 : (church (abs y N) (abs z (rename N y z Nil))).
   Red; Apply Rhat_ext; Apply alpha_conv_rule; Exact h2.
Assert h5 := 
 (kahrs_trans (church_to_kahrs h3) 
  (kahrs_trans h (church_to_kahrs h4))).
Apply (Rhat_trans 2!alpha_conv 3!(abs x M) 4!(abs z (rename M x z Nil))).
Apply Rhat_symm; Exact h3.
Apply (Rhat_trans 2!alpha_conv 3!(abs z (rename M x z Nil)) 4!(abs z (rename N y z Nil))).
Assert h6 : (church (rename M x z Nil)(rename N y z Nil)).
Apply ih.
Rewrite <- rename_skel_eq.
Exact p'.
Inversion_clear h5.
Assert h5 : (cons z (nil name))=(snoc z Nil);
[ Reflexivity | Rewrite h5 in H5 ].
Exact (kahrs_snoc2 H5).
Exact (church_cxt_congr (cxt_abs z) h6).
Apply Rhat_symm; Exact h4.
Intros x t' u p; Discriminate p.
Intros t1 t2 u p; Discriminate p.
(* eos_skel *)
Intros s' ih.
Destruct t.
Intros x u p; Discriminate p.
Intros x t' u p; Discriminate p.
Intros x t' u p h; Injection p; Fold skeleton; Intro p'.
Inversion_clear h.
Apply (church_cxt_congr (cxt_eos x)).
Exact (ih t' N p' H).
Intros t1 t2 u p; Discriminate p.
(* ap_skel *)
Intros s1 ih1 s2 ih2 t; Case t.
Intros x u p; Discriminate p.
Intros x t' u p; Discriminate p.
Intros x t' u p; Discriminate p.
Intros t1 t2 u p; Injection p; Fold skeleton; Intros p2 p1 h.
Inversion_clear h.
Exact (Rhat_trans
        (church_cxt_congr (cxt_apl t2) (ih1 t1 N1 p1 H))
        (church_cxt_congr (cxt_apr N1) (ih2 t2 N2 p2 H0))).
Qed.

Lemma kahrs_to_church : (t,u:Adbmal)(kahrs t u)->(church t u).
Proof [t,u;h](kahrs_to_church_skel_ind 
              (refl_equal ? (skeleton t)) h).

Lemma same_kahrs_church : (same_rel kahrs church).
Proof
 (conj (incl_rel kahrs church) 
       (incl_rel church kahrs)
       ([x,y;H](kahrs_to_church H))
       ([x,y;H](church_to_kahrs H))
 ).

Fixpoint FV [t:Adbmal] : stack->stack :=
[X] Cases t of
|(var x)    => Cases (in_dec x X) of (left _) => Nil | _ => (cons x Nil) end
|(abs x t') => (FV t' (cons x X))
|(eos x t') => (Fix FV_aux {FV_aux [l:stack] : stack :=
                Cases l of
                | nil         => (FV t' Nil)
                |(cons x' l') => Cases (eq_dec x x') of
                                 |(left _) => (FV t' l')
                                 | _       => (FV_aux l')
                                 end
                end} X)
|(ap t1 t2) => (juxt (FV t1 X)(FV t2 X))
end.

Lemma FV_eos_jump :
 (M:Adbmal;x:name;Y,X:stack)
  ~(In x X)
   ->(FV (eos x M) (juxt X Y)) = (FV (eos x M) Y).
Proof.
NewInduction X; Simpl; Intro h.
Reflexivity.
Elim (dmx h); Intros h0 h1.
Case (eq_dec x a); Intro h2.
Elim h0; Symmetry; Exact h2.
Exact (IHX h1).
Qed.

Lemma bal_fv_nil : (M:Adbmal;X:stack)(bal X M)->(FV M X)=Nil.
Proof.
NewInduction M; Intros X b; Simpl.
Elim (bal_var_inv b); Intros X' e; Rewrite e.
Case (in_dec n (cons n X')); Intros h.
Reflexivity.
Elim h; Left; Reflexivity.
Exact (IHM (cons n X) (bal_abs_inv b)).
Elim (bal_eos_inv2 b); Intros X' h; Elim h; Clear h; Intros e b'.
Rewrite e.
Case (eq_dec n n); Intro h.
Exact (IHM X' b').
Elim h; Reflexivity.
Elim (bal_ap_inv b); Intros b1 b2.
Rewrite (IHM1 X b1); Exact (IHM2 X b2).
Qed.

Lemma FV_sub1 :
 (M:Adbmal;X,Y,Z:stack)(sub (FV M (juxt X (juxt Y Z))) (FV M (juxt X Z))).
Proof.
NewInduction M; Intros X Y Z; Simpl.
(* var n *)
Case (in_dec n (juxt X Z)); Intro h; Case (in_dec n (juxt X (juxt Y Z))); Intro h0.
Apply sub_nil.
Elim h0; Apply in_or_juxt; Elim (in_juxt_or h); Intro h1.
Left; Exact h1.
Right; Apply in_or_juxt; Right; Exact h1.
Apply sub_nil.
Apply sub_refl.
(* abs n M *)
Exact (IHM (cons n X) Y Z).
(* eos n M *)
NewInduction X.
NewInduction Y.
Apply sub_refl.
Simpl; Case (eq_dec n a); Intro h.
Clear IHY; NewInduction Z.
Exact (IHM Nil Y Nil).
Case (eq_dec n a0); Intro h0.
Rewrite juxt_snoc.
Exact (IHM Nil (snoc a0 Y) Z).
Apply sub_trans with l2:=(FV M (juxt Y Z)).
Exact (IHM Y (cons a0 Nil) Z).
Exact IHZ.
Exact IHY.
Simpl; Case (eq_dec n a); Intro h.
Apply IHM.
Exact IHX.
(* ap M1 M2 *)
Simpl; Apply sub_juxt; [ Apply IHM1 | Apply IHM2 ].
Qed.

Fixpoint eos_skel_free [s:skel] : Prop :=
Cases s of 
  var_skel       => True
|(abs_skel s')   => (eos_skel_free s')
|(eos_skel _)    => False 
|(ap_skel s1 s2) => (eos_skel_free s1)/\(eos_skel_free s2)
end.

Definition eos_free := [t:Adbmal](eos_skel_free (skeleton t)).

Lemma eos_free_scb :
 (M:Adbmal;X:stack)
 (eos_free M)
  ->(scb X M).
NewInduction M; Intros X h.
Apply scb_var.
Apply scb_abs; Apply IHM; Exact h.
Elim h.
Elim h; Intros h1 h2.
Apply scb_ap; [ Exact (IHM1 X h1) | Exact (IHM2 X h2) ].
Qed.

Lemma rename_eos_free_in_stack :
 (x,y:name;M:Adbmal;X:stack)
  (eos_free M)
   ->(In x X)
    ->(rename M x y X)=M.
Proof.
NewInduction M; Intros X h h0; Simpl.
Case (in_dec n X); Intro h1.
Reflexivity.
Case (eq_dec n x); Intro h2.
Elim h1; Rewrite h2; Exact h0.
Reflexivity.
Rewrite IHM.
Reflexivity.
Exact h.
Right; Exact h0.
Elim h.
Elim h; Intros h1 h2.
Rewrite (IHM1 X h1 h0); Rewrite (IHM2 X h2 h0); Reflexivity.
Qed.

Lemma FV_sub2 :
 (M:Adbmal)(eos_free M)->
  (X,Y,Z:stack)
   (disjoint Y (FV M X))
    ->(sub (FV M (juxt X Z))(FV M (juxt X (juxt Y Z)))).
Proof.
NewInduction M; Intros h X Y Z.
Clear h.
Simpl.
Case (in_dec n X); Intro h.
Intro h0; Clear h0.
Case (in_dec n (juxt X Z)); Intro h0.
Apply sub_nil.
Elim h0; Apply in_or_juxt; Left; Exact h.
Case (in_dec n (juxt X Z)); Intro h0.
Intro h1; Apply sub_nil.
Intro h1.
Case (in_dec n (juxt X (juxt Y Z))); Intro h2.
Assert h3 : ~(In n Y).
Intro h3; Apply (h1 n h3); Left; Reflexivity.
Elim (in_juxt_or h2); Intro h4.
Elim (h h4).
Elim (in_juxt_or h4); Intro h5.
Elim (h3 h5).
Elim h0; Apply in_or_juxt; Right; Exact h5.
Apply sub_refl.
Intro h0.
Exact (IHM h (cons n X) Y Z h0).
Elim h.
Elim h; Intros h0 h1 h2.
Simpl in h2; Elim (disjoint_juxt_and h2); Intros h3 h4.
Exact (sub_juxt (IHM1 h0 X Y Z h3) (IHM2 h1 X Y Z h4)).
Qed.

Lemma FV_sub3 :
 (M:Adbmal;X,Y:stack)
  (scb (juxt X Y) M) (* this ass nec? *)
   ->(sub (FV M X) (juxt Y (FV M (juxt X Y)))).
Proof.
NewInduction M; Intros X Y b.
Simpl.
Case (in_dec n X); Intro h.
Apply sub_nil.
Intros u h1; Elim h1; Intro h2; [ Rewrite <- h2; Clear h1 h2 u | Elim h2 ].
Case (in_dec n (juxt X Y)); Intro h0.
Apply in_or_juxt.
Elim (in_juxt_or h0); Intro h1.
Right; Exact (h h1).
Left; Exact h1.
Apply in_or_juxt; Right; Left; Reflexivity.
Exact (IHM (cons n X) Y (scb_abs_inv b)).
Elim (scb_eos_inv2 b); Intros X' h; Elim h; Clear h; Intros e b'.
Rewrite e.
NewDestruct X; Simpl.
Case (eq_dec n n); Intro h; [ Clear h | Elim h; Reflexivity ].
Simpl in e; Rewrite e; Intros u h; Simpl; Right;
Exact (IHM Nil X' b' u h).
Simpl in e; Injection e; Intros e1 e2.
Rewrite e2.
Case (eq_dec n n); Intro h; [ Clear h | Elim h; Reflexivity ].
Rewrite <- e1.
Rewrite <- e1 in b'.
Exact (IHM l Y b').
Elim (scb_ap_inv b); Intros b1 b2.
Simpl.
Intros u h; Apply in_or_juxt; Elim (in_juxt_or h); Intro h0.
Elim (in_juxt_or (IHM1 X Y b1 u h0)); Intro h1.
Left; Exact h1.
Right; Apply in_or_juxt; Left; Exact h1.
Elim (in_juxt_or (IHM2 X Y b2 u h0)); Intro h1.
Left; Exact h1.
Right; Apply in_or_juxt; Right; Exact h1.
Qed.

Lemma kahrs_eos_free : 
(M,N:Adbmal;X,Y:stack)(kahrs' M X N Y)->(eos_free M)->(eos_free N).
Proof.
Intros M N X Y h.
Unfold eos_free; Rewrite (kahrs_skel h).
Exact [d]d.
Qed.

Lemma kahrs_var_repl_tails : 
 (x,y:name;U,V,U',V',X,Y:stack)
  (In x X)
   ->(length X)=(length Y)
    ->(length U')=(length V')
     ->(kahrs' (var x) (juxt X U) (var y) (juxt Y V))
      ->(kahrs' (var x) (juxt X U') (var y) (juxt Y V')).
Proof.
NewInduction X; Intros Y h.
Elim h.
NewDestruct Y; Simpl; Intros h0 h1 h2.
Discriminate h0.
Injection h0; Clear h0; Intro h0.
Inversion_clear h2.
Apply kahrs_var2.
Rewrite length_juxt in H; Rewrite length_juxt in H; 
Rewrite length_juxt; Rewrite length_juxt; Rewrite h0; Rewrite h1; Reflexivity.
Assert h2 : (In x X).
Elim h; Intro h3.
Elim H; Symmetry; Exact h3.
Exact h3.
Exact (kahrs_var3 H H0 (IHX l h2 h0 h1 H1)).
Qed.

Lemma kahrs_var_top : 
 (x,y:name;X1,X2,Y1,Y2:stack)
  (length X1)=(length Y1)
   ->~(In x X1)
    ->~(In y Y1)
     ->(kahrs' (var x) (juxt X1 X2) (var y) (juxt Y1 Y2))
        <->(kahrs' (var x) X2 (var y) Y2).
Proof.
NewInduction X1; NewDestruct Y1; Simpl; Intros Y2 h h0 h1.
Split; Exact [d]d.
Discriminate h.
Discriminate h.
Injection h; Clear h; Intro h.
Elim (dmx h0); Intros h2 h3.
Elim (dmx h1); Intros h4 h5.
Split; Intro h6.
Inversion h6.
Elim h2; Symmetry; Assumption.
Exact (proj1 ?? (IHX1 X2 l Y2 h h3 h5) H7).
Apply kahrs_var3.
Intro h7; Apply h2; Symmetry; Exact h7.
Intro h7; Apply h4; Symmetry; Exact h7.
Exact (proj2 ?? (IHX1 X2 l Y2 h h3 h5) h6).
Qed.

Lemma kahrs_var_in_in : 
 (x,y:name;X1,X2,Y1,Y2:stack)
  (kahrs' (var x) (juxt X1 X2) (var y) (juxt Y1 Y2))
   ->(length X1)=(length Y1)
    ->(In x X1)
     ->(In y Y1).
Proof.
NewInduction X1.
Intros X2 Y1 Y2 h h0 h1; Elim h1.
NewDestruct Y1; Simpl; Intros Y2 h h0 h1.
Discriminate h0.
Injection h0; Clear h0; Intro h0.
Inversion_clear h.
Left; Reflexivity.
Right.
Apply (IHX1 X2 l Y2 H1 h0).
Elim h1; Intro h2.
Elim H; Symmetry; Exact h2.
Exact h2.
Qed.

Lemma kahrs_var_rm_top : 
 (x,y:name;X1,X2,Y1,Y2:stack)
  (length X1)=(length Y1)
   ->~(In x X1)
 (*   ->~(In y Y1) *) 
     ->(kahrs' (var x) (juxt X1 X2) (var y) (juxt Y1 Y2))
        ->(kahrs' (var x) X2 (var y) Y2).
Proof
 [x,y;X1,X2,Y1,Y2;h;h0;h1]
  (proj1 ?? 
   (kahrs_var_top X2 Y2 h h0 [d](h0 (kahrs_var_in_in (kahrs_symm h1)(sym_eq ??? h) d)))
   h1).
  
Lemma kahrs_var_weak : 
 (x,y:name;X1,X2,Y1,Y2:stack)
  (length X1)=(length Y1)
   ->~(In x X1)
    ->~(In y Y1)
     ->(kahrs' (var x) X2 (var y) Y2)
      ->(kahrs' (var x) (juxt X1 X2) (var y) (juxt Y1 Y2)).
Proof [x,y;X1,X2,Y1,Y2;h;h0;h1;h2](proj2 ?? (kahrs_var_top X2 Y2 h h0 h1) h2).

Lemma kahrs_var_inj :
 (x,y:name;X:stack)
  (kahrs' (var x) X (var y) X)
   ->x=y.
Proof.
NewInduction X; Simpl; Intro h.
Inversion h; Reflexivity.
Inversion_clear h.
Reflexivity.
Apply IHX; Assumption.
Qed.

Lemma kahrs_eoss2 : 
 (M,N:Adbmal;X,Y,V,W:stack)
  (length X)=(length Y)
   ->(kahrs' M V N W)
    ->(kahrs' (eoss X M) (juxt X V) (eoss Y N) (juxt Y W)).
Proof.
NewInduction X; NewDestruct Y; Simpl; Intros V W h.
Exact [d]d.
Discriminate h.
Discriminate h.
Injection h; Clear h; Intros h h0.
Apply kahrs_eos2.
Exact (IHX l V W h h0).
Qed.

Lemma kahrs_eoss2_inv : 
 (M,N:Adbmal;X,Y,V,W:stack)
  (length X)=(length Y)
   ->(kahrs' (eoss X M) (juxt X V) (eoss Y N) (juxt Y W))
    ->(kahrs' M V N W).
Proof.
NewInduction X; NewDestruct Y; Simpl; Intros V W h.
Exact [d]d.
Discriminate h.
Discriminate h.
Injection h; Clear h; Intros h h0.
Inversion_clear h0.
Exact (IHX l V W h H).
Elim H; Reflexivity.
Qed.

Lemma kahrs_FV_eq' : 
 (M,N:Adbmal)
  (skeleton M)=(skeleton N) (* for proof convenience only *)
   ->(X1,X2,X:stack)
      (length X1)=(length X2)
       ->(kahrs' M (juxt X1 X) N (juxt X2 X))
        ->(FV M X1)=(FV N X2).
Proof.
NewInduction M; NewDestruct N; Intro h.
Intros X1 X2 X d h0.
Simpl; Case (in_dec n X1); Intro h1; Case (in_dec n0 X2); Intro h2.
Reflexivity.
Elim h2; Exact (kahrs_var_in_in h0 d h1).
Elim h1; Exact (kahrs_var_in_in (kahrs_symm h0)(sym_eq ??? d) h2).
Rewrite (kahrs_var_inj (kahrs_var_rm_top d h1 h0)); Reflexivity.
Discriminate h.
Discriminate h.
Discriminate h.
Discriminate h.
Rename a into N; Clear a.
Simpl in h; Injection h; Clear h; Intro h.
Intros X1 X2 X d h0.
Inversion_clear h0.
Exact (IHM N h (cons n X1) (cons n0 X2) X (eq_S ?? d) H).
Discriminate h.
Discriminate h.
Discriminate h.
Discriminate h.
Rename a into N; Clear a.
Simpl in h; Injection h; Clear h; Intro h.
NewInduction X1; NewDestruct X2; Intros X h0.
Clear h0.
Simpl; NewInduction X; Intro h0; Inversion_clear h0.
Exact (IHM N h Nil Nil Nil (refl_equal nat O) H). 
Exact (IHM N h Nil Nil X (refl_equal nat O) H).
Exact (IHX H1).
Discriminate h0.
Discriminate h0.
Simpl in h0; Injection h0; Clear h0; Intro h0.
Intro h1; Simpl in h1; Inversion_clear h1.
Simpl; Case (eq_dec a a); Intro h1.
Case (eq_dec n1 n1); Intro h2.
Exact (IHM N h X1 l X h0 H).
Elim h2; Reflexivity.
Elim h1; Reflexivity.
Simpl; Case (eq_dec n a); Intro h1.
Elim (H h1).
Case (eq_dec n0 n1); Intro h2.
Elim (H0 h2).
Exact (IHX1 l X h0 H1).
Discriminate h.
Discriminate h.
Discriminate h.
Discriminate h.
Rename a into N1; Clear a.
Rename a0 into N2; Clear a0.
Simpl in h; Injection h; Clear h; Intros h h0.
Intros X1 X2 X h1 h2.
Inversion_clear h2.
Simpl; Rewrite (IHM1 N1 h0 X1 X2 X h1 H); Rewrite (IHM2 N2 h X1 X2 X h1 H0); Reflexivity.
Qed.

Lemma kahrs_FV_eq : 
 (M,N:Adbmal;X,Y,Z:stack)
  (kahrs' M (juxt X Z) N (juxt Y Z))
   ->(FV M X)=(FV N Y).
Proof.
Intros M N X Y Z h.
Assert h0 := (kahrs_list_length h).
Rewrite length_juxt in h0; Rewrite length_juxt in h0.
Assert h1 :=  (simpl_plus_r h0).
Exact (kahrs_FV_eq' (kahrs_skel h) h1 h).
Qed.

Lemma kahrs_FV_eq1 : 
 (M,N:Adbmal;X,Y:stack)(kahrs' M X N Y)->(FV M X)=(FV N Y).
Proof.
Intros M N X Y h.
Rewrite (juxt_nil_end X) in h; Rewrite (juxt_nil_end Y) in h.
Exact (kahrs_FV_eq h).
Qed.

Lemma kahrs_FV_eq2 : 
 (M,N:Adbmal;X:stack)(kahrs' M X N X)->(FV M Nil)=(FV N Nil).
Proof [M,N;X;h](kahrs_FV_eq 3!Nil 4!Nil h).

Fixpoint jump_min [Y:stack] : stack->stack :=
[X] Cases Y of 
| nil                => Nil
|((cons y ys) as Y') => 
  Cases X of 
  | nil        => Y' 
  |(cons x xs) => 
    Cases (eq_dec x y) of
    |(left _)  => (jump_min ys xs)
    |(right _) => (jump_min ys X)
    end
  end
end.

Lemma FV_jump_min : (M:Adbmal;Y,X:stack)(FV (eoss X M) Y) = (FV M (jump_min Y X)).
Proof.
NewInduction Y.
Simpl.
NewInduction X; Auto.
NewInduction X; Simpl.
Reflexivity.
Case (eq_dec a0 a); Intro h.
Apply IHY.
Exact (IHY (cons a0 X)).
Qed.

Lemma jump_min_emp : (X:stack)(jump_min X X)=Nil.
Proof.
NewInduction X.
Reflexivity.
Simpl; Case (eq_dec a a); Intro h.
Exact IHX.
Elim h; Reflexivity.
Qed.

Lemma FV_eoss_rm_top_stack :
 (M:Adbmal;Y,Z:stack)
  (FV (eoss Z M) (juxt Z Y))=(FV M Y).
Proof.
NewInduction Z; Simpl.
Reflexivity.
Case (eq_dec a a); Intro h.
Exact IHZ.
Elim h; Reflexivity.
Qed.

Lemma FV_eoss_nil : (M:Adbmal;X:stack)(FV (eoss X M) Nil)=(FV M Nil).
Proof.
NewInduction X.
Reflexivity.
Exact IHX.
Qed.

Lemma subst_FV_sub :
 (M,N:Adbmal;x:name;Z,X,Y:stack)
   (sub (FV (adbmal_subst X Z M x N) (juxt Z Y))
     (juxt (FV M (juxt Z (cons x (jump_min Y X)))) (FV N Y))).
Proof. 
NewInduction M; Intros N x Z X Y.
(* var *)
Simpl.
Case (in_dec n Z); Intro h; Simpl.
Case (in_dec n (juxt Z Y)); Intro h0.
Apply sub_nil.
Elim h0; Apply in_or_juxt; Left; Exact h.
Case (eq_dec n x); Intro h0; Case (eq_dec x n); Intro h1.
Rewrite FV_eoss_rm_top_stack.
Intros a h2; Apply in_or_juxt; Right; Exact h2.
Elim h1; Symmetry; Exact h0.
Elim h0; Symmetry; Exact h1.
Rewrite FV_eoss_rm_top_stack.
Rewrite FV_jump_min.
Simpl.
Case (in_dec n (jump_min Y X)); Intro h2.
Apply sub_nil.
Case (in_dec n (juxt Z (cons x (jump_min Y X)))); Intro h3.
Apply False_ind; Elim (in_juxt_or h3); Intro h4.
Exact (h h4).
Elim h4; [ Exact h1 | Exact h2 ].
Intros a h4; Apply in_or_juxt; Left; Exact h4.
(* abs *)
Exact (IHM N x (cons n Z) X Y).
(* eos *)
Case (in_dec n Z); Intro h.
Elim (in_split eq_dec h); Intros Z1 h0; Elim h0; Intros Z2 h1; Elim h1;
Clear h0 h1; Intros h0 h1.
Rewrite h0.
Rewrite (adbmal_subst_eos_clause1 M N x X Z2 h1).
Rewrite juxt_ass; Rewrite juxt_ass.
Rewrite (FV_eos_jump M (juxt (cons n Z2) (cons x (jump_min Y X))) h1).
Rewrite (FV_eos_jump (adbmal_subst X Z2 M x N) (juxt (cons n Z2) Y) h1).
Simpl; Case (eq_dec n n); Intro h2; [ Apply IHM | Elim h2; Reflexivity ].
Rewrite (FV_eos_jump M (cons x (jump_min Y X)) h).
Case (eq_dec x n); Intro h0.
Rewrite (adbmal_subst_eos_clause2 M N X h0 h).
Simpl; Case (eq_dec n x); Intro h1.
Rewrite FV_eoss_rm_top_stack.
Intros a h2; Apply in_or_juxt; Left.
Rewrite <- FV_jump_min; Exact h2.
Elim h1; Symmetry; Exact h0.
Rewrite (adbmal_subst_eos_clause3 M N X h0 h).
Rewrite FV_eoss_rm_top_stack.
Simpl; Case (eq_dec n x); Intro h1.
Elim h0; Symmetry; Exact h1.
Intros a h2; Apply in_or_juxt; Left.
Fold (FV (eos n M) (jump_min Y X)).
Rewrite (FV_jump_min (eos n M) Y X) in h2.
Exact h2.
(* ap *)
Simpl.
Intros a h.
Apply in_or_juxt.
Elim (in_juxt_or h); Intro h0.
Elim (in_juxt_or (IHM1 N x Z X Y a h0)); Intro h1.
Left; Apply in_or_juxt; Left; Exact h1.
Right; Exact h1.
Elim (in_juxt_or (IHM2 N x Z X Y a h0)); Intro h1.
Left; Apply in_or_juxt; Right; Exact h1.
Right; Exact h1.
Qed.

Lemma beta_FV_sub : (M,N:Adbmal)(adbmal_beta M N)->(Y:stack)(sub (FV N Y)(FV M Y)).
Proof.
NewInduction 1; Intro Y.
Exact (IHadbmal_beta (cons x Y)).
NewInduction Y; Simpl.
Exact (IHadbmal_beta Nil).
Case (eq_dec x a); Intro h.
Exact (IHadbmal_beta Y).
Exact IHY.
Simpl.
Apply sub_juxt.
Apply IHadbmal_beta.
Apply sub_refl.
Simpl; Apply sub_juxt.
Apply sub_refl.
Apply IHadbmal_beta.
Simpl.
Rewrite FV_jump_min.
Exact (subst_FV_sub 4!Nil 5!X 6!Y).
Qed.

Lemma not_in_renamed_term : 
 (x,z,z':name;M:Adbmal)
  ~z'=z
   ->~(In z (names M))
    ->(Y:stack)~(In z (names (rename M x z' Y))).
Proof.
Intros x z z' M h.
NewInduction M; Simpl.
Intros h0 Y.
Case (eq_dec n x); Intro h1; Case (in_dec n Y); Intro h2.
Exact h0.
Simpl; Intro h3; Elim h3; Intro h4.
Exact (h h4).
Exact h4.
Exact h0.
Exact h0.
Intros h0 Y h1.
Apply IHM with Y:=(cons n Y).
Intro h2; Apply h0; Right; Exact h2.
Elim h1; Intro h2.
Elim h0; Left; Exact h2.
Exact h2.
Intros h0 Y.
Case (eq_dec x n); Intro h1.
Elim Y; Simpl.
Intro h2; Elim h2; Intro h3.
Exact (h h3).
Apply h0; Right; Exact h3.
Intros m Y' IHY.
Case (eq_dec n m); Intro h2.
Simpl; Intro h3.
Apply IHM with Y:=Y'.
Intro h4; Apply h0; Right; Exact h4.
Elim h3; Intro h4.
Elim h0; Left; Exact h4.
Exact h4.
Exact IHY.
Elim Y; Simpl.
Exact h0.
Intros m Y' IHY.
Case (eq_dec n m); Intro h2.
Simpl; Intro h3.
Apply IHM with Y:=Y'.
Intro h4; Apply h0; Right; Exact h4.
Elim h3; Intro h4.
Elim h0; Left; Exact h4.
Exact h4.
Exact IHY.
Simpl; Intros h0 Y h1.
Elim (in_juxt_or h1); Intro h2.
Apply IHM1 with 2:=h2.
Intro h3; Apply h0; Apply in_or_juxt; Left; Exact h3.
Apply IHM2 with 2:=h2.
Intro h3; Apply h0; Apply in_or_juxt; Right; Exact h3.
Qed.

Lemma in_not_in : 
 (M:Adbmal;x,y:name)(In x (names M))->~(In y (names M))->~x=y.
Proof.
Intros M x y h h0 h1; Apply h0; Rewrite <- h1; Exact h.
Qed.

Lemma rename_eos_not_in : 
 (x,y,z:name;M:Adbmal;X,Y:stack)
  ~(In y X)
   ->(rename (eos y M) x z (juxt X Y))
      =(rename (eos y M) x z Y).
Proof.
NewInduction X.
Reflexivity.
Intros Y h.
Assert h0 : ~(In y X).
Intro h0; Apply h; Right; Exact h0.
Simpl.
Case (eq_dec y a); Intro h1; Simpl.
Elim h; Left; Symmetry; Exact h1.
Exact (IHX Y h0).
Qed.

Lemma kahrs_rename :
 (x,y:name;M:Adbmal;X,Y:stack)
  ~(In y Y)
   ->~(In y (names M))
   ->(kahrs' M (juxt Y (cons x X)) (rename M x y Y) (juxt Y (cons y X))).
Proof.
NewInduction M; Intros X Y h h0.
(* var *)
Simpl; Case (in_dec n Y); Intro h1.
Apply (kahrs_var_repl_tails 2!n 3!X 4!X 5!(cons x X) 6!(cons y X) 7!Y 8!Y h1).
Reflexivity.
Reflexivity.
Apply kahrs_refl.
Case (eq_dec n x); Intro h2.
Apply (kahrs_var_weak 1!n 2!y 3!Y 4!(cons x X) 5!Y 6!(cons y X)).
Reflexivity.
Exact h1.
Exact h.
Rewrite h2; Apply kahrs_var2.
Reflexivity.
Apply (kahrs_var_weak 1!n 2!n 3!Y 4!(cons x X) 5!Y 6!(cons y X)).
Reflexivity.
Exact h1.
Exact h1.
Apply kahrs_var3.
Exact h2.
Intro h3; Apply h0; Left; Exact h3.
Apply kahrs_refl.
(* abs *)
Simpl; Apply kahrs_abs.
Apply (IHM X (cons n Y)).
Intro h1; Elim h1; Intro h2.
Apply h0; Left; Exact h2.
Exact (h h2).
Intro h1; Apply h0; Right; Exact h1.
(* eos *)
Case (in_dec n Y); Intro h1.
Elim (in_split eq_dec h1); Intros Y1 h2; Elim h2; Clear h2; Intros
  Y2 h2; Elim h2; Clear h2; Intros h3 h4.
Rewrite h3.
Rewrite (rename_eos_not_in x y M (cons n Y2) h4).
Simpl.
Case (eq_dec n n); Intro h5.
Rewrite juxt_ass.
Rewrite juxt_ass.
Apply kahrs_eos3_gen.
Exact h4.
Exact h4.
Reflexivity.
Simpl.
Apply kahrs_eos2.
Apply IHM.
Intro h6; Apply h; Rewrite h3; Apply in_or_juxt; Right; Right; Exact h6.
Intro h6; Apply h0; Right; Exact h6.
Elim h5; Reflexivity.
Pattern 2 Y; Rewrite (juxt_nil_end Y);
Rewrite (rename_eos_not_in x y M Nil h1).
Simpl.
Case (eq_dec x n); Intro h2.
Apply kahrs_eos3_gen.
Exact h1.
Exact h.
Reflexivity.
Rewrite h2.
Apply kahrs_eos2.
Apply kahrs_refl.
Apply kahrs_eos3_gen.
Exact h1.
Exact h1.
Reflexivity.
Apply kahrs_eos3.
Intro h3; Apply h2; Symmetry; Exact h3.
Intro h3; Apply h0; Left; Exact h3.
Apply kahrs_refl.
Simpl in h0.
Simpl; Apply kahrs_ap.
Apply IHM1.
Exact h.
Intro h1; Apply h0; Apply in_or_juxt; Left; Exact h1.
Apply IHM2.
Exact h.
Intro h1; Apply h0; Apply in_or_juxt; Right; Exact h1.
Qed.

Lemma scb_rename2 : 
 (M:Adbmal;x,z:name;X1,X2:stack)
  ~(In z (names M))
   ->~(In z X1)
    ->(scb (juxt X1 (cons z X2))(rename M x z X1))
     ->(scb (juxt X1 (cons x X2)) M).
Proof.
NewInduction M; Intros x z X1 X2 d1 d2.
Intro h; Apply scb_var.
Simpl; Intro h; Apply scb_abs.
Assert h0 := (scb_abs_inv h).
Assert d1' : ~(In z (names M)).
Intro h1; Apply d1; Right; Exact h1.
Assert d2' : ~(In z (cons n X1)).
Intro h1; Elim h1; Intro h2.
Apply d1; Simpl; Left; Exact h2.
Exact (d2 h2).
Exact (IHM x z (cons n X1) X2 d1' d2' h0).
(*!*)Case (in_dec n X1); Intro h.
Elim (in_split eq_dec h); Intros Y1 h0; Elim h0; Clear h0; Intros Y2 h0;
 Elim h0; Clear h0; Intros h0 h1.
Rewrite h0.
Rewrite (rename_eos_not_in x z M (cons n Y2) h1).
Simpl.
Case (eq_dec n n); Intro h2; Simpl.
Rewrite juxt_ass.
Rewrite juxt_ass.
Simpl.
NewDestruct Y1; Simpl; Intro h3.
Apply scb_eos.
Elim (scb_eos_inv h3); Intros h4 h5.
Apply (IHM x z Y2 X2).
Intro h6; Apply d1; Right; Exact h6.
Simpl in h0; Rewrite h0 in d2.
Intro h6; Apply d2; Right; Exact h6.
Exact h5.
Elim (scb_eos_inv h3); Intros h4 h5.
Elim h1; Left; Symmetry; Exact h4.
Elim h2; Reflexivity.
Pattern 2 X1; Rewrite (juxt_nil_end X1).
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec x n); Intro h0.
NewDestruct X1; Simpl.
Intro h1.
Elim (scb_eos_inv h1); Intros h2 h3.
Rewrite h0; Apply scb_eos; Exact h3.
Intro h1; Elim (scb_eos_inv h1); Intros h2 h3.
Elim d2; Left; Symmetry; Exact h2.
NewDestruct X1; Simpl.
Intro h1.
Elim (scb_eos_inv h1); Intros h2 h3.
Elim d1; Left; Exact h2.
Intro h1; Elim (scb_eos_inv h1); Intros h2 h3.
Elim h; Left; Symmetry; Exact h2.
Exact h.
Simpl.
Intro h.
Elim (scb_ap_inv h); Intros h0 h1.
Apply scb_ap.
Apply (IHM1 x z).
Intro h2; Apply d1; Simpl; Apply in_or_juxt; Left; Exact h2.
Exact d2.
Exact h0.
Apply (IHM2 x z).
Intro h2; Apply d1; Simpl; Apply in_or_juxt; Right; Exact h2.
Exact d2.
Exact h1.
Qed.

(** [M[x:=z,XyY][y:=z',X] = M[y:=z',X][x:z,Xz'Y]] *)

Lemma rename_commutes :
 (x,y,z,z':name)
 ~z=y
  ->(M:Adbmal)
     ~(In z (names M))
      ->~(In z' (names M))
       ->(X,Y:stack)
          ~(In z' X)
            ->~(In z X)
             -> (rename (rename M x z (juxt X (cons y Y))) y z' X)
                 =(rename (rename M y z' X) x z (juxt X (cons z' Y))).
Proof.
Intros x y z z' h0 M h2 h3.
NewInduction M; Intros X Y H H5.
(* var *)
Simpl.
Case (in_dec n X); Intro h4; Simpl.
Case (in_dec n (juxt X (cons y Y))); Intro h5; Simpl.
Case (in_dec n X); Intro h6; Simpl.
Case (in_dec n (juxt X (cons z' Y))); Intro h7; Simpl.
Reflexivity.
Elim h7; Apply in_or_juxt; Left; Exact h6.
Elim h6; Exact h4.
Elim h5; Apply in_or_juxt; Left; Exact h4.
Case (in_dec n (juxt X (cons y Y))); Intro h5; Simpl.
Case (in_dec n X); Intro h6; Simpl.
Elim h4; Exact h6.
Elim (in_juxt_or h5); Intro h7.
Elim h6; Exact h7.
Case (eq_dec n y); Intro h8; Simpl.
Case (in_dec z' (juxt X (cons z' Y))); Intro h9; Simpl.
Reflexivity.
Elim h9; Apply in_or_juxt; Right; Left; Reflexivity.
Elim h7; Intro h9.
Elim h8; Symmetry; Exact h9.
Case (in_dec n (juxt X (cons z' Y))); Intro h10; Simpl.
Reflexivity.
Elim h10; Apply in_or_juxt; Right; Right; Exact h9.
Case (eq_dec n x); Intro h6; Simpl.
Case (in_dec z X); Intro h7; Simpl.
Case (eq_dec n y); Intro h8; Simpl.
Elim h5; Apply in_or_juxt; Right; Left; Symmetry; Exact h8.
Case (in_dec n (juxt X (cons z' Y))); Intro h9; Simpl.
Elim (in_juxt_or h9); Intro h10.
Elim h4; Exact h10.
Elim h10; Intro h11.
Elim h3; Left; Symmetry; Exact h11.
Elim h5; Apply in_or_juxt; Right; Right; Exact h11.
Case (eq_dec n x); Intro h10; Simpl.
Reflexivity.
Elim h10; Exact h6.
Case (eq_dec z y); Intro h8; Simpl.
Elim h0; Exact h8.
Case (eq_dec n y); Intro h9; Simpl.
Elim h5; Apply in_or_juxt; Right; Left; Symmetry; Exact h9.
Case (in_dec n (juxt X (cons z' Y))); Intro h10; Simpl.
Elim (in_juxt_or h10); Intro h11.
Elim h4; Exact h11.
Elim h11; Intro h12.
Elim h3; Left; Symmetry; Exact h12.
Elim h5; Apply in_or_juxt; Right; Right; Exact h12.
Case (eq_dec n x); Intro h11; Simpl.
Reflexivity.
Elim h11; Exact h6.
Case (in_dec n X); Intro h7; Simpl.
Elim h4; Exact h7.
Case (eq_dec n y); Intro h8; Simpl.
Case (in_dec z' (juxt X (cons z' Y))); Intro h9; Simpl.
Reflexivity.
Elim h9; Apply in_or_juxt; Right; Left; Reflexivity.
Case (in_dec n (juxt X (cons z' Y))); Intro h9; Simpl.
Reflexivity.
Case (eq_dec n x); Intro h10; Simpl.
Elim h6; Exact h10.
Reflexivity.
(* abs *)
Simpl.
Assert h4 : ~(In z (names M)).
Intro h4; Apply h2; Right; Exact h4.
Assert h5 : ~(In z' (names M)).
Intro h5; Apply h3; Right; Exact h5.
Apply (f_equal Adbmal).
Assert H0 : ~(In z' (cons n X)).
Intro H1; Elim H1; Intro H2.
Apply h3; Left; Exact H2.
Exact (H H2).
Assert H6 : ~(In z (cons n X)).
Intro H6; Elim H6; Intro H7.
Apply h2; Left; Exact H7.
Exact (H5 H7).
Exact (IHM h4 h5 (cons n X) Y H0 H6).
(* eos *) 
Assert h4 : ~(In z (names M)).
Intro h4; Apply h2; Right; Exact h4.
Assert h5 : ~(In z' (names M)).
Intro h5; Apply h3; Right; Exact h5.
Case (in_dec n X); Intro h6.
(* (In n X) *)
Elim (in_split eq_dec h6); Intros X1 h7; Elim h7; Clear h7; 
 Intros X2 h7; Elim h7; Clear h7; Intros h7 h8.
Assert H0 : ~(In z' X2).
Intro h9; Apply H; Rewrite h7; Apply in_or_juxt; Right; Right; Exact h9.
Assert H6 : ~(In z X2).
Intro h9; Apply H5; Rewrite h7; Apply in_or_juxt; Right; Right; Exact h9.
Rewrite h7.
Rewrite juxt_ass.
Rewrite juxt_ass.
Rewrite (rename_eos_not_in x z M (juxt (cons n X2) (cons y Y)) h8).
Rewrite (rename_eos_not_in y z' M (cons n X2) h8).
Simpl.
Case (eq_dec n n); Intro h9.
Rewrite rename_eos_not_in.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec n n); Intro h10.
Rewrite (IHM h4 h5 X2 Y H0 H6); Reflexivity.
Elim h10; Reflexivity.
Exact h8.
Exact h8.
Elim h9; Reflexivity.
(* ~(In n X) *)
Rewrite rename_eos_not_in.
Pattern 2 X; Rewrite (juxt_nil_end X); Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec n y); Intro h7.
Pattern 1 X; Rewrite (juxt_nil_end X).
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec y n); Intro h8.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec z' z'); Intro h9; Simpl.
Reflexivity.
Elim h9; Reflexivity.
Exact H.
Elim h8; Symmetry; Exact h7.
Exact h6.
Case (eq_dec x n); Intro h8; Simpl.
Case (eq_dec y n); Intro h9.
Elim h7; Symmetry; Exact h9.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec n z'); Intro h10.
Elim h3; Left; Exact h10.
Case (eq_dec x n); Intro h11; Simpl.
NewInduction Y.
Pattern X; Rewrite (juxt_nil_end X); Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec y z); Intro h12.
Elim h0; Symmetry; Exact h12.
Reflexivity.
Exact H5.
Case (eq_dec n a); Intro h12.
Pattern X; Rewrite (juxt_nil_end X); Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec y n); Intro h13.
Elim (h9 h13).
Reflexivity.
Exact h6.
Exact IHY.
Elim (h11 h8).
Exact h6.
Case (eq_dec y n); Intro h9.
Elim h7; Symmetry; Exact h9.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec n z'); Intro h10; Simpl.
Elim h3; Left; Exact h10.
Case (eq_dec x n); Intro h11; Simpl.
Elim (h8 h11).
NewInduction Y.
Pattern X; Rewrite (juxt_nil_end X); Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec y n); Intro h12; Simpl.
Elim (h9 h12).
Reflexivity.
Exact h6.
Case (eq_dec n a); Intro h12.
Pattern X; Rewrite (juxt_nil_end X); Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec y n); Intro h13.
Elim (h9 h13).
Reflexivity.
Exact h6.
Exact IHY.
Exact h6.
Exact h6.
Exact h6.
(* ap *)
Assert h4 : ~(In z (names M1))/\~(In z (names M2)).
Split; Intro h4; Apply h2; Simpl.
Apply in_or_juxt; Left; Exact h4.
Apply in_or_juxt; Right; Exact h4.
Elim h4; Clear h4; Intros h4 h5.
Assert h6 : ~(In z' (names M1))/\~(In z' (names M2)).
Split; Intro h6; Apply h3; Simpl.
Apply in_or_juxt; Left; Exact h6.
Apply in_or_juxt; Right; Exact h6.
Elim h6; Clear h6; Intros h6 h7.
Simpl.
Rewrite (IHM1 h4 h6 X Y H H5).
Rewrite (IHM2 h5 h7 X Y H H5).
Reflexivity.
Qed.

Lemma rename_trans : 
 (x,z,z':name;M:Adbmal;X:stack)
  ~(In z (names M))
   ->~(In z X)
    ->(rename (rename M x z X) z z' X)
       =(rename M x z' X).
Proof.
NewInduction M.
(* var *)
Simpl.
Intros X h h0.
Case (in_dec n X); Intro h1; Simpl.
Case (in_dec n X); Intro h2; Simpl.
Reflexivity.
Elim h2; Exact h1.
Case (eq_dec n x); Intro h2; Simpl.
Case (in_dec z X); Intro h3; Simpl.
Elim h0; Exact h3.
Case (eq_dec z z); Intro h4; Simpl.
Reflexivity.
Elim h4; Reflexivity.
Case (in_dec n X); Intro h3; Simpl.
Elim h1; Exact h3. (*Reflexivity.*)
Case (eq_dec n z); Intro h4; Simpl.
Elim h; Left; Exact h4.
Reflexivity.
(* abs *)
Simpl.
Intros X h h0.
Rewrite IHM.
Reflexivity.
Intro h1; Apply h; Right; Exact h1.
Intro h1; Elim h1; Intro h2.
Apply h; Left; Exact h2.
Exact (h0 h2).
(* eos *)
Intros X h h0.
Case (in_dec n X); Intro h1.
Elim (in_split eq_dec h1); Intros X1 h2; Elim h2; Clear h2; 
 Intros X2 h2; Elim h2; Clear h2; Intros h2 h3.
Rewrite h2.
Rewrite rename_eos_not_in.
Rewrite rename_eos_not_in.
Assert h4 : ~(In z X1).
Intro h4; Apply h0; Rewrite h2; Apply in_or_juxt; Left; Exact h4.
Simpl.
Case (eq_dec n n); Intro h5.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec n n); Intro h6.
Rewrite IHM.
Reflexivity.
Intro h7; Apply h; Right; Exact h7.
Intro h7; Apply h0; Rewrite h2; Apply in_or_juxt; Right; Right;
Exact h7.
Elim h6; Reflexivity.
Exact h3.
Elim h5; Reflexivity.
Exact h3.
Exact h3.
Pattern X; Rewrite (juxt_nil_end X).
Rewrite rename_eos_not_in.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec x n); Intro h2.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec z z); Intro h3.
Reflexivity.
Elim h3; Reflexivity.
Exact h0.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec z n); Intro h3.
Elim h; Left; Symmetry; Exact h3.
Reflexivity.
Exact h1.
Exact h1.
Exact h1.
(* ap *)
Intros X h h0.
Simpl.
Rewrite IHM1.
Rewrite IHM2.
Reflexivity.
Intro h1; Apply h; Simpl; Apply in_or_juxt; Right; Exact h1.
Exact h0.
Intro h1; Apply h; Simpl; Apply in_or_juxt; Left; Exact h1.
Exact h0.
Qed.

Inductive schroer' : Adbmal->Adbmal->stack->Prop :=
| schroer_rule : (M,N:Adbmal;x,y,z:name;Z:stack)
                    ~(In z (names M))
                     ->~(In z (names N))
                      ->~(In z Z)
                       ->(schroer' (rename M x z Nil)(rename N y z Nil) Z)
                        ->(schroer' (abs x M)(abs y N)(cons z Z))
| schroer_var  : (z:name;Z:stack)(schroer' (var z)(var z) Z)
| schroer_eos  : (M,N:Adbmal;x:name;Z:stack)
                    (schroer' M N Z)
                     ->(schroer' (eos x M)(eos x N) Z)
| schroer_ap   : (M,M',N,N':Adbmal;Z:stack)
                    (schroer' M M' Z)
                     ->(schroer' N N' Z)
                      ->(schroer' (ap M N)(ap M' N') Z).

Definition schroer := [M,N:Adbmal](EX Z:stack|(schroer' M N Z)).

(** We write [M=(Z)N] for [(schroer' M N Z)]. *)

(** [M=(Z)N => M[x:=z,Y]=(Z)N[x:=z,Y]] *)

Lemma scb_schroer : 
 (M,N:Adbmal;Z:stack)
  (schroer' M N Z)
   ->(X:stack)
      (scb X M)
       ->(scb X N).
Proof.
NewInduction 1; Intros X h.
Apply scb_abs.
Assert h0 := (scb_abs_inv h).
Assert h1 := (scb_rename z 4!Nil h0).
Simpl in h1.
Assert h2 := (IHschroer' (cons z X) h1).
Assert h3 : ~(In z Nil).
Exact [h]h.
Exact (scb_rename2 H0 h3 h2).
Exact h.
Elim (scb_eos_inv2 h); Intros X' h0.
Elim h0; Clear h0; Intros h0 h1.
Rewrite h0.
Apply scb_eos.
Apply IHschroer'.
Exact h1.
Elim (scb_ap_inv h); Intros h1 h2.
Apply scb_ap.
Apply IHschroer'1.
Exact h1.
Apply IHschroer'2; Exact h2.
Qed.

Lemma schroer_skel :
 (M,N:Adbmal; Z:stack)
  (schroer' M N Z)
   ->(skeleton M)=(skeleton N).
Proof.
NewInduction 1; Simpl.
Rewrite <- (rename_skel_eq x z M Nil) in IHschroer'.
Rewrite <- (rename_skel_eq y z N Nil) in IHschroer'.
Rewrite IHschroer'; Reflexivity.
Reflexivity.
Rewrite IHschroer'; Reflexivity.
Rewrite IHschroer'1; Rewrite IHschroer'2; Reflexivity.
Qed.

Lemma schroer'_rename_same : 
 (M,N:Adbmal;x,z:name;Z:stack)
  (schroer' M N Z)
   ->~(In z Z)
    ->~(In z (names M))
     ->~(In z (names N))
      ->(Y:stack)(schroer' (rename M x z Y)(rename N x z Y) Z).
Proof.
Intros M N x z Z h.
Elim h; Clear h M N Z.
(* abs *)
Simpl.
Intros M N y1 y2 z' Z h h0 h1 h2 ih h3 h4 h5 Y.
Assert h6 : ~z'=z.
Intro h6; Apply h3; Left; Exact h6.
Assert h7 : ~(In z Z).
Intro h7; Apply h3; Right; Exact h7.
Clear h3.
Assert h8 : (schroer' (rename (rename M x z (cons y1 Y)) y1 z' Nil)
              (rename (rename N x z (cons y2 Y)) y2 z' Nil) Z).
Replace (cons y1 Y) with (juxt Nil (cons y1 Y)).
Rewrite rename_commutes.
Replace (cons y2 Y) with (juxt Nil (cons y2 Y)).
Rewrite rename_commutes.
Apply ih.
Exact h7.
Apply not_in_renamed_term.
Exact h6.
Intro h8; Apply h4; Right; Exact h8.
Apply not_in_renamed_term.
Exact h6.
Intro h8; Apply h5; Right; Exact h8.
Intro h8; Apply h5; Left; Symmetry; Exact h8.
Intro h8; Apply h5; Right; Exact h8.
Exact h0.
Exact [f]f.
Exact [f]f.
Reflexivity.
Intro h8; Apply h4; Left; Symmetry; Exact h8.
Intro h8; Apply h4; Right; Exact h8.
Exact h.
Exact [f]f.
Exact [f]f.
Reflexivity.
Apply schroer_rule.
Apply not_in_renamed_term.
Intro h9; Apply h6; Symmetry; Exact h9.
Exact h.
Apply not_in_renamed_term.
Intro h9; Apply h6; Symmetry; Exact h9.
Exact h0.
Exact h1.
Exact h8.
(* var *)
Simpl.
Intros y Z h h0 h1 Y.
Case (in_dec y Y); Intro h2; Simpl.
Apply schroer_var.
Case (eq_dec y x); Intro; Apply schroer_var.
(* eos *)
Intros M N y Z h ih h0 h1 h2 Y.
Case (in_dec y Y); Intro h3.
Elim (in_split eq_dec h3); Intros Y1 h4; Elim h4; Clear h4; Intros
  Y2 h4; Elim h4; Clear h4; Intros h5 h6.
Rewrite h5.
Rewrite rename_eos_not_in.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec y y); Intro h7.
Apply schroer_eos.
Apply ih.
Exact h0.
Intro h8; Apply h1; Right; Exact h8.
Intro h8; Apply h2; Right; Exact h8.
Elim h7; Reflexivity.
Exact h6.
Exact h6.
Pattern Y; Rewrite (juxt_nil_end Y).
Rewrite rename_eos_not_in.
Rewrite rename_eos_not_in.
Simpl.
Case (eq_dec x y); Intro h4; Apply schroer_eos; Exact h.
Exact h3.
Exact h3.
(* ap *)
Simpl.
Intros M M' N N' Z aM ihM aN ihN h h0 h1 Y.
Apply schroer_ap.
Apply ihM.
Exact h.
Intro h2; Apply h0; Apply in_or_juxt; Left; Exact h2.
Intro h2; Apply h1; Apply in_or_juxt; Left; Exact h2.
Apply ihN.
Exact h.
Intro h2; Apply h0; Apply in_or_juxt; Right; Exact h2.
Intro h2; Apply h1; Apply in_or_juxt; Right; Exact h2.
Qed.

(** [M[x:=z,nil]=(Z)N[y:=z,nil] => M[x:=z',nil]=(Z)N[y:=z',nil]] *)

Lemma rename_diff_schroer' : 
 (M,N:Adbmal;Z:stack;x,y,z,z':name)
  ~(In z (names M))
   ->~(In z (names N))
    ->~(In z' (names M))
     ->~(In z' (names N))
      ->~(In z' Z)
       ->(schroer' (rename M x z Nil)(rename N y z Nil) Z)
        ->(schroer' (rename M x z' Nil)(rename N y z' Nil) Z).
Proof.
Intros M N Z x y z z'.
Case (eq_dec z' z); Intros h h0 h1 h2 h3 h4 h5.
Rewrite h; Exact h5.
Assert h6 : ~(In z' (names (rename M x z Nil))).
Apply not_in_renamed_term.
Intro h6; Apply h; Symmetry; Exact h6.
Exact h2.
Assert h7 : ~(In z' (names (rename N y z Nil))).
Apply not_in_renamed_term.
Intro h7; Apply h; Symmetry; Exact h7.
Exact h3.
Assert h8 := (schroer'_rename_same z h5 h4 h6 h7 Nil).
Rewrite rename_trans in h8.
Rewrite rename_trans in h8.
Exact h8.
Exact h1.
Exact [f]f.
Exact h0.
Exact [f]f.
Qed.

(** [M=(Z)N => \x.M=(wZ)\x.N] for some [w] *)

Lemma schroer'_abs : 
 (M,N:Adbmal;x:name;Z:stack)
  (schroer' M N Z)->(EX w:name|(schroer' (abs x M)(abs x N)(cons w Z))).
Proof.
Intros M N x Z h.
Elim (inf_many_names (juxt Z (juxt (names M) (names N))));
Intros w h1.
Exists w.
Assert h2 : ~(In w Z).
Intro h2; Apply h1; Apply in_or_juxt; Left; Exact h2.
Assert h3 : ~(In w (names M)).
Intro h3; Apply h1; Apply in_or_juxt; Right; Apply in_or_juxt;
 Left; Exact h3.
Assert h4 : ~(In w (names N)).
Intro h4; Apply h1; Apply in_or_juxt; Right; Apply in_or_juxt;
 Right; Exact h4.
Apply schroer_rule.
Exact h3.
Exact h4.
Exact h2.
Exact (schroer'_rename_same x h h2 h3 h4 Nil).
Qed.

Lemma le_Sn_m : (n,m:nat)(le (S n) m)->(EX m':nat|m=(S m')/\(le n m')).
Proof.
NewInduction n; NewDestruct m; Intro h.
Inversion h.
Exists n; Split.
Reflexivity.
Apply le_O_n.
Inversion h.
Exists n0; Split.
Reflexivity.
Apply le_S_n.
Exact h.
Qed.

(** [M=(Z1)N => M=(Z2)N] for [Z2] disjoint from [Z1], [|Z2|>=|Z1|],
   none of the [z] in [Z2] occur in [MN], and all elements of [Z2] distinct *)

Lemma schroer_change_Z :
 (M,N:Adbmal;Z1:stack)
  (schroer' M N Z1)
   ->(Z2:stack)
      (le (length Z1)(length Z2))
       ->(disjoint Z2 Z1)
        ->(disjoint Z2 (names M))
         ->(disjoint Z2 (names N))
          ->(all_distinct Z2)
           ->(schroer' M N Z2).
Proof.
NewInduction 1; Simpl.
Intros Z2 h3.
Elim (le_Sn_m h3); Intros n h4; Elim h4; Clear h4; Intros h4 h5.
Elim (length_S h4); Intros z' h6; Elim h6; Clear h6; Intros Z2' h6.
Rewrite h6.
Intros h7 h8 h9 h10.
Inversion_clear h10.
Assert h13 := (h7 z' (or_introl ?? (refl_equal name z'))).
Assert h14 : ~z=z'.
 Intro h14; Apply h13; Left; Exact h14.
Assert h15 : ~(In z' Z).
 Intro h15; Apply h13; Right; Exact h15.
Assert h16 : ~(In z' (names M)).
 Intro h16; Apply (h8 z' (or_introl ?? (refl_equal name z')));
 Right; Exact h16.
Assert h17 : ~(In z' (names N)).
 Intro h17; Apply (h9 z' (or_introl ?? (refl_equal name z')));
 Right; Exact h17.
Apply schroer_rule.
Exact h16.
Exact h17.
Exact H4.
Assert h18 : (schroer' (rename M x z (nil name)) (rename N y z (nil name)) Z2').
Apply IHschroer'.
Rewrite h6 in h3; Apply le_S_n; Exact h3.
Unfold disjoint; Intros a h18 h19;
 Apply (h7 a (or_intror ?? h18)); Right; Exact h19.
Unfold disjoint; Intros a h18; Apply not_in_renamed_term.
Intro h19; Apply (h7 a (or_intror ?? h18)); Left; Exact h19.
Intro h20; Apply (h8 a (or_intror ?? h18)); Right; Exact h20.
Unfold disjoint; Intros a h18; Apply not_in_renamed_term.
Intro h19; Apply (h7 a (or_intror ?? h18)); Left; Exact h19.
Intro h20; Apply (h9 a (or_intror ?? h18)); Right; Exact h20.
Exact H3.
Exact (rename_diff_schroer' H H0 h16 h17 H4 h18).
(* var *)
Intros; Apply schroer_var.
(* eos *)
Intros Z2 h0 h1 h2 h3 h4.
Apply schroer_eos.
Apply IHschroer'.
Exact h0.
Exact h1.
Unfold disjoint; Intros z h5 h6; Apply (h2 z h5); Right; Exact h6.
Unfold disjoint; Intros z h5 h6; Apply (h3 z h5); Right; Exact h6.
Exact h4.
(* ap *)
Intros Z2 h2 h3 h4 h5 h6.
Apply schroer_ap.
Apply IHschroer'1.
Exact h2.
Exact h3.
Unfold disjoint; Intros z h7 h8; Apply (h4 z h7); 
 Apply in_or_juxt; Left; Exact h8.
Unfold disjoint; Intros z h7 h8; Apply (h5 z h7); 
 Apply in_or_juxt; Left; Exact h8.
Exact h6.
Apply IHschroer'2.
Exact h2.
Exact h3.
Unfold disjoint; Intros z h7 h8; Apply (h4 z h7); 
 Apply in_or_juxt; Right; Exact h8.
Unfold disjoint; Intros z h7 h8; Apply (h5 z h7); 
 Apply in_or_juxt; Right; Exact h8.
Exact h6.
Qed.

Lemma fresh_list : 
 (n:nat;l:stack)
  {m:stack|(length m)=n/\(disjoint m l)/\(all_distinct m)}.
Proof.
Unfold disjoint; NewInduction n; Simpl; Intro l.
Exists (nil name); Split.
Reflexivity.
Split.
Intros a h; Elim h.
Apply all_distinct_nil.
Elim (IHn l); Intros m h; Elim h; Intros h0 h1; Elim h1; Clear h1; Intros h1 h2.
Elim (inf_many_names (juxt l m)); Intros a h3.
Assert h4 : ~(In a l).
Intro h4; Apply h3; Apply in_or_juxt; Left; Exact h4.
Assert h5 : ~(In a m).
Intro h5; Apply h3; Apply in_or_juxt; Right; Exact h5.
Exists (cons a m); Split.
Simpl; Rewrite h0; Reflexivity.
Split.
Intros b h6 h7.
Elim h6; Intro h8.
Apply h4; Rewrite h8; Exact h7.
Exact (h1 b h8 h7).
Apply all_distinct_cons.
Exact h2.
Exact h5.
Qed.

Lemma schroer_ap_Z1Z2 : 
 (M1,M2,N1,N2:Adbmal;Z1,Z2:stack)
  (schroer' M1 N1 Z1)
   ->(schroer' M2 N2 Z2)
    ->(EX Z:stack | (schroer' (ap M1 M2) (ap N1 N2) Z)).
Proof.
Intros M1 M2 N1 N2 Z1 Z2 h h0.
Elim (fresh_list (max (length Z1)(length Z2))
      (juxt (juxt Z1 Z2) 
       (juxt (juxt (names M1) (names M2))
         (juxt (names N1) (names N2)))));
 Intros Z3 h3; Elim h3; Clear h3; Intros h3 h4; Elim h4; Clear h4;
 Intros h4 h5.
Exists Z3.
Elim (disjoint_juxt_and h4); Clear h4; Intros h6 h7.
Elim (disjoint_juxt_and h6); Clear h6; Intros h8 h9.
Elim (disjoint_juxt_and h7); Clear h7; Intros h10 h11.
Elim (disjoint_juxt_and h10); Clear h10; Intros h4 h6.
Elim (disjoint_juxt_and h11); Clear h11; Intros h7 h10.
Elim (max_dec (length Z1) (length Z2)); Intro h12; Rewrite h12 in h3.
(* (max (length Z1) (length Z2))=(length Z1) *)
Assert h13 : (le (length Z1) (length Z3)).
 Rewrite h3; Apply le_n.
Assert h14 : (le (length Z2) (length Z3)).
 Rewrite h3; Rewrite <- h12; Apply le_max_r.
Apply schroer_ap.
Apply (schroer_change_Z h h13).
Exact h8.
Exact h4.
Exact h7.
Exact h5.
Apply (schroer_change_Z h0 h14).
Exact h9.
Exact h6.
Exact h10.
Exact h5.
(* (max (length Z1) (length Z2))=(length Z2) *)
Assert h13 : (le (length Z1) (length Z3)).
 Rewrite h3; Rewrite <- h12; Apply le_max_l.
Assert h14 : (le (length Z2) (length Z3)).
 Rewrite h3; Apply le_n.
Apply schroer_ap.
Apply (schroer_change_Z h h13).
Exact h8.
Exact h4.
Exact h7.
Exact h5.
Apply (schroer_change_Z h0 h14).
Exact h9.
Exact h6.
Exact h10.
Exact h5.
Qed.

Lemma schroer'_refl : (M:Adbmal)(EX Z:stack|(schroer' M M Z)).
Proof.
NewInduction M.
(* var *)
Exists (nil name); Apply schroer_var.
(* abs *)
Elim IHM; Intros Z h.
Elim (schroer'_abs n h); Intros w h0.
Exists (cons w Z); Exact h0.
(* eos *)
Elim IHM; Intros Z h.
Exists Z; Apply schroer_eos; Exact h.
(* ap *)
Elim IHM1; Intros Z1 h1.
Elim IHM2; Intros Z2 h2.
Exact (schroer_ap_Z1Z2 h1 h2).
Qed.

Lemma schroer_refl : (M:Adbmal)(schroer M M).
Proof [M](schroer'_refl M).

Lemma schroer'_symm : 
 (M,N:Adbmal;Z:stack)(schroer' M N Z)->(schroer' N M Z).
Proof.
NewInduction 1.
Apply schroer_rule; Assumption.
Apply schroer_var.
Apply schroer_eos; Assumption.
Apply schroer_ap; Assumption.
Qed.

Lemma schroer_symm : (M,N:Adbmal)(schroer M N)->(schroer N M).
Proof.
Intros M N h; Elim h; Intros Z h0.
Exists Z.
Exact (schroer'_symm h0).
Qed.

Lemma schroer'_tranzzz : 
 (M,N:Adbmal;Z:stack)
  (schroer' M N Z)
   ->(P:Adbmal)
      (schroer' N P Z)
       ->(schroer' M P Z).
Proof.
NewInduction 1; Simpl; Intros P h; Inversion_clear h.
Apply schroer_rule.
Exact H.
Exact H4.
Exact H1.
Apply IHschroer'; Exact H6.
Apply schroer_var.
Apply schroer_eos.
Apply IHschroer'.
Exact H0.
Apply schroer_ap.
Apply IHschroer'1.
Exact H0.
Apply IHschroer'2.
Exact H2.
Qed.

Lemma schroer'_trans : 
 (M,N:Adbmal;Z1:stack)
  (schroer' M N Z1)
   ->(P:Adbmal;Z2:stack)
      (schroer' N P Z2)
       ->(EX Z3:stack|(schroer' M P Z3)).
Proof.
Intros M N Z1 h P Z2 h0.
Elim (fresh_list (max (length Z1)(length Z2))
       (juxt (juxt Z1 Z2) 
             (juxt (names M)(juxt (names N)(names P)))));
 Intros Z3 h3; Elim h3; Clear h3; Intros h3 h4; Elim h4; Clear h4;
 Intros h4 h5.
Exists Z3.
Elim (disjoint_juxt_and h4); Clear h4; Intros h6 h7.
Elim (disjoint_juxt_and h6); Clear h6; Intros h8 h9.
Elim (disjoint_juxt_and h7); Clear h7; Intros h10 h11.
Elim (disjoint_juxt_and h11); Clear h11; Intros h11 h12.
Elim (max_dec (length Z1) (length Z2)); Intro h13; Rewrite h13 in h3.
(* (max (length Z1) (length Z2))=(length Z1) *)
Assert h14 : (le (length Z1) (length Z3)).
 Rewrite h3; Apply le_n.
Assert h15 : (le (length Z2) (length Z3)).
 Rewrite h3; Rewrite <- h13; Apply le_max_r.
Exact (schroer'_tranzzz 
       (schroer_change_Z h h14 h8 h10 h11 h5) 
        (schroer_change_Z h0 h15 h9 h11 h12 h5)).
(* (max (length Z1) (length Z2))=(length Z2) *)
Assert h14 : (le (length Z1) (length Z3)).
 Rewrite h3; Rewrite <- h13; Apply le_max_l.
Assert h15 : (le (length Z2) (length Z3)).
 Rewrite h3; Apply le_n.
Exact (schroer'_tranzzz 
       (schroer_change_Z h h14 h8 h10 h11 h5) 
        (schroer_change_Z h0 h15 h9 h11 h12 h5)).
Qed.

Lemma schroer_trans : 
 (M,N:Adbmal)
  (schroer M N)
   ->(P:Adbmal)
      (schroer N P)
       ->(schroer M P).
Proof.
Intros M N h; Elim h; Intros Z1 h0 P h1; Elim h1; Intros Z2 h2.
Exact (schroer'_trans h0 h2).
Qed.

Lemma schroer'_abs_congr : 
 (M,N:Adbmal;Z:stack;x:name)
  (schroer' M N Z)
   ->(EX z:name|(schroer' (abs x M)(abs x N)(cons z Z))).
Proof.
Intros M N Z x h.
Elim (inf_many_names (juxt Z (juxt (names M) (names N))));
 Intros z h0.
Exists z.
Assert h1 : ~(In z Z).
Intro h1; Apply h0; Apply in_or_juxt; Left; Exact h1.
Assert h2 : ~(In z (names M)).
Intro h2; Apply h0; Apply in_or_juxt; Right; Apply in_or_juxt; Left;
 Exact h2.
Assert h3 : ~(In z (names N)).
Intro h3; Apply h0; Apply in_or_juxt; Right; Apply in_or_juxt; Right;
 Exact h3.
Apply schroer_rule.
Exact h2.
Exact h3.
Exact h1.
Apply schroer'_rename_same.
Exact h.
Exact h1.
Exact h2.
Exact h3.
Qed.

Lemma schroer_abs_congr : 
 (M,N:Adbmal;x:name)
  (schroer M N)
   ->(schroer (abs x M)(abs x N)).
Proof.
Intros M N x h; Elim h; Intros Z h0.     
Elim (schroer'_abs_congr x h0); Intros z h1.
Exists (cons z Z); Exact h1.
Qed.

Lemma schroer_eos_congr : 
 (M,N:Adbmal;x:name)
  (schroer M N)
   ->(schroer (eos x M) (eos x N)).
Proof.
Intros M N x h; Elim h; Intros Z h0.     
Exists Z; Apply schroer_eos; Exact h0.
Qed.

Lemma schroer'_apl_congr : 
 (M,M',N:Adbmal;Z:stack)
  (schroer' M M' Z)
   ->(EX Z':stack|(schroer' (ap M N)(ap M' N) Z')).
Proof.
Intros M M' N Z1 h.
Elim (schroer'_refl N); Intros Z2 h0.
Exact (schroer_ap_Z1Z2 h h0).
Qed.

Lemma schroer_apl_congr : 
 (M,M',N:Adbmal)(schroer M M')->(schroer (ap M N)(ap M' N)).
Proof.
Intros M M' N h; Elim h; Intros Z h0.
Exact (schroer'_apl_congr N h0).
Qed.

Lemma schroer'_apr_congr : 
 (M,N,N':Adbmal;Z:stack)
  (schroer' N N' Z)
   ->(EX Z':stack|(schroer' (ap M N)(ap M N') Z')).
Intros M N N' Z2 h.
Elim (schroer'_refl M); Intros Z1 h0.
Exact (schroer_ap_Z1Z2 h0 h).
Qed.

Lemma schroer_apr_congr : 
 (M,N,N':Adbmal)(schroer N N')->(schroer (ap M N)(ap M N')).
Proof.
Intros M M' N h; Elim h; Intros Z h0.
Exact (schroer'_apr_congr M h0).
Qed.

Lemma alpha_conv_to_schroer :
 (M,N:Adbmal)(alpha_conv M N)->(schroer M N).
Proof.
NewInduction 1.
(* alpha_conv_rule *)
Elim (schroer'_refl M); Intros Z H0.
Elim (inf_many_names (cons y (juxt Z (names M)))); Intros z H1.
Exists (cons z Z).
Assert H2 : ~z=y.
Intro H2; Apply H1; Left; Symmetry; Exact H2.
Assert H3 : ~(In z Z).
Intro H3; Apply H1; Right; Apply in_or_juxt; Left; Exact H3.
Assert H4 : ~(In z (names M)).
Intro H4; Apply H1; Right; Apply in_or_juxt; Right; Exact H4.
Apply schroer_rule.
Exact H4.
Apply not_in_renamed_term.
Intro H5; Apply H2; Symmetry; Exact H5.
Exact H4.
Exact H3.
Rewrite rename_trans.
Apply schroer'_rename_same.
Exact H0.
Exact H3.
Exact H4.
Exact H4.
Exact H.
Exact [f]f.
(* alpha_conv_abs *)
Exact (schroer_abs_congr x IHalpha_conv).
(* alpha_conv_eos *)
Exact (schroer_eos_congr x IHalpha_conv).
(* alpha_conv_apl *)
Exact (schroer_apl_congr N IHalpha_conv).
(* alpha_conv_apr *)
Exact (schroer_apr_congr N IHalpha_conv).
Qed.

Lemma church_to_schroer :
 (M,N:Adbmal)(church M N)->(schroer M N).
Proof.
NewInduction 1.
Exact (alpha_conv_to_schroer H).
Apply schroer_refl.
Apply schroer_symm; Exact IHRhat.
Exact (schroer_trans IHRhat1 IHRhat2).
Qed.

Lemma schroer'_to_church :
 (M,N:Adbmal;Z:stack)(schroer' M N Z)->(church M N).
Proof.
NewInduction 1.
(* schroer_rule *)
Assert H3 := (Rhat_ext 3!(abs x M) (alpha_conv_rule x H)). 
 (* why can't position 3 be inferred? *)
Assert H4 := (Rhat_symm (Rhat_ext 3!(abs y N)(alpha_conv_rule y H0))).
Assert H5 := (church_cxt_congr (cxt_abs z) IHschroer').
Exact (Rhat_trans H3 (Rhat_trans H5 H4)).
(* schroer_var *)
Unfold church; Apply Rhat_refl. (* why is unfolding necessary? *)
(* schroer_eos *)
Apply (church_cxt_congr (cxt_eos x)); Exact IHschroer'.
(* schroer_ap *)
Assert H2 := (church_cxt_congr (cxt_apl N) IHschroer'1).
Assert H3 := (church_cxt_congr (cxt_apr M') IHschroer'2).
Exact (Rhat_trans H2 H3).
Qed.

Lemma schroer_to_church :
 (M,N:Adbmal)(schroer M N)->(church M N).
Proof.
Intros M N h; Elim h; Intros Z h0.
Exact (schroer'_to_church h0).
Qed.

Lemma same_schroer_church : (same_rel schroer church).
Proof
 (conj (incl_rel schroer church) 
       (incl_rel church schroer)
       ([M,N;H](schroer_to_church H))
       ([M,N;H](church_to_schroer H))
 ).

Lemma same_schroer_kahrs : (same_rel schroer kahrs).
Proof
(conj ??
 ([x,y;h](proj2 ?? same_kahrs_church x y
          (proj1 ?? same_schroer_church x y h)))
 ([x,y;h](proj2 ?? same_schroer_church x y
          (proj1 ?? same_kahrs_church x y h)))).

Lemma rename_bwr1 :
 (M,N:Adbmal;x,y,z:name;X1,X2,Z,Z':stack)
  (scb (juxt Z (cons x Z')) M)
   ->~(In z X1)
    ->~(In z (names M))
     ->(rename M x z Z)=(eoss X1 (eos z (eoss X2 (abs y N))))
      -> Z = X1 /\ M = (eoss (juxt Z (cons x X2))(abs y N)).
Proof.
NewInduction M; Intros N x y z X1 X2 Z Z' h h0 h1.
(* var n *)
Simpl; Case (in_dec n Z); Intro h2.
NewDestruct X1; Intro h3; Discriminate h3.
Case (eq_dec n x); Intro h3; NewDestruct X1; Intro h4; Discriminate h4.
(* abs n M *)
NewDestruct X1; Intro h2; Discriminate h2.
(* eos n M *)
NewDestruct Z; Simpl.
Simpl in h; Elim (scb_eos_inv h); Intros h2 h3.
Case (eq_dec x n); Intro h4; Simpl.
NewDestruct X1; Simpl.
Intro h5; Injection h5; Intro h6.
Split.
Reflexivity.
Rewrite h4; Rewrite h6; Reflexivity.
Intro h5; Injection h5; Intros h6 h7.
Elim h0; Left; Symmetry; Exact h7.
Elim h4; Symmetry; Exact h2.
Simpl in h; Elim (scb_eos_inv h); Intros h2 h3.
Case (eq_dec n n0); Intro h4; Simpl.
NewDestruct X1; Simpl.
Intro h5; Injection h5; Intros h6 h7.
Elim h1; Left; Exact h7.
Intro h5; Injection h5; Intros h6 h7.
Assert h8 : ~(In z l0).
Intro h8; Apply h0; Right; Exact h8.
Assert h9 : ~(In z (names M)).
Intro h9; Apply h1; Right; Exact h9.
Elim (IHM N x y z l0 X2 l Z' h3 h8 h9 h6); Intros h10 h11.
Split.
Rewrite <- h4; Rewrite <- h7; Rewrite h10; Reflexivity.
Rewrite h4; Rewrite h11; Reflexivity.
Elim (h4 h2).
(* ap M N *)
Simpl; NewDestruct X1; Simpl; Intro h2; Discriminate h2.
Qed.

Lemma rename_bwr2 : 
 (M,N:Adbmal;x,y,z:name;X,Z,Z':stack)
  (scb (juxt Z (cons x Z')) M)
   ->~(In z X)
    ->~(In z (names M))
     ->(rename M x z Z)=(eoss X (abs y N))
      ->(EX X':stack|
         Z=(juxt X X')
          /\ (EX M':Adbmal| M=(eoss X (abs y M')) 
                          /\ N = (rename M' x z (cons y X')))).
Proof.
NewInduction M; Intros N x y z X Z Z' h h0 h1.
Simpl; Case (in_dec n Z); Intro h2; Simpl.
NewDestruct X; Intro h3; Discriminate h3.
Case (eq_dec n x); Intro h3; Simpl; NewDestruct X; Simpl; 
 Intro h4; Discriminate h4.
NewDestruct X; Simpl.
Intro h2; Injection h2; Intros h3 h4.
Exists Z; Split.
Reflexivity.
Exists M; Split.
Rewrite h4; Reflexivity.
Symmetry; Rewrite <- h4; Exact h3.
Intro h2; Discriminate h2.
(* eos n M *)
NewDestruct Z; Simpl.
Simpl in h.
Elim (scb_eos_inv2 h); Intros Z0 h2; Elim h2; Clear h2; Intros h2 h3.
Injection h2; Intros h4 h5.
Case (eq_dec x n); Intro h6; Simpl.
NewDestruct X; Simpl.
Intro h7; Discriminate h7.
Intro h7; Injection h7; Intros h8 h9.
Elim h0; Left; Symmetry; Exact h9.
Elim (h6 h5).
Simpl in h.
Elim (scb_eos_inv h); Intros h2 h3.
Case (eq_dec n n0); Intro h4; Simpl.
NewDestruct X; Simpl.
Intro h5; Discriminate h5.
Intro h5; Injection h5; Intros h6 h7.
Elim (IHM N x y z l0 l Z').
Intros X' h8; Elim h8; Clear h8; Intros h8 h9.
Elim h9; Intros M' h10; Elim h10; Clear h10; Intros h10 h11.
Exists X'; Split.
Rewrite <- h4; Rewrite <- h7; Rewrite h8; Reflexivity.
Exists M'; Split.
Rewrite h10.
Rewrite <- h7.
Reflexivity.
Exact h11.
Exact h3.
Intro h8; Apply h0; Right; Exact h8.
Intro h8; Apply h1; Right; Exact h8.
Exact h6.
Elim h4; Exact h2.
NewDestruct X; Simpl; Intro h2; Discriminate h2.
Qed.

Lemma rename_bwr3 : 
 (M,P:Adbmal;x,z:name;Z,Z':stack)
  (scb (juxt Z (cons x Z')) M)
   ->~(In z (names M))
    ->(adbmal_beta (rename M x z Z) P)
     ->(EX N:Adbmal | (adbmal_beta M N) /\ P = (rename N x z Z)).
Proof.
NewInduction M; Intros P x z Z Z' d1 d2; Simpl.
(* var *)
Case (in_dec n Z); Intro h; Simpl.
Intro h0; Inversion h0.
Case (eq_dec n x); Intro h0; Simpl; Intro h1; Inversion h1.
(* abs *)
Intro h; Inversion_clear h.
Assert d1' := (scb_abs_inv d1).
Assert d2' : ~(In z (names M)).
Intro h; Apply d2; Right; Exact h.
Elim (IHM N x z (cons n Z) Z' d1' d2' H); Intros N' h; Elim h; Clear h; 
 Intros h h0.
Exists (abs n N'); Split.
Apply beta_abs; Exact h.
Simpl; Rewrite h0; Reflexivity.
(* eos *)
Case (eq_dec x n); Intro h; Simpl.
NewDestruct Z.
Intro h0; Inversion_clear h0.
Exists (eos n N); Split.
Apply beta_eos; Assumption.
Simpl; Case (eq_dec x n); Intro h0.
Reflexivity.
Elim (h0 h).
Simpl in d1.
Assert h0 := (scb_eos_inv d1).
Elim h0; Clear h0; Intros h0 d1'.
Assert d2' : ~(In z (names M)).
Intro h1; Apply d2; Right; Exact h1.
Case (eq_dec n n0); Intro h1; Simpl.
Intro h2; Inversion_clear h2.
Elim (IHM N x z l Z' d1' d2' H); Intros N' h2; Elim h2; Clear h2; Intros h2 h3.
Exists (eos n N'); Split.
Apply beta_eos; Assumption.
Rewrite h3; Simpl.
Case (eq_dec n n0); Intro h4; Simpl.
Reflexivity.
Elim h4; Exact h1.
Elim h1; Exact h0.
NewDestruct Z.
Intro h0; Inversion_clear h0.
Exists (eos n N); Split.
Apply beta_eos; Assumption.
Simpl; Case (eq_dec x n); Intro h0; Simpl.
Elim (h h0).
Reflexivity.
Assert h0 := (scb_eos_inv d1).
Elim h0; Clear h0; Intros h0 d1'.
Assert d2' : ~(In z (names M)).
Intro h1; Apply d2; Right; Exact h1.
Case (eq_dec n n0); Intro h1; Simpl.
Intro h2; Inversion_clear h2.
Elim (IHM N x z l Z' d1' d2' H); Intros N' h2; Elim h2; Clear h2; Intros h2 h3.
Exists (eos n N'); Split.
Apply beta_eos; Assumption.
Rewrite h3; Simpl.
Case (eq_dec n n0); Intro h4; Simpl.
Reflexivity.
Elim h4; Exact h1.
Elim h1; Exact h0.
(* ap *)
Intro h; Inversion h.
Assert h0 := (scb_ap_inv d1).
Elim h0; Clear h0; Intros d1a d1b.
Assert h0 : ~(In z (names M1))/\~(In z (names M2)).
Split; Intro h0; Apply d2; Simpl.
Apply in_or_juxt; Left; Exact h0.
Apply in_or_juxt; Right; Exact h0.
Elim h0; Clear h0; Intros d2a d2b.
Elim (IHM1 M' x z Z Z' d1a d2a H2); Intros N1 h0; Elim h0; Clear h0; 
 Intros h0 h1.
Exists (ap N1 M2); Split.
Apply beta_apl; Assumption.
Rewrite h1; Reflexivity.
Assert h0 := (scb_ap_inv d1).
Elim h0; Clear h0; Intros d1a d1b.
Assert h0 : ~(In z (names M1))/\~(In z (names M2)).
Split; Intro h0; Apply d2; Simpl.
Apply in_or_juxt; Left; Exact h0.
Apply in_or_juxt; Right; Exact h0.
Elim h0; Clear h0; Intros d2a d2b.
Elim (IHM2 M' x z Z Z' d1b d2b H2); Intros N2 h0; Elim h0; Clear h0; 
 Intros h0 h1.
Exists (ap M1 N2); Split.
Apply beta_apr; Assumption.
Rewrite h1; Reflexivity.
(* adbmal_beta rule *)
Clear H1 N.
Assert h0 := (scb_ap_inv d1).
Elim h0; Clear h0; Intros d1a d1b.
Assert h0 : ~(In z (names M1))/\~(In z (names M2)).
Split; Intro h0; Apply d2;Simpl.
Apply in_or_juxt; Left; Exact h0.
Apply in_or_juxt; Right; Exact h0.
Elim h0; Clear h0; Intros d2a d2b.
(*!*) Case (in_dec z X); Intro h0.
(* In z X *)
Elim (in_split eq_dec h0); Intros X1 h1; Elim h1; Clear h1; Intros X2 h1;
Elim h1; Clear h1; Intros h1 h2.
Assert h3 : (rename M1 x z Z)=(eoss X1 (eos z (eoss X2 (abs x0 M)))).
Rewrite h1 in H0.
Rewrite eoss_juxt in H0.
Symmetry; Exact H0.
Elim (rename_bwr1 d1a h2 d2a h3); Intros h4 h5.
Exists (adbmal_subst (juxt Z (cons x X2)) Nil M x0 M2); Split.
Rewrite h5.
Apply beta_rule.
Symmetry.
Rewrite h1.
Rewrite h4.
Rewrite h5 in d1a.
Rewrite eoss_juxt in d1a.
Assert h6 := (scb_eoss_inv2 d1a).
Simpl in h6.
Elim (scb_eos_inv h6); Intros h7 h8.
Elim (scb_eoss_inv h8); Intros Z0 h9.
Elim h9; Clear h9 h7; Intros h7 h9.
Assert h10 := (scb_abs_inv h9).
Rewrite <- h7 in d1b; Rewrite h4 in d1b.
Exact (rename_subst_commute_closed 3!Nil 4!X1 5!X2 6!Z0 z h10 d1b).
(* ~In z X *)
Assert h1 : (rename M1 x z Z)=(eoss X (abs x0 M)).
Symmetry; Assumption.
Elim (rename_bwr2 d1a h0 d2a h1); Intros X' h2; Elim h2; Clear h2; 
 Intros h2 h3; Elim h3; Clear h3; Intros M' h3; Elim h3; Clear h3; 
 Intros h3 h4.
Exists (adbmal_subst X Nil M' x0 M2); Split.
Rewrite h3; Apply beta_rule.
Rewrite h4.
Rewrite h2.
Assert h5 : ~(In z (names M')).
Intro h5; Apply d2a; Rewrite h3.
Apply in_eoss2.
Right.
Exact h5.
Assert h6 : ~z=x0.
Intro h6; Apply d2a; Rewrite h3.
Apply in_eoss2.
Left; Symmetry; Exact h6.
Assert h7 : ~(In z Nil).
Exact [h]h.
Rewrite h3 in d1a.
Rewrite h2 in d1a.
Rewrite juxt_ass in d1a.
Assert h8 := (scb_eoss_inv2 d1a).
Assert h9 := (scb_abs_inv h8).
Rewrite h2 in d1b.
Rewrite juxt_ass in d1b.
Symmetry.
Exact (rename_subst_commute_open h5 h7 h6 h9 d1b).
Qed.

Lemma rename_beta :
 (M,N:Adbmal;x,z:name)
  ~(In z (names M))
  ->(adbmal_beta M N)
   ->(X,Z:stack)
      (scb (juxt Z (cons x X)) M)
       ->(adbmal_beta (rename M x z Z)(rename N x z Z)).
Proof.
NewInduction M; Intros N x z d h0 X Z h; Inversion h0; Simpl.
Apply beta_abs.
Assert h1 := (scb_abs_inv h).
Assert h2 : ~(In z (names M)).
Intro h2; Apply d; Right; Exact h2.
Exact (IHM N0 x z h2 H2 X (cons n Z) h1).
Case (eq_dec x n); Intro h1; Simpl.
NewDestruct Z; Simpl.
Apply beta_eos; Assumption.
Simpl in h.
Elim (scb_eos_inv h); Intros h2 h3.
Case (eq_dec n n0); Intro h4; Simpl.
Apply beta_eos.
Assert h5 : ~(In z (names M)).
Intro h5; Apply d; Right; Exact h5.
Exact (IHM N0 x z h5 H2 X l h3).
Elim (h4 h2).
NewDestruct Z; Simpl.
Apply beta_eos; Assumption.
Simpl in h.
Elim (scb_eos_inv h); Intros h2 h3.
Case (eq_dec n n0); Intro h4; Simpl.
Apply beta_eos.
Assert h5 : ~(In z (names M)).
Intro h5; Apply d; Right; Exact h5.
Exact (IHM N0 x z h5 H2 X l h3).
Elim (h4 h2).
Elim (scb_ap_inv h); Intros h1 h2.
Assert h3 : ~(In z (names M1)).
Intro h3; Apply d; Simpl; Apply in_or_juxt; Left; Exact h3.
Apply beta_apl.
Exact (IHM1 M' x z h3 H2 X Z h1).
Elim (scb_ap_inv h); Intros h1 h2.
Assert h4 : ~(In z (names M2)).
Intro h4; Apply d; Simpl; Apply in_or_juxt; Right; Exact h4.
Apply beta_apr.
Exact (IHM2 M' x z h4 H2 X Z h2).
Elim (scb_ap_inv h); Intros h1 h2.
Rewrite <- H0 in h1.
Elim (scb_eoss_inv h1); Intros Z' h3; Elim h3; Clear h3; Intros h3 h4.
(*!*) Elim (le_or_gt_list h3); Intro h6.
(* (le_list X Z) *)
Elim h6; Intros Y h7.
Rewrite h7.
Rewrite rename_eoss.
Simpl.
Assert h8 : ~(In z (names M1)).
Intro h8; Apply d; Simpl; Apply in_or_juxt; Left; Exact h8.
Rewrite <- H0 in h8.
Assert h9 : ~(In z (names M)).
Intro h9; Apply h8; Apply in_eoss2; Right; Exact h9.
Assert h10 : ~z=x0.
Intro h10; Apply h8; Apply in_eoss2; Left; Symmetry; Exact h10.
Assert h11 := (scb_abs_inv h4).
Assert h12 : ~(In z Nil).
Exact [h]h.
Rewrite h7 in h2.
Rewrite h7 in h3; Rewrite juxt_ass in h3.
Assert h13 := (juxt_inj h3).
Rewrite h13 in h11.
Rewrite juxt_ass in h2.
Assert rsc := (rename_subst_commute_open h9 h12 h10 h11 h2).
Simpl in rsc.
(* at last ... *) Rewrite rsc.
Apply beta_rule.
(* (gt_list X0 Z) *)
Elim h6; Intros y h7; Elim h7.
Clear h7 H0 H1 N0 H2 h0 N h4 h3 Z' h6 h.
Intros Y h3.
Rewrite h3 in h1; Rewrite eoss_juxt in h1.
Elim (scb_eoss_inv h1); Intros W h4; Elim h4; Clear h4; Intros h4 h5.
Rewrite (juxt_inj h4) in h5; Clear h4.
Simpl in h5; Elim (scb_eos_inv h5); Clear h5; Intros h4 h5.
Elim (scb_eoss_inv h5); Intros Y' h6; Elim h6; Clear h6; Intros h6 h7.
Assert h8 := (scb_abs_inv h7).
Rewrite h3.
Rewrite h4.
Pattern 2 Z; Rewrite (juxt_nil_end Z).
Rewrite eoss_juxt.
Rewrite rename_eoss; Simpl.
Case (eq_dec x x); Intro h9; Simpl.
Rewrite (rename_subst_commute_closed 1!M 2!M2 3!Nil 4!Z 5!Y 6!Y').
Replace (eoss Z (eos z (eoss Y (abs x0 M))))
 with (eoss (juxt Z (cons z Y)) (abs x0 M)).
Apply beta_rule.
Rewrite eoss_juxt; Reflexivity.
Exact h8.
Rewrite h6; Exact h2.
Elim h9; Reflexivity.
Qed.

Lemma schroer_eoss_inv1 : 
 (X,Z:stack;M,N:Adbmal)
  (schroer' (eoss X M) N Z)
   ->(EX N':Adbmal|N=(eoss X N')/\(schroer' M N' Z)).
Proof.
NewInduction X; Simpl; Intros Z M N h.
Exists N; Split; Auto.
Inversion_clear h.
Elim IHX with 1:=H; Intros N' h; Elim h; Intros h1 h2.
Exists N'; Split.
Rewrite h1; Reflexivity.
Exact h2.
Qed.

Lemma schroer_eoss : 
 (M,N:Adbmal;X,Z:stack)
  (schroer' M N Z)->
   (schroer' (eoss X M)(eoss X N) Z). 
Proof.
NewInduction X; Simpl; Intros Z h.
Exact h.
Apply schroer_eos; Apply IHX; Exact h.
Qed.

Lemma in_rename :
(M:Adbmal;x,w,z:name;Y:stack)
 (In w (names (rename M x z Y)))
 ->~w=z
  ->(In w (names M)).
Proof.
NewInduction M; Simpl; Intros x w z Y h h0.
NewDestruct (in_dec n Y).
Exact h.
NewDestruct (eq_dec n x).
Elim h; Intro h1.
Right; Apply h0; Symmetry; Exact h1.
Right; Exact h1.
Elim h; Intro h1.
Left; Exact h1.
Right; Exact h1.
Elim h; Intro h1.
Left; Exact h1.
Right; Apply IHM with 1:=h1 2:=h0.
NewInduction Y.
NewDestruct (eq_dec x n).
Elim h; Intro h1.
Elim h0; Symmetry; Exact h1.
Right; Exact h1.
Exact h.
NewDestruct (eq_dec n a).
Elim h; Intro h1.
Left; Exact h1.
Right; Apply IHM with 1:=h1 2:=h0.
Exact (IHY h).
Elim (in_juxt_or h); Intro h1.
Apply in_or_juxt; Left; Apply IHM1 with 1:=h1 2:=h0.
Apply in_or_juxt; Right; Apply IHM2 with 1:=h1 2:=h0.
Qed.

Lemma schroer_subst_skel_ind :
 (s:skel;M:Adbmal;h:s=(skeleton M);
  M',N,N':Adbmal;x,y,z:name;X,Y,Z1,Z2,W:stack)
  (schroer' N N' Z1)
   ->(schroer' (rename M x z Y)(rename M' y z Y) Z2)
    ->(scb (juxt Y (cons x W)) M)
     ->(scb (juxt Y (cons y W)) M')
      ->~(In z (names M))
       ->~(In z (names M'))
        ->~(In z Z2)
         ->(disjoint Z2 X)
          ->(disjoint Z2 Y)
           ->(disjoint Z2 Z1)
            ->(disjoint Z2 (names M))
             ->(disjoint Z2 (names M'))
              ->(disjoint Z2 (names N))
               ->(disjoint Z2 (names N'))
                ->(EX Z3:stack| 
                   (schroer' (adbmal_subst X Y M x N)(adbmal_subst X Y M' y N') Z3)).
Proof.
Intros s M h M' N N' x y z X Y Z1 Z2 W h0 h1.
Assert q : (skeleton M)=(skeleton M'). 
(* makes it easier to eliminate absurd cases *)
Rewrite (rename_skel_eq x z M Y).
Rewrite (rename_skel_eq y z M' Y).
Exact (schroer_skel h1).
Generalize M h M' q Y Z2 h1; Clear h1 Z2 Y q M' h M.
NewInduction s; NewDestruct M; Intro h.
(* var *)
NewDestruct M'; Simpl; 
 Intros q Y Z2 h1 b1 b2 d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
Exists Z1.
NewDestruct (in_dec n Y).
NewDestruct (in_dec n0 Y).
Inversion h1.
Apply schroer_var.
NewDestruct (eq_dec n0 y).
Inversion h1.
Elim d1; Left; Exact H.
Inversion h1.
Elim n1; Rewrite <- H; Exact i.
NewDestruct (eq_dec n x).
NewDestruct (in_dec n0 Y).
Inversion h1.
Elim d2; Left; Symmetry; Exact H.
NewDestruct (eq_dec n0 y).
NewDestruct (eq_dec y n0).
NewDestruct (eq_dec x n).
Apply schroer_eoss; Exact h0.
Elim n3; Symmetry; Exact e.
Elim n3; Symmetry; Exact e0.
Inversion h1.
Elim d2; Left; Symmetry; Exact H.
NewDestruct (in_dec n0 Y).
Inversion h1.
Elim n1; Rewrite H; Exact i.
NewDestruct (eq_dec n0 y).
Inversion h1.
Elim d1; Left; Exact H.
NewDestruct (eq_dec x n).
Elim n2; Symmetry; Exact e.
NewDestruct (eq_dec y n0).
Elim n4; Symmetry; Exact e.
Inversion h1.
Apply schroer_eoss; Apply schroer_eoss; Apply schroer_var.
(* impossible cases *)
Discriminate q.
Discriminate q.
Discriminate q.
Discriminate h.
Discriminate h.
Discriminate h.
Discriminate h.
Simpl in h; Injection h; Clear h; Intro h.
Rename a into t; Clear a.
NewDestruct M'; Simpl; Intros q Y Z2 h1.
Discriminate q.
(* abs *)
Inversion_clear h1.
Rename a into t0; Clear a.
Intros b1 b2 d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
Assert h1 : s=(skeleton (rename t n z0 Nil)).
Rewrite h; Apply rename_skel_eq.
Assert h2 : ~z0=z.
Intro h2; Apply d3; Left; Exact h2.
Assert h3 : ~(In z (names t)).
Intro h3; Apply d1; Right; Exact h3.
Assert d1' : ~(In z (names (rename t n z0 Nil))).
Exact (not_in_renamed_term h2 h3 7!Nil).
Assert h4 : ~(In z (names t0)).
Intro h4; Apply d2; Right; Exact h4.
Assert d2' : ~(In z (names (rename t0 n0 z0 Nil))).
Exact (not_in_renamed_term h2 h4 7!Nil).
Assert d3' : ~(In z Z).
Intro h5; Apply d3; Right; Exact h5.
Assert d4' : (disjoint Z X).
Intros w h5; Apply (d4 w (or_intror ?? h5)). 
Assert d5' : (disjoint Z (cons z0 Y)).
Intros w h5; Intro h6; Elim h6; Intro h7.
Apply H1; Rewrite h7; Exact h5.
Exact (d5 w (or_intror ?? h5) h7).
Assert d6' : (disjoint Z Z1).
Intros w h5 h6; Apply (d6 w).
Right; Exact h5.
Exact h6.
Assert d8' : (disjoint Z (names (rename t n z0 Nil))).
Intros w h5; Intro h6.
Apply (d8 w (or_intror ?? h5)); Right.
Assert h8 : ~w=z0.
Intro h8; Apply H1; Rewrite <- h8; Exact h5.
Exact (in_rename h6 h8).
Assert d9' : (disjoint Z (names (rename t0 n0 z0 Nil))).
Intros w h5; Intro h6.
Apply (d9 w (or_intror ?? h5)); Right.
Assert h8 : ~w=z0.
Intro h8; Apply H1; Rewrite <- h8; Exact h5.
Exact (in_rename h6 h8).
Assert d10' : (disjoint Z (names N)).
Intros w h5; Exact (d10 w (or_intror ?? h5)).
Assert d11' : (disjoint Z (names N')).
Intros w h5; Exact (d11 w (or_intror ?? h5)).
Assert h5 : (schroer' 
             (rename (rename t n z0 Nil) x z (cons z0 Y))
             (rename (rename t0 n0 z0 Nil) y z (cons z0 Y)) Z).
Assert h5 : ~z=n0.
Intro h5; Apply d2; Left; Symmetry; Exact h5.
Assert h7 : ~(In z0 (names t0)).
Intro h7; Apply (d9 z0 (or_introl ?? (refl_equal ? z0)));
 Right; Exact h7.
Assert h8 : ~z=n.
Intro h8; Apply d1; Left; Symmetry; Exact h8.
Assert h9 : ~(In z (names t)).
Intro h9; Apply d1; Right; Exact h9.
Assert h10 : ~(In z0 (names t)).
Intro h10; Apply (d8 z0 (or_introl ?? (refl_equal ? z0))); 
 Right; Exact h10.
Replace (cons z0 Y) with (juxt Nil (cons z0 Y)).
Rewrite <- (rename_commutes y h5 h4 h7 9!Nil Y [h]h [h]h).
Rewrite <- (rename_commutes x h8 h9 h10 9!Nil Y [h]h [h]h).
Exact H2.
Reflexivity.
Assert b1' := (scb_rename z0 4!Nil (scb_abs_inv b1)).
Assert b2' := (scb_rename z0 4!Nil (scb_abs_inv b2)).
Assert q' : (skeleton (rename t n z0 Nil))=(skeleton (rename t0 n0 z0 Nil)).
Injection q; Intro h6.
Rewrite <- (rename_skel_eq n z0 t Nil).
Rewrite <- (rename_skel_eq n0 z0 t0 Nil).
Exact h6.
Elim (IHs (rename t n z0 Nil) h1 (rename t0 n0 z0 Nil) q' (cons z0 Y) Z
           h5 b1' b2' d1' d2' d3' d4' d5' d6' d8' d9' d10' d11');
 Intros Z3 h6.
(* we cannot give (cons z0 Z3) as witness for the goal, as then we'd need
  that z0 not in Z3; therefore we introduce Z4: *)
Elim (fresh_list (length Z3)
      (juxt (cons z0 Z3)
            (juxt (names (adbmal_subst X (cons z0 Y)(rename t n z0 Nil) x N))
                  (names (adbmal_subst X (cons z0 Y)(rename t0 n0 z0 Nil) y N')))));
 Intros Z4 h7; Elim h7; Clear h7; Intros h7 h8; Elim h8; Clear h8;
 Intros h8 h9.
Elim (disjoint_juxt_and h8); Clear h8; Intros h8 h10.
Elim (disjoint_juxt_and h10); Clear h10; Intros h10 h11.
Assert h12 : (le (length Z3) (length Z4)).
Rewrite h7; Apply le_n.
Assert h13 : (disjoint Z4 Z3).
Intros w h13 h14; Apply (h8 w h13); Right; Exact h14.
Assert h14 := (schroer_change_Z h6 h12 h13 h10 h11 h9).
Exists (cons z0 Z4).
Assert p8 : ~(In z0 (names t)).
Intro p8; Apply (d8 z0 (or_introl ?? (refl_equal ? z0))); Right; 
 Exact p8.
Assert p9 : ~(In z0 (names N)).
Intro p9; Apply (d10 z0 (or_introl ?? (refl_equal ? z0))); Exact p9.
Assert p10 : ~(In z0 X).
Intro p10; Apply (d4 z0 (or_introl ?? (refl_equal ? z0))); Exact p10.
Assert p11 : ~(In z0 (cons n Y)).
Intro p11; Elim p11; Intro p12.
Apply (d8 z0 (or_introl ?? (refl_equal ? z0))); Left; Exact p12.
Exact (d5 z0 (or_introl ?? (refl_equal ? z0)) p12).
Assert p12 : ~(In z0 (names t0)).
Intro p12; Apply (d9 z0 (or_introl ?? (refl_equal ? z0))); Right; 
 Exact p12.
Assert p13 : ~(In z0 (names N')).
Intro p13; Apply (d11 z0 (or_introl ?? (refl_equal ? z0))); Exact p13.
Assert p14 : ~(In z0 (cons n0 Y)).
Intro p14; Elim p14; Intro p15.
Apply (d9 z0 (or_introl ?? (refl_equal ? z0))); Left; Exact p15.
Exact (d5 z0 (or_introl ?? (refl_equal ? z0)) p15).
Apply schroer_rule.
Exact (not_in_subst p8 p9 p10 p11).
Exact (not_in_subst p12 p13 p10 p14).
Intro h15; Apply (h8 z0 h15); Left; Reflexivity.
Replace (cons n Y) with (juxt Nil (cons n Y)).
Replace (cons n0 Y) with (juxt Nil (cons n0 Y)).
Rewrite (subst_rename_commute_open N X 5!Nil p8 (scb_abs_inv b1)).
Rewrite (subst_rename_commute_open N' X 5!Nil p12 (scb_abs_inv b2)).
Exact h14.
Reflexivity.
Reflexivity.
(* absurd cases *)
Discriminate q.
Discriminate q.
Discriminate h.
Discriminate h.
Discriminate h.
Discriminate h.
Simpl in h; Injection h; Clear h; Intro h.
NewDestruct M'; Intros q Y Z2 h1.
Discriminate q.
Discriminate q.
(* eos *)
Rename a into t; Clear a.
Rename a0 into t0; Clear a0.
Simpl in q; Injection q; Intro q'.
NewDestruct Y.
Intros b1 b2; Simpl in b1 b2.
Elim (scb_eos_inv b1); Intros e1 b1'.
Elim (scb_eos_inv b2); Intros e2 b2'.
Intros d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
Simpl; Simpl in h1.
NewDestruct (eq_dec x n).
NewDestruct (eq_dec y n0).
Inversion_clear h1.
Exists Z2.
Apply schroer_eoss.
Exact H.
Elim n1; Symmetry; Exact e2.
Elim n1; Symmetry; Exact e1.
Intros b1 b2; Simpl in b1 b2.
Elim (scb_eos_inv b1); Intros e1 b1'.
Elim (scb_eos_inv b2); Intros e2 b2'.
Simpl; Simpl in h1.
NewDestruct (eq_dec n n1).
NewDestruct (eq_dec n0 n1).
Inversion_clear h1.
Intros d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
Assert d1' : ~(In z (names t)).
Intro h1; Apply d1; Right; Exact h1.
Assert d2' : ~(In z (names t0)).
Intro h1; Apply d2; Right; Exact h1.
Assert d5' : (disjoint Z2 l).
Intros w h1 h2; Apply (d5 w h1); Right; Exact h2.
Assert d8' : (disjoint Z2 (names t)).
Intros w h1 h2; Apply (d8 w h1); Right; Exact h2.
Assert d9' : (disjoint Z2 (names t0)).
Intros w h1 h2; Apply (d9 w h1); Right; Exact h2.
Elim (IHs t h t0 q' l Z2 H b1' b2' d1' d2' d3 d4 d5' d6 d8' d9' d10 d11); 
 Intros Z3 h1.
Exists Z3; Apply schroer_eos; Exact h1.
Elim (n2 e2).
Elim (n2 e1).
Discriminate q.
Discriminate h.
Discriminate h.
Discriminate h.
Discriminate h.
Simpl in h; Injection h; Intros h1 h2.
NewDestruct M'; Intros q Y Z2 h3.
Discriminate q.
Discriminate q.
Discriminate q.
(* ap *)
Rename a into t; Rename a0 into t0; Rename a1 into t1; Rename a2 into t2; Clear a a0.
Simpl in q; Injection q; Intros q1 q2.
Intros b1 b2.
Elim (scb_ap_inv b1); Intros b1a b1b.
Elim (scb_ap_inv b2); Intros b2a b2b.
Simpl.
Intros d1 d2 d3 d4 d5 d6 d8 d9 d10 d11.
Assert d1a : ~(In z (names t)).
Intro h4; Apply d1; Apply in_or_juxt; Left; Exact h4.
Assert d1b : ~(In z (names t0)).
Intro h4; Apply d1; Apply in_or_juxt; Right; Exact h4.
Assert d2a : ~(In z (names t1)).
Intro h4; Apply d2; Apply in_or_juxt; Left; Exact h4.
Assert d2b : ~(In z (names t2)).
Intro h4; Apply d2; Apply in_or_juxt; Right; Exact h4.
Simpl in h3.
Inversion_clear h3.
Elim (disjoint_juxt_and d8); Intros d8a d8b.
Elim (disjoint_juxt_and d9); Intros d9a d9b.
Elim (IHs1 t h2 t1 q2 Y Z2 H b1a b2a d1a d2a d3 d4 d5 d6 d8a d9a d10 d11);
 Intros Z3a h4.
Elim (IHs2 t0 h1 t2 q1 Y Z2 H0 b1b b2b d1b d2b d3 d4 d5 d6 d8b d9b d10 d11);
 Intros Z3b h5.
Elim (schroer_ap_Z1Z2 h4 h5); Intros Z3 h6.
Exists Z3.
Exact h6.
Qed.

Lemma schroer_subst :
 (M,M',N,N':Adbmal;x,y,z:name;X,Y,Z1,Z2,W:stack)
  (schroer' N N' Z1)
   ->(schroer' (rename M x z Y)(rename M' y z Y) Z2)
    ->(scb (juxt Y (cons x W)) M)
     ->(scb (juxt Y (cons y W)) M')
      ->~(In z (names M))
       ->~(In z (names M'))
        ->~(In z Z2)
         ->(disjoint Z2 X)
          ->(disjoint Z2 Y)
           ->(disjoint Z2 Z1)
            ->(disjoint Z2 (names M))
             ->(disjoint Z2 (names M'))
              ->(disjoint Z2 (names N))
               ->(disjoint Z2 (names N'))
                ->(EX Z3:stack| 
                   (schroer' (adbmal_subst X Y M x N)(adbmal_subst X Y M' y N') Z3)).
Proof [M](schroer_subst_skel_ind (refl_equal ? (skeleton M))).

Lemma commute_schroer_beta_skel_ind : 
 (s:skel;M:Adbmal;h:s=(skeleton M);X:stack)
  (scb X M)
   ->(N:Adbmal)
      (adbmal_beta M N)
       ->(M':Adbmal;Z:stack)
          (schroer' M M' Z)
           ->(EX N':Adbmal|(adbmal_beta M' N')
              /\(EX Z':stack|(schroer' N N' Z'))).
Proof.
NewInduction s; NewDestruct M; Simpl.
Intros h X h0 N h1.
(* var *)
Inversion h1.
Intro h; Discriminate h.
Intro h; Discriminate h.
Intro h; Discriminate h.
Intro h; Discriminate h.
(* abs *)
Rename a into t; Clear a.
Intro h; Injection h; Clear h; Intro h.
Intros X h0 N h1.
Inversion_clear h1.
Clear N.
Intros M' Z h1.
Inversion_clear h1.
Assert h1 : s=(skeleton (rename t n z Nil)).
Rewrite h; Exact (rename_skel_eq n z t Nil).
Assert h2 := (scb_abs_inv h0).
Assert h3 := (rename_beta H0 H 8!Nil h2).
Assert h4 := (scb_rename z 4!Nil h2).
Elim (IHs ? h1 ? h4 ? h3 ?? H3); Intros N' h6; Elim h6; Clear h6; 
 Intros h6 h7; Elim h7; Clear h7; Intros Z' h7.
Simpl in h4.
Assert h8 := (scb_schroer H3 h4).
Assert h9 : ~(In z Nil).
Exact [h]h.
Assert h10 := (scb_rename2 H1 h9 h8).
Simpl in h10.
Elim (rename_bwr3 5!Nil h10 H1 h6); Intros P h11; Elim h11; Clear h11;
Intros h11 h12.
Rewrite h12 in h7.
Exists (abs y P); Split.
Apply beta_abs.
Exact h11.
Assert h13 := (not_in_beta H0 H).
Assert h14 := (not_in_beta H1 h11).
(* we need a z' not in N0,P,Z' *)
LetTac z' := (fresh (names (ap N0 (eoss Z' P)))).
Assert h15 := (fresh_not_in 1!(names (ap N0 (eoss Z' P)))).
Assert h16 : ~(In z' (names N0)).
Intro h16; Apply h15; Simpl; Apply in_or_juxt; Left; Exact h16.
Assert h17 : ~(In z' (names P)).
Intro h17; Apply h15; Simpl; Apply in_or_juxt; Right;
Apply in_eoss2; Exact h17.
Assert h18 : ~(In z' Z').
Intro h18; Apply h15; Simpl; Apply in_or_juxt; Right;
Apply in_eoss1; Exact h18.
Assert h19 := (rename_diff_schroer' h13 h14 h16 h17 h18 h7).
Exists (cons z' Z').
Apply schroer_rule.
Exact h16.
Exact h17.
Exact h18.
Exact h19.
Intro h; Discriminate h.
Intro h; Discriminate h.
Intro h; Discriminate h.
Intro h; Discriminate h.
(* eos *)
Rename a into t; Clear a.
Intro h; Injection h; Clear h; Intro h.
Intros X h0.
Elim (scb_eos_inv2 h0); Intros X' h1; Elim h1; Clear h1; Intros h1 h2.
Intros N h3.
Inversion_clear h3.
Intros M' Z h3.
Inversion_clear h3.
Elim (IHs t h X' h2 N0 H N1 Z H0); Intros N' h3; Elim h3; Clear h3;
Intros h3 h4.
Exists (eos n N'); Split.
Apply beta_eos; Exact h3.
Elim h4; Intros Z' h5.
Exists Z'; Apply schroer_eos; Exact h5.
Intro h; Discriminate h.
Intro h; Discriminate h.
Intro h; Discriminate h.
Intro h; Discriminate h.
(* ap *)
Rename a into t; Clear a.
Rename a0 into t0; Clear a0.
Intro h; Injection h; Clear h; Intros h h0.
Intros X h1.
Elim (scb_ap_inv h1); Clear h1; Intros h1 h2.
Intros N h3.
Inversion h3.
Intros P Z h4.
Inversion_clear h4.
Clear P.
Elim (IHs1 t h0 X h1 M' H2 M'0 Z H3); Intros P h4; Elim h4; Clear h4;
 Intros h4 h5; Elim h5; Clear h5; Intros Z' h5.
Exists (ap P N'); Split.
Apply beta_apl; Exact h4.
Exact (schroer_ap_Z1Z2 h5 H4).
Intros P Z h4.
Inversion_clear h4.
Clear P.
Elim (IHs2 t0 h X h2 M' H2 N' Z H4); Intros P h4; Elim h4; Clear h4;
 Intros h4 h5; Elim h5; Clear h5; Intros Z' h5.
Exists (ap M'0 P); Split.
Apply beta_apr; Exact h4.
Exact (schroer_ap_Z1Z2 H3 h5).
(* adbmal_beta *)
Rewrite <- H0 in h1.
Elim (scb_eoss_inv h1); Intros X' b; Elim b; Clear b; Intros e b1'.
Assert b1:= (scb_abs_inv b1'); Clear b1'.
Clear IHs1 IHs2 h h0 h1 h2 e X H2 H1 H0 N0 h3 s1 s2 N t.
Intros M' Z h4.
Inversion_clear h4; Clear M'.
Elim (schroer_eoss_inv1 H); Intros P h4; Elim h4; Clear H h4; Intros h5 h6.
Rewrite h5; Clear h5 M'0.
Generalize H0; Clear H0; Inversion_clear h6; Clear P.
Exists (adbmal_subst X0 Nil N y N'); Split.
Apply beta_rule.
(* choose Z2 fresh from [X0,M,N,zZ0] *)
Elim 
 (fresh_list (length Z0) 
  (juxt (names t0)(juxt (names N')
   (juxt (names M)(juxt (names N)
    (juxt X0 (cons z Z0)))))));
 Intros Z2 h; Elim h; Clear h; Intros h h0; Elim h0; Clear h0; 
 Intros h0 h1.
Assert h2 : (le (length Z0) (length Z2)).
Rewrite h; Apply le_n.
Clear h.
Elim (disjoint_juxt_and h0); Clear h0; Intros h3 h0; 
 Elim (disjoint_juxt_and h0); Clear h0; Intros h4 h0;
 Elim (disjoint_juxt_and h0); Clear h0; Intros h5 h0;
 Elim (disjoint_juxt_and h0); Clear h0; Intros h6 h0;
 Elim (disjoint_juxt_and h0); Clear h0; Intros h h0.
Assert h7 : (disjoint Z2 (names (rename M x z Nil))).
Unfold disjoint; Intros w h7 h8; Apply (h5 w h7).
Apply (in_rename h8).
Intro h9; Apply (h0 w h7); Left; Symmetry; Exact h9.
Assert h8 : (disjoint Z2 (names (rename N y z Nil))).
Unfold disjoint; Intros w h8 h9; Apply (h6 w h8).
Apply (in_rename h9).
Intro h10; Apply (h0 w h8); Left; Symmetry; Exact h10.
Assert h9 : (disjoint Z2 Z0).
Unfold disjoint; Intros w h9 h10; Apply (h0 w h9); Right; Exact h10.
Assert h10 := (schroer_change_Z H2 h2 h9 h7 h8 h1).
Assert b2 :=
 (scb_rename2 4!Nil H0 [f]f (scb_schroer h10 (scb_rename z 4!Nil b1))).
Simpl in b2.
Assert h11 : ~(In z Z2).
Intro h11; Apply (h0 z h11); Left; Reflexivity.
Assert h12 : (disjoint Z2 Nil).
Intros w h12 h13; Elim h13.
Exact (schroer_subst 9!Nil H3 h10 b1 b2 H H0 h11 h h12 h0 h5 h6 h3 h4).
Qed.

Lemma commute_schroer_beta : 
 (M:Adbmal;X:stack)
  (scb X M)
   ->(N:Adbmal)
      (adbmal_beta M N)
       ->(M':Adbmal;Z:stack)
          (schroer' M M' Z)
           ->(EX N':Adbmal|(adbmal_beta M' N')
              /\(EX Z':stack|(schroer' N N' Z'))).
Proof [M](commute_schroer_beta_skel_ind (refl_equal ? (skeleton M))).

Lemma commute_kahrs_beta :
 (M,N,M':Adbmal;X:stack)
  (scb X M)
   ->(adbmal_beta M N)
    ->(kahrs M M')
     ->(EX N':Adbmal|(adbmal_beta M' N')/\(kahrs N N')).
Proof.
Intros M N M' X b h h0.
Assert h1 : (schroer M M').
Apply (proj2 ?? same_schroer_kahrs); Exact h0.
Elim h1; Intros Z h2.
Elim (commute_schroer_beta b h h2); Intros N' h3; Elim h3; Clear h3; Intros h3 h4.
Exists N'; Split.
Exact h3.
Apply (proj1 ?? same_schroer_kahrs); Exact h4.
Qed.

Inductive omega : Adbmal->Adbmal->stack->Prop :=
| omega_rule : (x:name;M,M':Adbmal;X:stack)
                ~(In x (FV M Nil))->(omega M M' X)->(omega (eos x M) M' (cons x X))
| omega_var  : (x:name;X:stack)(omega (var x)(var x) X)
| omega_abs  : (x:name;M,M':Adbmal;X:stack)(omega M M'  (cons x X))
                ->(omega (abs x M)(abs x M') X)
| omega_ap   : (M1,M2,M1',M2':Adbmal;X:stack)
                (omega M1 M1' X)
                 ->(omega M2 M2' X)
                  ->(omega (ap M1 M2)(ap M1' M2') X).

Lemma omega_rule_gen :
 (M,N:Adbmal;X,Y:stack)
  (omega M N Y)
   ->(disjoint X (FV M Nil))
    ->(omega (eoss X M) N (juxt X Y)).
Proof.
NewInduction X; Intros Y h h0.
Exact h.
Simpl; Apply omega_rule.
Intro h1; Elim (h0 a).
Left; Reflexivity.
Rewrite FV_eoss_nil in h1; Exact h1.
Apply IHX.
Exact h.
Intros b h1.
Apply (h0 b).
Right; Exact h1.
Qed.

Lemma omega_gen_rule_inv :
 (M,N:Adbmal;Z,X:stack)
  (omega (eoss X M) N (juxt X Z))
   ->(disjoint X (FV M Nil))
      /\(omega M N Z).
Proof.
NewInduction X; Simpl; Intro h.
Split; [ Exact [_;f;_]f | Exact h ].
Inversion_clear h.
Elim (IHX H0); Intros h h0.
Split.
Intros u h1; Elim h1; Intro h2.
Rewrite <- h2; Intro h3; Apply H.
Rewrite FV_eoss_nil.
Exact h3.
Exact (h u h2).
Exact h0.
Qed.

Lemma omega_abs_inv : 
 (x:name;M,N:Adbmal;X:stack)
  (omega (abs x M)(abs x N) X)
   ->(omega M N (cons x X)).
Proof.
Intros x M N X h; Inversion_clear h; Assumption.
Qed.

Lemma omega_eoss_inv : 
 (M,N:Adbmal;X:stack)
  (omega M N X)
   ->(EX X1:stack|(EX M':Adbmal|(EX X2:stack|
      M=(eoss X1 M') 
       /\ X=(juxt X1 X2) 
        /\ (disjoint X1 (FV M' Nil))
         /\ (omega M' N X2)))).
Proof.
NewInduction 1.
Rename M' into N.
Elim IHomega; Intros X1 h; Elim h; Clear h; Intros M' h; Elim h;
 Clear h; Intros X2 h; Elim h; Clear h; Intros h h0; Elim h0; Clear h0;
 Intros h0 h1; Elim h1; Clear h1; Intros h1 h2.
Exists (cons x X1); Exists M'; Exists X2; Split.
Simpl; Rewrite h; Reflexivity.
Split.
Rewrite h0; Reflexivity.
Rewrite h in H.
Rewrite FV_eoss_nil in H.
Split.
Intros a h3; Elim h3; Intro h4.
Rewrite <- h4; Exact H.
Exact (h1 a h4).
Exact h2.
Exists (nil name); Exists (var x); Exists X; Split;
[ Reflexivity | Split; [ Reflexivity | Split; [ Intros a h; Elim h | Apply omega_var ] ] ].
Exists (nil name); Exists (abs x M); Exists X; Split; [ Reflexivity | Split; 
[ Reflexivity | Split; [ Intros a h; Elim h | Apply omega_abs; Assumption ] ] ].
Exists (nil name); Exists (ap M1 M2); Exists X; Split; [ Reflexivity | Split; 
[ Reflexivity | Split; [ Intros a h; Elim h | Apply omega_ap; Assumption ] ] ].
Qed.

Lemma omega_eoss_abs_inv : 
 (y:name;M,N:Adbmal;X:stack)
  (omega M (abs y N) X)
   ->(EX X1:stack|(EX M':Adbmal|(EX X2:stack|
      M=(eoss X1 (abs y M')) 
       /\ X=(juxt X1 X2) 
        /\ (disjoint X1 (FV (abs y M') Nil))
         /\ (omega M' N (cons y X2))))).
Proof.
NewInduction M; Intros N X h; Inversion_clear h.
Exists (nil name); Exists M; Exists X; Split;
[ Reflexivity | Split; [ Reflexivity | Split; [ Intros a h; Elim h | Assumption ] ] ].
Elim (IHM N X0 H0); Intros X1 h; Elim h; Clear h; Intros M' h; Elim h;
 Clear h; Intros X2 h; Elim h; Clear h; Intros h h0; Elim h0; Clear h0;
 Intros h0 h1; Elim h1; Clear h1; Intros h1 h2.
Exists (cons n X1); Exists M'; Exists X2; Split.
Simpl; Rewrite h; Reflexivity.
Split.
Rewrite h0; Reflexivity.
Rewrite h in H.
Rewrite FV_eoss_nil in H.
Split.
Intros a h3; Elim h3; Intro h4.
Rewrite <- h4; Exact H.
Exact (h1 a h4).
Exact h2.
Qed.

Lemma omega_target_eos_free : (M,N:Adbmal;X:stack)(omega M N X)->(eos_free N).
Proof.
NewInduction 1.
Exact IHomega.
Exact I.
Exact IHomega.
Split; [ Exact IHomega1 | Exact IHomega2 ].
Qed.

Lemma omega_scb :
 (M,N:Adbmal;X:stack)
  (omega M N X)
   ->(scb X M).
Proof.
NewInduction 1.
Apply scb_eos; Exact IHomega.
Apply scb_var.
Apply scb_abs; Exact IHomega.
Apply scb_ap; [ Exact IHomega1 | Exact IHomega2 ].
Qed.

Lemma omega_FV_sub1 :
 (M,M':Adbmal;X,Y:stack)(omega M M' (juxt X Y))->(sub (FV M' X)(FV M X)).
Proof.
NewInduction M; Intros M' X Y h; Inversion h.
Apply sub_refl.
Exact (IHM M'0 (cons n X) Y H3).
NewDestruct X.
Exact (IHM M' Nil X0 H4).
Simpl in H1; Injection H1; Intros h0 h1.
Simpl; Case (eq_dec n n0); Intro h2.
Apply sub_trans with l2:=(FV M' l).
Exact (FV_sub1 2!Nil 3!(cons n0 Nil) 4!l).
Rewrite h0 in H4.
Apply IHM with 1:=H4.
Elim (h2 h1).
Exact (sub_juxt (IHM1 M1' X Y H1) (IHM2 M2' X Y H4)).
Qed.

Lemma omega_FV_sub2 :
 (M,M':Adbmal;X,Y:stack)(omega M M' (juxt X Y))->(sub (FV M X)(FV M' X)).
Proof.
NewInduction M; Intros M' X Y h; Inversion h.
Apply sub_refl.
Exact (IHM M'0 (cons n X) Y H3).
NewDestruct X.
Exact (IHM M' Nil X0 H4).
Simpl in H1; Injection H1; Intros h0 h1.
Simpl; Case (eq_dec n n0); Intro h2.
Apply sub_trans with l2:=(FV M' l).
Rewrite h0 in H4.
Apply IHM with 1:=H4.
Assert h3 : (disjoint (cons n0 Nil) (FV M' Nil)).
Assert h3 : ~(In n (FV M' Nil)).
Intro h3; Apply H3.
Exact (omega_FV_sub1 3!Nil H4 h3).
Intros a h4 h5; Elim h4; Intro h6.
Apply h3; Rewrite h1; Rewrite h6; Exact h5.
Exact h6.
Assert h4 : (eos_free M').
Apply omega_target_eos_free with 1:=H4.
Exact (FV_sub2 h4 h3).
Elim (h2 h1).
Exact (sub_juxt (IHM1 M1' X Y H1) (IHM2 M2' X Y H4)).
Qed.

Lemma kahrs_weak :
(M,N:Adbmal;X1,X2,Y1,Y2:stack;x,y:name)
 (eos_free M)
  ->(length X1)=(length Y1)
   ->~(In x (FV M X1))
    ->~(In y (FV N Y1))
     ->(kahrs' M (juxt X1 X2) N (juxt Y1 Y2))
      ->(kahrs' M (juxt X1 (cons x X2)) N (juxt Y1 (cons y Y2))).
Proof.
NewInduction M.
NewDestruct N; Intros X1 X2 Y1 Y2 x y h h0 h1 h2 h3.
(* var *)
Clear h.
Assert h4 : (length X2)=(length Y2).
 Assert h5 := (kahrs_list_length h3).
 Rewrite length_juxt in h5; Rewrite length_juxt in h5.
 Rewrite h0 in h5.
 Exact (simpl_plus_l ??? h5).
Assert h5 : (length (cons x X2))=(length (cons y Y2)).
Simpl; Rewrite h4; Reflexivity.
Generalize h1 h2; Clear h1 h2; Simpl.
Case (in_dec n X1); Intro h6; Case (in_dec n0 Y1); Intro h7.
Intros h1 h2; Clear h1 h2.
Exact (kahrs_var_repl_tails h6 h0 h5 h3).
Elim h7; Exact (kahrs_var_in_in h3 h0 h6).
Elim h6; Exact (kahrs_var_in_in (kahrs_symm h3) (sym_eq ??? h0) h7).
Intros h1 h2.
Assert h8 : ~n=x.
Intro h; Apply h1; Left; Exact h.
Assert h9 : ~n0=y.
Intro h; Apply h2; Left; Exact h. 
Exact (kahrs_var_weak h0 h6 h7 (kahrs_var3 h8 h9 (kahrs_var_rm_top h0 h6 h3))).
(* diff M N *)
Inversion h3.
Inversion h3.
Inversion h3.
NewDestruct N; Intros X1 X2 Y1 Y2 x y h h0 h1 h2 h3.
(* diff M N *) Inversion h3.
(* abs *)
Rename a into t; Clear a.
Inversion_clear h3.
Apply kahrs_abs.
Exact (IHM t (cons n X1) X2 (cons n0 Y1) Y2 x y h (eq_S ?? h0) h1 h2 H).
(* diff M N *)
Inversion h3.
Inversion h3.
(* eos *)
Intros N X1 X2 Y1 Y2 x y h; Inversion h.
NewDestruct N; Intros X1 X2 Y1 Y2 x y h h0 h1 h2 h3.
(* diff M N *)
Inversion h3.
Inversion h3.
Inversion h3.
(* ap *)
Rename a into t; Clear a.
Rename a0 into t0; Clear a0.
Inversion_clear h3.
Elim h; Intros h4 h5.
Assert h6 : ~(In x (FV M1 X1))/\~(In x (FV M2 X1)).
 Split; Intro h6; Apply h1; Simpl; Apply in_or_juxt.
 Left; Exact h6.
 Right; Exact h6.
Elim h6; Clear h6; Intros h6 h7.
Assert h8 : ~(In y (FV t Y1))/\~(In y (FV t0 Y1)).
 Split; Intro h8; Apply h2; Simpl; Apply in_or_juxt.
 Left; Exact h8.
 Right; Exact h8.
Elim h8; Clear h8; Intros h8 h9.
Apply kahrs_ap.
Exact (IHM1 t X1 X2 Y1 Y2 x y h4 h0 h6 h8 H).
Exact (IHM2 t0 X1 X2 Y1 Y2 x y h5 h0 h7 h9 H0).
Qed.

Lemma kahrs_omega_commute : 
 (M,M',N,N':Adbmal;X,X':stack)
  (kahrs' M X M' X')
   ->(omega M N X)
    ->(omega M' N' X')
     ->(kahrs' N X N' X').
Proof.
NewInduction M; Intros M' N N' X X' h; Inversion_clear h.
Intro h; Inversion_clear h.
Intro h; Inversion_clear h.
Apply kahrs_var1.
Intro h; Inversion_clear h.
Intro h; Inversion_clear h.
Apply kahrs_var2; Assumption.
Intro h; Inversion_clear h.
Intro h; Inversion_clear h.
Apply kahrs_var3; Assumption.
Intro h; Inversion_clear h.
Intro h; Inversion_clear h.
Apply kahrs_abs.
Apply IHM with 1:=H 2:=H0 3:=H1.
Intro h; Inversion_clear h.
Intro h; Inversion_clear h.
Intro h; Inversion_clear h.
Assert h1 : ~(In n (FV N Nil)).
 Intro h; Apply H0; Exact (omega_FV_sub1 3!Nil H1 h).
Assert h2 : ~(In y (FV N' Nil)).
 Intro h; Apply H2; Exact (omega_FV_sub1 3!Nil H3 h).
Exact (kahrs_weak (omega_target_eos_free H1)(refl_equal ? (length Nil)) h1 h2 (IHM ????? H H1 H3)).
Intro h; Inversion h.
Elim (H H4).
Intro h; Inversion_clear h.
Intro h; Inversion_clear h.
Apply kahrs_ap.
Exact (IHM1 ?? ?? ? H H1 H3).
Exact (IHM2 ?? ?? ? H0 H2 H4).
Qed.

Lemma phone_lemma' : 
 (x,y:name;M:Adbmal)
  (eos_free M)
   ->(N:Adbmal)
      (skeleton M)=(skeleton N) (* for convenience only, follows from third assumpion *)
       ->(X1,X2,Y1,Y2:stack)
          (kahrs' M (juxt X1 (cons x X2)) N (juxt Y1 (cons y Y2)))
           ->(length X1)=(length Y1)
            ->~(In x (FV M X1))
             ->(kahrs' M (juxt X1 X2) N (juxt Y1 Y2))/\~(In y (FV N Y1)).
Proof.
NewInduction M; Intro h.
(* var *) 
Clear h; NewDestruct N; Intro h.
Clear h.
Simpl.
Intros X1 X2 Y1 Y2 h h0.
Case (in_dec n X1); Intro h1; Case (in_dec n0 Y1); Intro h2.
Intro h3; Clear h3.
Split.
Assert h3 : (length X2)=(length Y2).
Assert h3 := (kahrs_list_length h).
Rewrite length_juxt in h3; Rewrite length_juxt in h3; Rewrite h0 in h3. 
Assert h4 : (length (cons x X2))=(length (cons y Y2)).
Rewrite (simpl_plus_l ??? h3); Reflexivity.
Injection h4; Exact [d]d.
Exact (kahrs_var_repl_tails h1 h0 h3 h).
Exact [z]z.
Intro h3; Clear h3.
Elim h2; Exact (kahrs_var_in_in h h0 h1).
Elim h1; Exact (kahrs_var_in_in (kahrs_symm h) (sym_eq ??? h0) h2).
Intro h3.
Assert h6 := (kahrs_var_rm_top h0 h1 h).
Split.
Apply kahrs_var_weak.
Exact h0.
Exact h1.
Exact h2.
Apply (kahrs_var_rm_top 1!n 2!n0 3!(cons x Nil) 4!X2 5!(cons y Nil) 6!Y2 (refl_equal ??)).
Intro h4; Elim h4; Intro h5.
Apply h3; Left; Symmetry; Exact h5.
Exact h5.
Exact h6.
Generalize h3; Clear h3; Inversion_clear h6.
Intros h3 h4.
Apply h3; Left; Reflexivity.
Intros h3 h4.
Elim h4.
Assumption.
Exact [f]f.
(* N diff skel *)
Discriminate h.
Discriminate h.
Discriminate h.
(* abs *)
NewDestruct N; Intro h0.
(* N diff skel *)
Discriminate h0.
Rename a into t; Clear a.
Simpl in h0; Injection h0; Clear h0; Intro h0.
Intros X1 X2 Y1 Y2 h1 h2 h3.
Inversion_clear h1.
Elim (IHM h t h0 (cons n X1) X2 (cons n0 Y1) Y2 H (eq_S ?? h2) h3); Intros h4 h5; Split.
Apply kahrs_abs; Exact h4.
Exact h5.
(* N diff skel *)
Discriminate h0.
Discriminate h0.
(* eos *)
Elim h.
(* ap *)
Simpl in h.
Elim h; Clear h; Intros h h0.
NewDestruct N; Intro h1.
(* N diff skel *)
Discriminate h1.
Discriminate h1.
Discriminate h1.
Rename a into t; Clear a.
Rename a0 into t0; Clear a0.
Simpl in h1; Injection h1; Clear h1; Intros h1 h2.
Intros X1 X2 Y1 Y2 h3 h4 h5.
Assert h6 : ~(In x (FV M1 X1))/\~(In x (FV M2 X1)).
Simpl in h5.
Split; Intro h6; Apply h5; Apply in_or_juxt; [ Left; Exact h6 | Right; Exact h6 ].
Elim h6; Clear h6; Intros h6 h7.
Inversion_clear h3.
Elim (IHM1 h t h2 X1 X2 Y1 Y2 H h4 h6); Intros h8 h9.
Elim (IHM2 h0 t0 h1 X1 X2 Y1 Y2 H0 h4 h7); Intros h10 h11.
Split.
Apply kahrs_ap; Assumption.
Intro h12; Elim (in_juxt_or h12); Assumption.
Qed.

Lemma phone_lemma : 
 (M,N:Adbmal;X,Y:stack;x,y:name)
  (eos_free M)
   ->~(In x (FV M Nil))
    ->(kahrs' M (cons x X) N (cons y Y))
     ->(kahrs' M X N Y)/\~(In y (FV N Nil)).
Proof [M,N;X,Y;x,y;h;h0;h1]
       (phone_lemma' h (kahrs_skel h1) 7!Nil 9!Nil h1 (refl_equal ? O) h0).

Lemma omega_kahrs_postpone :
 (M,P:Adbmal;X:stack)
  (omega M P X)
   ->(N:Adbmal;Y:stack)
      (kahrs' P X N Y)
       ->(EX Q:Adbmal|(omega Q N Y)/\(kahrs' M X Q Y)).
Proof.
NewInduction 1; Intros N Y h.
(* omega_rule *)
Assert h0 : (length Y)=(S(length X)).
Symmetry; Exact (kahrs_list_length h).
Elim (length_S h0); Intros y h1; Elim h1; Clear h0 h1; Intros Y' h0.
Rewrite h0; Rewrite h0 in h; Clear h0.
Assert h0 := (omega_target_eos_free H0).
Assert h1 : ~(In x (FV M' Nil)).
Intro h1; Apply H; Exact (omega_FV_sub1 3!Nil H0 h1).
Elim (phone_lemma h0 h1 h); Intros h2 h3.
Elim (IHomega N Y' h2); Intros Q h4; Elim h4; Clear h4; Intros h4 h5.
Exists (eos y Q); Split.
Assert h6 : ~(In y (FV Q Nil)).
Intro h6; Apply h3.
Exact (omega_FV_sub2 3!Nil h4 h6).
Exact (omega_rule h6 h4).
Apply kahrs_eos2.
Exact h5.
(* omega_var *)
Inversion_clear h.
Exists (var x); Split.
Apply omega_var.
Apply kahrs_var1.
Exists (var y); Split.
Apply omega_var.
Apply kahrs_var2.
Assumption.
Exists (var y); Split.
Apply omega_var.
Apply kahrs_var3; Assumption.
(* omega_abs *)
Inversion_clear h.
Elim (IHomega N0 (cons y Y) H0); Intros Q h; Elim h; Clear h; Intros h h0.
Exists (abs y Q); Split; [ Exact (omega_abs h) | Exact (kahrs_abs h0) ].
(* omega_ap *)
Inversion_clear h.
Elim IHomega1 with 1:=H0; Intros Q1 h; Elim h; Clear h; Intros h h0.
Elim IHomega2 with 1:=H2; Intros Q2 h1; Elim h1; Clear h1; Intros h1 h2.
Exists (ap Q1 Q2); Split; [ Exact (omega_ap h h1) | Exact (kahrs_ap h0 h2) ].
Qed.

Lemma rename_sub :
 (x,y:name;M:Adbmal;Z:stack) 
  (sub (names (rename M x y Z)) (cons y (names M))).
Proof.
NewInduction M; Intro Z.
Simpl;Case (in_dec n Z); Intro h.
Intros u h0; Right; Elim h0; Intro h1;
[ Left; Exact h1 | Right; Exact h1 ].
Case (eq_dec n x); Intro h0.
Intros u h1; Elim h1; Intro h2;
[ Left; Exact h2 | Right; Right; Exact h2 ].
Intros u h1; Right; Elim h1; Intro h2;
[ Left; Exact h2 | Right; Exact h2 ].
Intros u h1; Elim h1; Intro h2.
Right; Left; Exact h2.
Elim IHM with 1:=h2; Intro h3.
Left; Exact h3.
Right; Right; Exact h3.
NewInduction Z.
Simpl.
Case (eq_dec x n); Intro h.
Simpl.
Intros u h0; Elim h0; Intro h1.
Left; Exact h1.
Right; Right; Exact h1.
Intros u h0; Right; Exact h0.
Simpl.
Case (eq_dec n a); Intro h.
Intros u h0; Elim h0; Intro h1.
Right; Left; Exact h1.
Elim (IHM Z u h1); Intro h2.
Left; Exact h2.
Right; Right; Exact h2.
Exact IHZ.
Simpl.
Intros u h; Elim (in_juxt_or h); Intro h0.
Elim (IHM1 Z u h0); Intro h1.
Left; Exact h1.
Right; Apply in_or_juxt; Left; Exact h1.
Elim (IHM2 Z u h0); Intro h1.
Left; Exact h1.
Right; Apply in_or_juxt; Right; Exact h1.
Qed.

Lemma rename_eos_free_not_in_FV_id :
(x,y:name;M:Adbmal;X:stack)
 (eos_free M)
  ->~(In x (FV M X))
   ->(rename M x y X) = M.
Proof.
NewInduction M; Intros X h; Simpl.
Case (in_dec n X); Intro h0.
Reflexivity.
Intro h1.
Case (eq_dec n x); Intro h2.
Elim h1; Left; Exact h2.
Reflexivity.
Intro h0.
Rewrite (IHM (cons n X) h h0); Reflexivity.
Elim h.
Elim h; Intros h1 h2.
Intro h0.
Elim (dmx [d](h0 (in_or_juxt d))); Intros h3 h4.
Rewrite (IHM1 X h1 h3); Rewrite (IHM2 X h2 h4); Reflexivity.
Qed.

Lemma kahrs_find_var :
 (x:name;X:stack)
  (In x X)
   ->(Y:stack)
      (length X)=(length Y)
       ->(all_distinct Y)
        ->(EX y:name|(In y Y) /\ (kahrs' (var x) X (var y) Y)).
Proof.
NewInduction X; Intro c; [ Elim c | NewDestruct Y; Intro h ].
Discriminate h.
Rename l into Y; Rename a into x'; Rename n into y'; Clear l a n.
Simpl in h; Injection h; Clear h; Intros h h0.
Inversion_clear h0.
Case (eq_dec x' x); Intro h0.
Rewrite h0; Exists y'; Split; [ Left; Reflexivity | Apply kahrs_var2; Exact h ].
Elim c; Intro h1.
Elim (h0 h1).
Elim (IHX h1 Y h H); Intros y h2; Elim h2; Clear h2; Intros h2 h3.
Assert h4 : ~y'=y.
Intro h4; Apply H0; Rewrite h4; Exact h2.
Exists y; Split; [ Right; Exact h2 | Apply kahrs_var3; Auto ].
Qed.

End Alpha.
