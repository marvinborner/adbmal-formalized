Require Export lambda.
Require Export alpha.
Require Export adbmal_subst_lems.

Set Implicit Arguments.

Section Projecting_Adbmal_to_Lambda.

Lemma project_subst' : 
 (N':Adbmal;N:Lambda;x:name;X,Z:stack)
 (omega N' (emb N) (juxt X Z)) 
  ->(M1,M2:Adbmal)
    (skeleton M1)=(skeleton M2) (*redundant*)
     ->(Y1,Y2:stack)
       (length Y1)=(length Y2) (*redundant*)
        ->(scb (juxt Y1 (cons x Z)) M1) (* redundant, follows from 1,2 *)
         ->(disjoint Y2 (cons x (FV N' Nil)))
          ->(kahrs' M1 (juxt Y1 (cons x Z)) M2 (juxt Y2 (cons x Z))) (*1*)
           ->(M:Lambda)
             (omega M2 (emb M) (juxt Y2 (cons x Z)))(*2*)
              ->(disjoint X (FV M1 (juxt Y1 (cons x Nil))))
               ->(EX P:Adbmal | 
                  (kahrs' (adbmal_subst X Y1 M1 x N') (juxt Y1 (juxt X Z)) 
                          (adbmal_subst X Y2 P x N') (juxt Y2 (juxt X Z)))
                  /\(omega (adbmal_subst X Y2 P x N')
                           (emb (lambda_subst M x N))
                           (juxt Y2 (juxt X Z)))).
Proof.
Intros N' N x X Z oN.
NewInduction M1.
(* var *)
NewDestruct M2; Intro c.
Clear c.
Intros Y1 Y2 c b c0 h.
NewDestruct M; Intro h0; Generalize h; Clear h; Inversion_clear h0; Intros h c1.
(* M1 = (var n) ; M2 = (var n1) ; M = (var_l n1) *)
Exists (var n1).
Simpl.
Case (in_dec n Y1); Intro h0; Case (in_dec n1 Y2); Intro h1.
Clear c1.
Split.
Exact (kahrs_var_repl_tails h0 c (refl_equal ? (length (juxt X Z))) h).
Unfold lambda_subst; Simpl.
Case (eq_dec n1 x); Intro h2.
Elim c0 with 1:=h1.
Left; Symmetry; Exact h2.
Simpl; Apply omega_var.
Elim (h1 (kahrs_var_in_in h c h0)).
Elim (h0 (kahrs_var_in_in (kahrs_symm h)(sym_eq ??? c) h1)).
Assert h2 := (kahrs_var_inj (kahrs_var_rm_top c h0 h)).
Rewrite h2.
Unfold lambda_subst; Simpl.
Case (eq_dec x n1); Intro h3; Case (eq_dec n1 x); Intro h4.
Split.
Apply kahrs_eoss2.
Exact c.
Apply kahrs_refl.
Apply omega_rule_gen.
Exact oN.
Intros u h6 h7.
Apply (c0 u h6); Right; Exact h7.
Elim h4; Symmetry; Exact h3.
Elim h3; Symmetry; Exact h4.
Split.
Apply kahrs_eoss2.
Exact c.
Apply kahrs_eoss2.
Reflexivity.
Apply kahrs_refl.
Apply omega_rule_gen.
Apply omega_rule_gen.
Simpl; Apply omega_var.
Intros u h5 h6; Apply (c1 u h5).
Simpl.
Case (in_dec n (juxt Y1 (cons x Nil))); Intro h7.
Elim (in_juxt_or h7); Intro h8.
Exact (h0 h8).
Elim h8; Intro h9.
Elim h3; Rewrite h9; Exact h2.
Exact h9.
Generalize h6; Simpl; Case (in_dec n1 Nil); Intro h10.
Elim h10.
Intro h8; Elim h8; Intro h9.
Left; Rewrite h2; Exact h9.
Right; Exact h9.
Rewrite FV_eoss_nil.
Simpl.
Case (in_dec n1 Nil); Intro h5.
Elim h5.
Intros u h6 h7; Elim h7; Intro h8.
Apply h1; Rewrite h8; Exact h6.
Exact h8.
(* diff skel M1 M2 *)
Discriminate c.
Discriminate c.
Discriminate c.
NewDestruct M2; Intro c.
Discriminate c.
(* abs *)
Simpl in c; Injection c; Clear c; Intro c.
Rename a into M2; Clear a.
Intros Y1 Y2 c0 b c1 h.
Assert b' := (scb_abs_inv b).
NewDestruct M; Intro h0; Generalize h; Clear h; Inversion_clear h0; Intros h h1.
Rename H into h0.
Rename n into y1; Clear n.
Rename n1 into y2; Clear n1.
Rename l into M; Clear l.
Clear Mind.
(* ________________________________________________________________ *)
Unfold lambda_subst; Simpl; Fold skeleton_l.
LetTac F :=
 Fix aux {aux [z:name;p:Lambda;d:((skeleton_l p)=(skeleton_l M));n:nat] : Lambda :=
 Cases n of
 | O    => (abs_l z (lambda_subst_skel_rec p (skeleton_l M) x N d))
 |(S m) => [y':=(fresh (cons x (juxt (names_l p) (FV_l N))))]
           (aux y' (rename_l p z y') (trans_eq ???? (rename_l_skel_eq p z y') d) m)
 end}.
Assert h2 :
 (n:nat;z:name;p:Lambda;d:(skeleton_l p)=(skeleton_l M);m2:Adbmal)
  (skeleton M1)=(skeleton m2)
   ->(n=O->~(In z (cons x (FV N' Nil))))
   ->(kahrs' (abs y1 M1)(juxt Y1 (cons x Z))(abs z m2)(juxt Y2 (cons x Z)))
    ->(omega (abs z m2)(abs z (emb p))(juxt Y2 (cons x Z)))
     ->(EX P:Adbmal |
        (kahrs' (adbmal_subst X Y1 (abs y1 M1) x N') (juxt Y1 (juxt X Z)) 
                (adbmal_subst X Y2 P x N') (juxt Y2 (juxt X Z)))
         /\(omega (adbmal_subst X Y2 P x N') (emb(F z p d n)) (juxt Y2 (juxt X Z)))).
NewInduction n; Intros z p d m2 c2 c3 h2 h3.
(* O *)
Inversion_clear h2.
Inversion_clear h3.
Assert c4 : (disjoint (cons z Y2) (cons x (FV N' Nil))).
 Intros u h2; Elim h2; Intro h3.
 Rewrite <- h3; Exact (c3 (refl_equal ? O)).
 Exact (c1 u h3).
Elim (IHM1 m2 c2 (cons y1 Y1) (cons z Y2) (eq_S ?? c0) b' c4 H p H0 h1); Intros P h4; 
 Elim h4; Clear h4; Intros h4 h5.
Exists (abs z P); Simpl; Split.
Apply kahrs_abs; Exact h4.
Apply omega_abs.
Rewrite (lambda_subst_skel_rec_repl_skel N x d (refl_equal ? (skeleton_l p))).
Exact h5.
(* S *)
Clear c3.
Simpl.
LetTac y':=(fresh (cons x (juxt (names_l p) (FV_l N)))).
LetTac d':=(trans_eq skel_l (skeleton_l (rename_l p z y')) (skeleton_l p)
       (skeleton_l M) (rename_l_skel_eq p z y') d).
Assert c4 : ~(In y' (cons x (FV N' Nil))).
Intro h5; Apply (fresh_not_in 1!(cons x (juxt (names_l p) (FV_l N)))); Fold y'.
Elim h5; Intro h6.
Left; Exact h6.
Right; Apply in_or_juxt; Right.
Unfold FV_l.
Rewrite <- (FV_l2s N Nil).
Fold emb.
Exact (omega_FV_sub2 3!Nil oN h6).
Assert a : ~(In y' Nil).
Exact [z]z.
Assert a0 : ~(In y' (names (emb p))).
Rewrite <- names_l2s.
Intro h4.
Assert h5 : (In y' (cons x (juxt (names_l p) (FV_l N)))).
Right; Apply in_or_juxt; Left; Exact h4.
Apply (fresh_not_in h5); Clear h4 h5.
Assert a1 := (kahrs_rename z (juxt Y2 (cons x Z)) a a0).
Simpl in a1.
Assert a2 := (kahrs_abs a1).
Rewrite <- rename_l2s in a2.
Fold emb in a2.
Elim (omega_kahrs_postpone h3 a2); Intros Q a3; Elim a3; Clear a3; Intros a3 a4.
Assert a5 := (kahrs_trans h2 a4).
Inversion a5.
Rewrite <- H2 in a3.
Rewrite <- H2 in a5.
Assert y=y'.
Inversion a3; Reflexivity.
Rewrite H5 in a3.
Rewrite H5 in a5.
Clear H H0 H1 H2 H3 H4 H5 a4 x0 y Q M0 X0 Y.
Assert a6 := (kahrs_skel a5).
Simpl in a6; Injection a6; Clear a6; Intro a6.
Exact (IHn y' (rename_l p z y') d' N0 a6 [_]c4 a5 a3).
Exact [b]b.
Unfold in_10.
Case (in_dec y2 (cons x (FV_l N))); Intro h3.
Apply h2 with 1:=c 3:=h 4:=(omega_abs h0).
Intro h4; Discriminate h4.
Assert h4 : ~(In y2 (cons x (FV N' Nil))).
Intro h4; Apply h3; Elim h4; Intro h5.
Left; Exact h5.
Right.
Unfold FV_l.
Rewrite <- FV_l2s.
Exact (omega_FV_sub2 3!Nil oN h5).
Apply h2 with 1:=c 2:=[_:(O=O)]h4 3:=h 4:=(omega_abs h0).
(* ________________________________________________________________ *)
(* diff skel M1 M2 *)
Discriminate c.
Discriminate c.
NewDestruct M2; Intro c.
Discriminate c.
Discriminate c.
(* eos *)
Simpl in c; Injection c; Clear c; Intro c.
Rename a into M2; Clear a.
NewDestruct Y1; NewDestruct Y2; Intro c0.
Simpl.
Intro b; Elim (scb_eos_inv b); Clear b; Intros e b.
Rewrite e; Clear e.
Clear c0.
Intro c0; Clear c0.
Intro h; Inversion_clear h.
Intros M h h0.
Inversion_clear h.
Assert h1 : ~(In x (FV (emb M) Nil)).
Intro h1.
Apply H0.
Exact (omega_FV_sub1 3!Nil H1 h1).
Assert h2 := (subst_l_not_in N 4!Nil Z [d]d h1).
Simpl in h2.
Elim (omega_kahrs_postpone H1 (kahrs_symm h2)); Intros P' h3; Elim h3;
Clear h3; Intros h3 h4.
Exists (eos x P'); Simpl.
NewDestruct (eq_dec x x).
Assert h5 := (kahrs_trans H h4).
Split.
Apply kahrs_eoss2.
Reflexivity.
Exact h5.
Apply omega_rule_gen.
Exact h3.
Rewrite <- (kahrs_FV_eq2 h5).
Exact h0.
Elim n1; Reflexivity.
Intros M h.
Inversion h.
Elim (H0 H4).
Discriminate c0.
Discriminate c0.
Rename l into Y1; Clear l.
Rename l0 into Y2; Clear l0.
Simpl in c0; Injection c0; Intro c1.
Intro b; Simpl in b; Elim (scb_eos_inv b); Clear b; Intros e b; Rewrite e; Clear e.
Intro c2.
Assert c3 : (disjoint Y2 (cons x (FV N' (nil name)))).
Intros u h; Apply (c2 u); Right; Exact h.
Intro h; Simpl in h; Inversion_clear h.
Intros M h; Inversion_clear h; Simpl.
Case (eq_dec n1 n1); Intro h; [ Clear h | Elim h; Reflexivity ].
Intro c4.
Rename n1 into y1; Rename n2 into y2; Clear n1 n2.
Elim (IHM1 M2 c Y1 Y2 c1 b c3 H M H1 c4); Intros P h; Elim h; Clear h; Intros h h0.
Exists (eos y2 P); Simpl.
Case (eq_dec y2 y2); Intro h1; [ Clear h1 | Elim h1; Reflexivity ].
Split.
Apply kahrs_eos2; Exact h.
Apply omega_rule with 2:=h0.
Intro h1.
Assert h2 := (FV_subst_l_sub 1!x 2!M 3!N).
Assert h3 := (omega_FV_sub1 3!Nil H1).
Assert h4 := (omega_FV_sub2 3!Nil h0).
Assert h5 := (omega_FV_sub1 3!Nil oN).
Unfold FV_l in h2; Rewrite <- FV_l2s in h2.
Elim (in_juxt_or (h2 y2 (h4 y2 h1))); Rewrite <- FV_l2s; Intro h6.
Exact (H0 (h3 y2 h6)).
Apply (c2 y2 (or_introl ?? (refl_equal ? y2))); Right.
Exact (h5 y2 h6).
Intros M h; Elim H0; Inversion h; Reflexivity.
Discriminate c.
(* ap *)
Rename M0 into M1a; Clear M0.
Rename M2 into M1b; Clear M2.
Rename IHM0 into IHa; Clear IHM0.
Rename IHM2 into IHb; Clear IHM2.
NewDestruct M2; Simpl; Intro c.
Discriminate c.
Discriminate c.
Discriminate c.
Injection c; Intros cb ca.
Intros Y1 Y2 c3 b.
Elim (scb_ap_inv b); Intros ba bb.
Intros c4 h.
Inversion_clear h.
NewDestruct M; Intro h; Inversion_clear h.
Intro c5; Simpl in c5.
Assert da : (disjoint X (FV M1a (juxt Y1 (cons x Nil)))).
 Intros u h h0; Exact (c5 u h (in_or_juxt (or_introl ?? h0))).
Assert db : (disjoint X (FV M1b (juxt Y1 (cons x Nil)))).
 Intros u h h0; Exact (c5 u h (in_or_juxt (or_intror ?? h0))).
Rename a into M2a; Clear a.
Rename a0 into M2b; Clear a0.
Rename l into Ma; Clear l.
Rename l0 into Mb; Clear l0.
Elim (IHa M2a ca Y1 Y2 c3 ba c4 H Ma H1 da); Intros Pa h; Elim h; Clear h; Intros h1a h2a.
Elim (IHb M2b cb Y1 Y2 c3 bb c4 H0 Mb H2 db); Intros Pb h; Elim h; Clear h; Intros h1b h2b.
Simpl; Fold skeleton_l.
Exists (ap Pa Pb); Split.
Exact (kahrs_ap h1a h1b).
LetTac ha := 
 (proj1 (skeleton_l Ma)=(skeleton_l Ma) (skeleton_l Mb)=(skeleton_l Mb)
  (skel_l_inj_ap (refl_equal ? (skel_l_ap (skeleton_l Ma) (skeleton_l Mb))))).
LetTac hb := 
 (proj2 (skeleton_l Ma)=(skeleton_l Ma) (skeleton_l Mb)=(skeleton_l Mb)
  (skel_l_inj_ap (refl_equal ? (skel_l_ap (skeleton_l Ma) (skeleton_l Mb))))).
Rewrite (lambda_subst_skel_rec_repl_skel N x ha (refl_equal ? (skeleton_l Ma))).
Rewrite (lambda_subst_skel_rec_repl_skel N x hb (refl_equal ? (skeleton_l Mb))).
Exact (omega_ap h2a h2b).
Qed.

Lemma project_subst : 
 (M1,M2,N':Adbmal;M,N:Lambda;x:name;X,Y1,Y2,Z:stack)
  (scb (juxt Y1 (cons x Z)) M1) (* redundant *)
   ->(disjoint X (FV M1 (juxt Y1 (cons x Nil))))
    ->(disjoint Y2 (cons x (FV N' Nil)))
     ->(kahrs' M1 (juxt Y1 (cons x Z)) M2 (juxt Y2 (cons x Z)))
      ->(omega M2 (emb M) (juxt Y2 (cons x Z)))
       ->(omega N' (emb N) (juxt X Z)) 
        ->(EX P:Adbmal | 
           (kahrs' (adbmal_subst X Y1 M1 x N') (juxt Y1 (juxt X Z))
                   (adbmal_subst X Y2 P x N') (juxt Y2 (juxt X Z)))
           /\(omega (adbmal_subst X Y2 P x N')(emb (lambda_subst M x N))(juxt Y2 (juxt X Z)))).
Proof.
Intros M1 M2 N' M N x X Y1 Y2 Z h h0 h1 h2 h3 h4.
Assert h5 := (kahrs_list_length h2).
Rewrite length_juxt in h5; Rewrite length_juxt in h5.
Assert h6 := (simpl_plus_r h5).
Assert h7 := (kahrs_skel h2).
Exact (project_subst' h4 h7 h6 h h1 h2 h3 h0).
Qed.

(* diagram C' *)

Lemma project_beta :
 (M,N:Adbmal;X:stack)
  (adbmal_beta M N)
   ->(M':Lambda)
      (omega M (emb M') X)
       ->(EX N1:Adbmal|(EX N2:Lambda|
          (kahrs' N X N1 X)
           /\(omega N1 (emb N2) X)
            /\(lambda_beta M' N2))).
Proof.
NewInduction M; Intros N X h; Inversion_clear h; Clear N; Simpl.
(* beta_abs *)
NewDestruct M'; Intro h; Inversion_clear h.
(* M' = abs n t *)
Rename l into t; Clear l.
Elim (IHM N0 (cons n0 X) H t H0); Intros N1 h; Elim h; Clear h ; 
 Intros N2 h; Elim h; Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (abs n0 N1); Exists (abs_l n0 N2); Split; 
 [ Exact (kahrs_abs h)  | Split; [Exact (omega_abs h0) |  Exact (lambda_beta_abs n0 h1)] ].
(* beta_eos *)
Intros M' h; Inversion_clear h.
Elim (IHM N0 X0 H M' H1); Intros N1 h; Elim h; Clear h ; 
 Intros N2 h; Elim h; Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (eos n N1); Exists N2; Split; [ Exact (kahrs_eos2 n n h) | Split ].
Assert h2 : ~(In n (FV N1 Nil)).
 Rewrite <- (kahrs_FV_eq2 h).
 Intro h2.
 Exact (H0 (beta_FV_sub H h2)).
Exact (omega_rule h2 h0).
Exact h1.
(* beta_apl *)
Clear IHM2.
Rename M' into M1'.
NewDestruct M'; Intro h; Inversion_clear h.
Rename l into t; Clear l.
Rename l0 into t0; Clear l0.
Elim (IHM1 M1' X H t H0); Intros N1 h; Elim h; Clear h; 
 Intros N2 h; Elim h; Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (ap N1 M2); Exists (ap_l N2 t0); Split;
 [ Exact (kahrs_ap h (kahrs_refl M2 X)) 
   | Split; [ Exact (omega_ap h0 H1) | Exact (lambda_beta_apl t0 h1) ]].
(* beta_apr *)
Clear IHM1.
Rename M' into M2'.
NewDestruct M'; Intro h; Inversion_clear h.
Rename l into t; Clear l.
Rename l0 into t0; Clear l0.
Elim (IHM2 M2' X H t0 H1); Intros N1 h; Elim h; Clear h; 
 Intros N2 h; Elim h; Clear h; Intros h h0; Elim h0; Clear h0; Intros h0 h1.
Exists (ap M1 N1); Exists (ap_l t N2); Split;
 [ Exact (kahrs_ap (kahrs_refl M1 X) h) 
   | Split; [ Exact (omega_ap H0 h0) | Exact (lambda_beta_apr t h1) ]].
(* beta_rule *)
Clear IHM1 IHM2.
NewDestruct M'; Intro h; Inversion_clear h.
Rename l into t; Clear l.
Rename l0 into t0; Clear l0.
Elim (scb_eoss_inv (omega_scb H)); Intros Z h; Elim h; Clear h; Intros e b.
Rewrite <- e in H; Rewrite <- e in H0; Rewrite <- e.
Clear e X.
Rename X0 into X.
Elim (omega_gen_rule_inv H); Intros h h0.
NewDestruct t; Inversion h0.
Rename l into t; Clear l.
Rewrite <- H4; Rewrite <- H4 in H6; Clear H2 H5 H4 H3 H1 X0 M' M0 x0 h0.
Elim (project_subst 8!Nil 9!Nil (scb_abs_inv b) h [_;f;_]f 
      (kahrs_refl M (cons x Z)) H6 H0); Intros P h0; Elim h0; Clear h0; Intros h0 h1.
Exists (adbmal_subst X (nil name) P x M2); Exists (lambda_subst t x t0); Split; 
 [ Exact h0 | Split; [ Exact h1 | Apply lambda_beta_rule ]].
Qed.

End Projecting_Adbmal_to_Lambda.
