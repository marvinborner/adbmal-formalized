Require Export lambda.
Require Export alpha.
Require Export adbmal_subst_lems.

Set Implicit Arguments.

Section Projecting_Adbmal_to_Lambda.

Lemma project_subst' : 
 forall (N':Adbmal) (N:Lambda) (x:name) (X Z:stack),
 (omega N' (emb N) (juxt X Z)) 
  -> forall M1 M2:Adbmal,
    (skeleton M1)=(skeleton M2) (*redundant*)
     -> forall Y1 Y2:stack,
       (length Y1)=(length Y2) (*redundant*)
        ->(scb (juxt Y1 (cons x Z)) M1) (* redundant, follows from 1,2 *)
         ->(disjoint Y2 (cons x (FV N' Nil)))
          ->(kahrs' M1 (juxt Y1 (cons x Z)) M2 (juxt Y2 (cons x Z))) (*1*)
           -> forall M:Lambda,
             (omega M2 (emb M) (juxt Y2 (cons x Z)))(*2*)
              ->(disjoint X (FV M1 (juxt Y1 (cons x Nil))))
               -> exists P:Adbmal,
                  (kahrs' (adbmal_subst X Y1 M1 x N') (juxt Y1 (juxt X Z)) 
                          (adbmal_subst X Y2 P x N') (juxt Y2 (juxt X Z)))
                  /\(omega (adbmal_subst X Y2 P x N')
                           (emb (lambda_subst M x N))
                           (juxt Y2 (juxt X Z))).
Proof.
intros N' N x X Z oN.
intro M1; induction M1.
(* var *)
intro M2; destruct M2; intro c.
clear c.
intros Y1 Y2 c b c0 h.
destruct M; intro h0; generalize h; clear h; inversion_clear h0; intros h c1.
(* M1 = (var n) ; M2 = (var n1) ; M = (var_l n1) *)
exists (var n1).
simpl.
destruct (in_dec n Y1) as [h0|h0]; destruct (in_dec n1 Y2) as [h1|h1].
clear c1.
split.
exact (@kahrs_var_repl_tails n n1 (cons x Z) (cons x Z)
         (juxt X Z) (juxt X Z) Y1 Y2
         h0 c (eq_refl (length (juxt X Z))) h).
unfold lambda_subst; simpl.
destruct (eq_dec n1 x) as [h2|h2].
exfalso; apply (c0 n1 h1).
left; symmetry; exact h2.
simpl; apply omega_var.
elim (h1 (@kahrs_var_in_in n n1 Y1 (cons x Z) Y2 (cons x Z) h c h0)).
elim (h0 (@kahrs_var_in_in n1 n Y2 (cons x Z) Y1 (cons x Z)
            (@kahrs_symm (var n) (var n1) (juxt Y1 (cons x Z))
               (juxt Y2 (cons x Z)) h) (eq_sym c) h1)).
pose proof
  (@kahrs_var_inj n n1 (cons x Z)
     (@kahrs_var_rm_top n n1 Y1 (cons x Z) Y2 (cons x Z) c h0 h)) as h2.
rewrite h2.
unfold lambda_subst; simpl.
destruct (eq_dec x n1) as [h3|h3]; destruct (eq_dec n1 x) as [h4|h4].
split.
apply kahrs_eoss2.
exact c.
apply kahrs_refl.
apply omega_rule_gen.
exact oN.
intros u h6 h7.
apply (c0 u h6); right; exact h7.
elim h4; symmetry; exact h3.
elim h3; symmetry; exact h4.
split.
apply kahrs_eoss2.
exact c.
apply kahrs_eoss2.
reflexivity.
apply kahrs_refl.
apply omega_rule_gen.
apply omega_rule_gen.
simpl; apply omega_var.
intros u h5 h6; apply (c1 u h5).
simpl.
destruct (in_dec n (juxt Y1 (cons x Nil))) as [h7|h7].
elim (@in_juxt_or name Y1 (cons x Nil) n h7); intro h8.
exact (h0 h8).
elim h8; intro h9.
elim h3; rewrite h9; exact h2.
exact h9.
generalize h6; simpl; destruct (in_dec n1 Nil) as [h10|h10].
elim h10.
intro h8; elim h8; intro h9.
left; rewrite h2; exact h9.
right; exact h9.
rewrite FV_eoss_nil.
simpl.
destruct (in_dec n1 Nil) as [h5|h5].
elim h5.
intros u h6 h7; elim h7; intro h8.
apply h1; rewrite h8; exact h6.
exact h8.
(* diff skel M1 M2 *)
discriminate c.
discriminate c.
discriminate c.
intro M2; destruct M2 as [n1|n1 M2|n1 M2|M2a M2b]; intro c.
discriminate c.
(* abs *)
simpl in c; injection c; clear c; intro c.
intros Y1 Y2 c0 b c1 h.
pose proof (scb_abs_inv b) as b'.
destruct M; intro h0; generalize h; clear h; inversion_clear h0; intros h h1.
rename H into h0.
rename n into y1.
rename n0 into y2.
(* ________________________________________________________________ *)
unfold lambda_subst; simpl; fold skeleton_l.
pose (F :=
 fix aux (z:name) (p:Lambda) (d:skeleton_l p = skeleton_l M)
         (n:nat) {struct n} : Lambda :=
 match n with
 | O => abs_l z (lambda_subst_skel_rec p (skeleton_l M) x N d)
 | S m =>
     let y' := fresh (cons x (juxt (names_l p) (FV_l N))) in
     aux y' (rename_l p z y') (eq_trans (rename_l_skel_eq p z y') d) m
 end).
assert (h2 :
 forall (n:nat) (z:name) (p:Lambda)
        (d:skeleton_l p = skeleton_l M) (m2:Adbmal),
  (skeleton M1)=(skeleton m2)
   ->(n=O->~(In z (cons x (FV N' Nil))))
   ->(kahrs' (abs y1 M1)(juxt Y1 (cons x Z))(abs z m2)(juxt Y2 (cons x Z)))
    ->(omega (abs z m2)(abs z (emb p))(juxt Y2 (cons x Z)))
     -> exists P:Adbmal,
        (kahrs' (adbmal_subst X Y1 (abs y1 M1) x N') (juxt Y1 (juxt X Z)) 
                (adbmal_subst X Y2 P x N') (juxt Y2 (juxt X Z)))
         /\(omega (adbmal_subst X Y2 P x N') (emb(F z p d n))
                  (juxt Y2 (juxt X Z)))).
intro n; induction n as [|n IHn]; intros z p d m2 c2 c3 h2 h3.
(* O *)
inversion_clear h2.
inversion_clear h3.
assert (c4 : (disjoint (cons z Y2) (cons x (FV N' Nil)))).
 intros u h2; elim h2; intro h3.
 rewrite <- h3; exact (c3 (eq_refl O)).
 exact (c1 u h3).
elim (IHM1 m2 c2 (cons y1 Y1) (cons z Y2) (f_equal S c0) b' c4 H p H0 h1); intros P h4; 
 elim h4; clear h4; intros h4 h5.
exists (abs z P); simpl; split.
apply kahrs_abs; exact h4.
apply omega_abs.
rewrite (lambda_subst_skel_rec_repl_skel p N x d (eq_refl (skeleton_l p))).
exact h5.
(* S *)
clear c3.
simpl.
set (y' := fresh (cons x (juxt (names_l p) (FV_l N)))).
set (d' := eq_trans (rename_l_skel_eq p z y') d).
assert (c4 : ~(In y' (cons x (FV N' Nil)))).
intro h5; apply (fresh_not_in (cons x (juxt (names_l p) (FV_l N)))); fold y'.
elim h5; intro h6.
left; exact h6.
right; apply in_or_juxt; right.
unfold FV_l.
rewrite <- (FV_l2s N Nil).
fold emb.
exact (omega_FV_sub2 Nil _ oN y' h6).
assert (a : ~(In y' Nil)).
exact (fun z => z).
assert (a0 : ~(In y' (names (emb p)))).
rewrite <- names_l2s.
intro h4.
assert (h5 : (In y' (cons x (juxt (names_l p) (FV_l N))))).
right; apply in_or_juxt; left; exact h4.
apply (fresh_not_in (cons x (juxt (names_l p) (FV_l N)))); exact h5.
pose proof
  (@kahrs_rename z y' (emb p) (juxt Y2 (cons x Z)) Nil a a0) as a1.
simpl in a1.
pose proof (kahrs_abs a1) as a2.
rewrite <- rename_l2s in a2.
fold emb in a2.
elim (omega_kahrs_postpone h3 a2); intros Q a3; elim a3; clear a3; intros a3 a4.
pose proof (kahrs_trans h2 a4) as a5.
inversion a5.
rewrite <- H2 in a3.
rewrite <- H2 in a5.
assert (H5 : y = y').
inversion a3; reflexivity.
rewrite H5 in a3.
rewrite H5 in a5.
clear H H0 H1 H2 H3 H4 H5 a4 x0 y Q M0 X0 Y.
pose proof (kahrs_skel a5) as a6.
simpl in a6; injection a6; clear a6; intro a6.
exact (IHn y' (rename_l p z y') d' N0 a6 (fun _ => c4) a5 a3).
exact (fun b => b).
unfold in_10.
destruct (in_dec y2 (cons x (FV_l N))) as [h3|h3].
refine (h2 (S O) y2 M (eq_refl (skeleton_l M)) M2 c _ h (omega_abs h0)).
intro h4; discriminate h4.
assert (h4 : ~(In y2 (cons x (FV N' Nil)))).
intro h4; apply h3; elim h4; intro h5.
left; exact h5.
right.
unfold FV_l.
rewrite <- FV_l2s.
exact (omega_FV_sub2 Nil _ oN y2 h5).
exact (h2 O y2 M (eq_refl (skeleton_l M)) M2 c
         (fun _ : O = O => h4) h (omega_abs h0)).
(* ________________________________________________________________ *)
(* diff skel M1 M2 *)
discriminate c.
discriminate c.
intro M2; destruct M2 as [n1|n1 M2|n1 M2|M2a M2b]; intro c.
discriminate c.
discriminate c.
(* eos *)
simpl in c; injection c; clear c; intro c.
destruct Y1 as [|y1 Y1]; destruct Y2 as [|y2 Y2]; intro c0.
simpl.
intro b; elim (scb_eos_inv b); clear b; intros e b.
rewrite e; clear e.
clear c0.
intro c0; clear c0.
intro h; inversion_clear h.
intros M h h0.
inversion_clear h.
assert (h1 : ~(In x (FV (emb M) Nil))).
intro h1.
apply H0.
exact (omega_FV_sub1 Nil _ H1 x h1).
pose proof (subst_l_not_in M N x Nil Z (fun d => d) h1) as h2.
simpl in h2.
elim (omega_kahrs_postpone H1 (kahrs_symm h2)); intros P' h3; elim h3;
clear h3; intros h3 h4.
exists (eos x P'); simpl.
destruct (eq_dec x x) as [_|hne].
pose proof (kahrs_trans H h4) as h5.
split.
apply kahrs_eoss2.
reflexivity.
exact h5.
apply omega_rule_gen.
exact h3.
rewrite <- (kahrs_FV_eq2 h5).
exact h0.
exfalso; apply hne; reflexivity.
intros M h.
inversion h.
elim (H0 H4).
discriminate c0.
discriminate c0.
simpl in c0; injection c0; intro c1.
intro b; simpl in b; elim (scb_eos_inv b); clear b; intros e b; rewrite e; clear e.
intro c2.
assert (c3 : (disjoint Y2 (cons x (FV N' nil)))).
intros u h; apply (c2 u); right; exact h.
intro h; simpl in h; inversion_clear h.
intros M h; inversion_clear h; simpl.
destruct (eq_dec y1 y1) as [h|h]; [ clear h | elim h; reflexivity ].
intro c4.
elim (IHM1 M2 c Y1 Y2 c1 b c3 H M H1 c4); intros P h; elim h; clear h; intros h h0.
exists (eos y2 P); simpl.
destruct (eq_dec y2 y2) as [h1|h1]; [ clear h1 | elim h1; reflexivity ].
split.
apply kahrs_eos2; exact h.
apply omega_rule.
intro h1.
pose proof (FV_subst_l_sub x M N) as h2.
pose proof (omega_FV_sub1 Nil _ H1) as h3.
pose proof (omega_FV_sub2 Nil _ h0) as h4.
pose proof (omega_FV_sub1 Nil _ oN) as h5.
unfold FV_l in h2; rewrite <- FV_l2s in h2.
elim (@in_juxt_or name (FV_l_rec M Nil) (FV_l_rec N Nil) y2
        (h2 y2 (h4 y2 h1))); rewrite <- FV_l2s; intro h6.
exact (H0 (h3 y2 h6)).
apply (c2 y2 (or_introl (eq_refl y2))); right.
exact (h5 y2 h6).
exact h0.
intros M h; elim H0; inversion h; reflexivity.
discriminate c.
(* ap *)
rename M1_1 into M1a.
rename M1_2 into M1b.
rename IHM1_1 into IHa.
rename IHM1_2 into IHb.
intro M2; destruct M2 as [n|n M2|n M2|M2a M2b]; simpl; intro c.
discriminate c.
discriminate c.
discriminate c.
injection c; intros cb ca.
intros Y1 Y2 c3 b.
elim (scb_ap_inv b); intros ba bb.
intros c4 h.
inversion_clear h.
destruct M as [n|n M|Ma Mb]; intro h; inversion_clear h.
intro c5; simpl in c5.
assert (da : (disjoint X (FV M1a (juxt Y1 (cons x Nil))))).
 intros u h h0; exact
   (c5 u h (@in_or_juxt name (FV M1a (juxt Y1 (cons x Nil)))
               (FV M1b (juxt Y1 (cons x Nil))) u (or_introl h0))).
assert (db : (disjoint X (FV M1b (juxt Y1 (cons x Nil))))).
 intros u h h0; exact
   (c5 u h (@in_or_juxt name (FV M1a (juxt Y1 (cons x Nil)))
               (FV M1b (juxt Y1 (cons x Nil))) u (or_intror h0))).
elim (IHa M2a ca Y1 Y2 c3 ba c4 H Ma H1 da); intros Pa h; elim h; clear h; intros h1a h2a.
elim (IHb M2b cb Y1 Y2 c3 bb c4 H0 Mb H2 db); intros Pb h; elim h; clear h; intros h1b h2b.
simpl; fold skeleton_l.
exists (ap Pa Pb); split.
exact (kahrs_ap h1a h1b).
rewrite (lambda_subst_skel_rec_repl_skel Ma N x
  (proj1 (skel_l_inj_ap
    (eq_refl (skel_l_ap (skeleton_l Ma) (skeleton_l Mb)))))
  (eq_refl (skeleton_l Ma))).
rewrite (lambda_subst_skel_rec_repl_skel Mb N x
  (proj2 (skel_l_inj_ap
    (eq_refl (skel_l_ap (skeleton_l Ma) (skeleton_l Mb)))))
  (eq_refl (skeleton_l Mb))).
exact (omega_ap h2a h2b).
Qed.

Lemma project_subst : 
 forall (M1 M2 N':Adbmal) (M N:Lambda) (x:name)
        (X Y1 Y2 Z:stack),
  (scb (juxt Y1 (cons x Z)) M1) (* redundant *)
   ->(disjoint X (FV M1 (juxt Y1 (cons x Nil))))
    ->(disjoint Y2 (cons x (FV N' Nil)))
     ->(kahrs' M1 (juxt Y1 (cons x Z)) M2 (juxt Y2 (cons x Z)))
      ->(omega M2 (emb M) (juxt Y2 (cons x Z)))
       ->(omega N' (emb N) (juxt X Z)) 
        -> exists P:Adbmal,
           (kahrs' (adbmal_subst X Y1 M1 x N') (juxt Y1 (juxt X Z))
                   (adbmal_subst X Y2 P x N') (juxt Y2 (juxt X Z)))
           /\(omega (adbmal_subst X Y2 P x N')
                    (emb (lambda_subst M x N)) (juxt Y2 (juxt X Z))).
Proof.
intros M1 M2 N' M N x X Y1 Y2 Z h h0 h1 h2 h3 h4.
pose proof (kahrs_list_length h2) as h5.
rewrite length_juxt in h5; rewrite length_juxt in h5.
pose proof (simpl_plus_r (length (cons x Z)) (length Y1) (length Y2) h5) as h6.
pose proof (kahrs_skel h2) as h7.
exact (@project_subst' N' N x X Z h4 M1 M2 h7 Y1 Y2 h6
         h h1 h2 M h3 h0).
Qed.

(* diagram C' *)

Lemma project_beta :
 forall (M N:Adbmal) (X:stack),
  (adbmal_beta M N)
   -> forall M':Lambda,
      (omega M (emb M') X)
       -> exists N1:Adbmal, exists N2:Lambda,
          (kahrs' N X N1 X)
           /\(omega N1 (emb N2) X)
            /\(lambda_beta M' N2).
Proof.
intro M; induction M; intros N X h; inversion_clear h; clear N; simpl.
(* beta_abs *)
intro M'; destruct M' as [z|z t|ta tb]; intro h; inversion_clear h.
(* M' = abs n t *)
elim (IHM N0 (cons z X) H t H0); intros N1 h; elim h; clear h ; 
 intros N2 h; elim h; clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (abs z N1); exists (abs_l z N2); split; 
 [ exact (kahrs_abs h)  | split; [exact (omega_abs h0) |  exact (lambda_beta_abs z h1)] ].
(* beta_eos *)
intros M' h; inversion_clear h.
elim (IHM N0 X0 H M' H1); intros N1 h; elim h; clear h ; 
 intros N2 h; elim h; clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (eos n N1); exists N2; split; [ exact (kahrs_eos2 n n h) | split ].
assert (h2 : ~(In n (FV N1 Nil))).
 rewrite <- (kahrs_FV_eq2 h).
 intro h2.
 exact (H0 (beta_FV_sub H Nil n h2)).
exact (omega_rule n h2 h0).
exact h1.
(* beta_apl *)
clear IHM2.
rename M' into M1'.
destruct M' as [z|z t|t t0]; intro h; inversion_clear h.
elim (IHM1 M1' X H t H0); intros N1 h; elim h; clear h; 
 intros N2 h; elim h; clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (ap N1 M2); exists (ap_l N2 t0); split;
 [ exact (kahrs_ap h (kahrs_refl M2 X)) 
   | split; [ exact (omega_ap h0 H1) | exact (lambda_beta_apl t0 h1) ]].
(* beta_apr *)
clear IHM1.
rename M' into M2'.
destruct M' as [z|z t|t t0]; intro h; inversion_clear h.
elim (IHM2 M2' X H t0 H1); intros N1 h; elim h; clear h; 
 intros N2 h; elim h; clear h; intros h h0; elim h0; clear h0; intros h0 h1.
exists (ap M1 N1); exists (ap_l t N2); split;
 [ exact (kahrs_ap (kahrs_refl M1 X) h) 
   | split; [ exact (omega_ap H0 h0) | exact (lambda_beta_apr t h1) ]].
(* beta_rule *)
clear IHM1 IHM2.
destruct M' as [z|z t|t t0]; intro h; inversion_clear h.
elim (@scb_eoss_inv X0 X (abs x M) (omega_scb H));
  intros Z h; elim h; clear h; intros e b.
rewrite <- e in H; rewrite <- e in H0; rewrite <- e.
clear e X.
rename X0 into X.
elim (omega_gen_rule_inv (abs x M) Z X H); intros h h0.
destruct t as [z|z t|ta tb]; inversion h0.
rewrite <- H4; rewrite <- H4 in H6; clear H2 H5 H4 H3 H1 X0 M' M0 x0 h0.
elim (@project_subst M M M2 t t0 x X Nil Nil Z
      (scb_abs_inv b) h (fun _ f _ => f)
      (kahrs_refl M (cons x Z)) H6 H0);
  intros P h0; elim h0; clear h0; intros h0 h1.
exists (adbmal_subst X nil P x M2); exists (lambda_subst t x t0); split; 
 [ exact h0 | split; [ exact h1 | apply lambda_beta_rule ]].
Qed.

End Projecting_Adbmal_to_Lambda.
