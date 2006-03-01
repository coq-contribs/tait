Require Export TaitCore.
Require Export Eta.
Require Export WN. 

Set Implicit Arguments.

Module RequirementsProofEtaExp <: Requirements.
 (* begin hide *)
 Module Rename.
 (* end hide *)

 Definition abstr (k:nat)(rho:type)(r:term) := 
  \rho, sub_swap0 r k.

 Inductive N (rhos:context)(rho:type)(r s:term) : Prop := 
   N_intro : forall t, WN r t -> EtaExp rhos rho t s -> N rhos rho r s.

Lemma Ax1 : forall r s rhos rho sigma k, F rhos (rho-->sigma) r k -> 
  N (rhos++ext_ctx rhos k rho) sigma (r;k) s -> 
  N rhos (rho-->sigma) r (\!k:rho, s).
 Proof. 
 intros.
 set (u:=r;k).
 assert (u=r;k).
  auto.
 clearbody u.
 assert (ext_ctx rhos k rho <> nil).
   red; intros.
   destruct H.
   generalize (ext_ctx_length rhos k rho); simp; rewrite H2; simpl; intro; omega.
 assert (H8:=@app_removelast_last _ (ext_ctx rhos k rho) dtype H2).
 rewrite ext_ctx_last in H8; [idtac|destruct H;auto].
 set (taus:=removelast (ext_ctx rhos k rho)) in *; clearbody taus.
 assert (L : k - length rhos = length taus).
 destruct H.
 apply eq_add_S.
 replace (S (length taus)) with (length (taus++rho::nil)).
 rewrite <- H8.
 generalize (ext_ctx_length rhos k rho H3); simp; omega.
 simp; auto.
 rewrite H8 in H0; clear H8 H2. 
 destruct H0.
 rewrite <- H1 in H0.
 generalize  L H1 H2  H; clear  L H1 H2 H.
 generalize r s k rho sigma taus rhos;  clear r s  k rho sigma taus rhos.
 induction H0; intros.

destruct l as [|t0 l0].
 inversion H1.
 destruct l' as [|t0' l0'].
 inversion H.
 destruct (@exists_last _ (t0::l0)) as [l (t,Htl)]; try discriminate.
  rewrite Htl in H; rewrite Htl in H1; clear Htl t0 l0.
 destruct (@exists_last _ (t0'::l0')) as [l' (t',Htl)]; try discriminate.
  rewrite Htl in H; rewrite Htl in H2; clear Htl t0' l0'.
 rewrite <- apps_app in H1; simpl in H1.
 injection H1; clear H1; intros; subst.
 destruct (WNs_last _ _ _ _ H); clear H; intros.
 assert (t'=[k]).
   inversion H3.
   replace [k] with ([k];;nil) in H; auto.
   assert (H6:=apps_form_unique2 _ _ _ _ H).
   intuition; subst.   
   inversion H4; auto.
   replace [k] with ([k];;nil) in H; auto.
   replace (((\ rho0, r); s0);; l0) with ((\ rho0, r);; (s0::l0)) in H; auto.
   assert (H6:=apps_form_unique1 _ _ _ _ H).
   intuition; discriminate.
 subst; clear H3.
 exists (n;;l'); auto.
 inversion H2; [ idtac |  rewrite <- apps_app in H; discriminate ].

 subst t.
 assert (H8:=apps_form_unique2 _ _ _ _ H (refl_equal false) (refl_equal false)).
 subst.
 assert (H8:=apps_form_unique1 _ _ _ _ H (refl_equal false) (refl_equal false)).
 injection H8; clear H8; intro; subst. 
 clear H.
 destruct (@exists_last _ sigmas) as [sigmas' (sigma',Htl')].
   inversion H4; try discriminate.
   assert (length (@nil term)  = (S (length l'))). 
   rewrite H8; simp; auto.
   discriminate.
 subst.
 destruct (@exists_last _ ss) as [ss' (etak,Htl)].
   inversion H4; try discriminate.
   assert (length (@nil term)  = (S (length l'))). 
   rewrite H8; simp; auto.
   discriminate.
 subst.
 destruct (EtaExps_last _ _ _ _ _ _ H4).
 clear H4.
 rewrite arrows_app in H3; simpl in H3.
 assert (rho = sigma').
   assert (length l = length sigmas').
    clear H5 H7 H3 H2 H0 etak sigma' sigma.
    generalize H H1; clear H H1; generalize sigmas' ss' l';clear sigmas' ss' l'.    
    induction l; intros.
     inversion H1; subst.
     inversion H; subst; auto.
     inversion H1; subst.
     inversion H; subst; simp.
     f_equal.
     eauto.
   clear H5 H H7 H2 H1 etak ss' l'.
   destruct H0.
   set (r:=[n]) in *; clearbody r.
   generalize H4 H3 H0 H; clear H4 H3 H0 H.
   generalize sigmas' r; clear sigmas' r.
   induction l; simpl; intros.
    destruct sigmas'; simpl in *;  try discriminate.
    assert (H5:= TypJ_ext_ctx r rhos (taus++rho::nil) _ H).
    destruct H3; destruct H5; congruence.
    destruct sigmas' as [| sigma0 sigmas']; simpl in *; try discriminate.
    apply IHl with sigmas' (r;a); auto.      
    eapply TypJ_App with sigma0; auto.
    set (mus := taus++rho::nil) in *.
    assert (H5:=TypJ_ext_ctx _ _ mus _ H).
    clear H.
    split.
    destruct H5.    
    assert (CorTyp (rhos++mus) (r;a)).
     eapply CorTyp_apps; eauto.
    inversion H2; auto. 
    destruct H5.    
    assert (CorTyp (rhos++mus) (r;a)).
     eapply CorTyp_apps; eauto.
    inversion H2; subst.
    destruct H3.
    congruence.
 subst sigma'.
 apply EtaExp_Var with sigmas' ss'; auto.

  destruct H0 as [(T,T1) T2]. 
  assert  (T3:=CorTyp_apps _ _ T).
  inversion_clear T3.
  split; auto. 
  destruct H3; auto.
  simpl in H4; simpl; rewrite app_nth1 in H4; auto. 
 
 eapply EtaExps_red_ctx; eauto.
  assert (above (length rhos) (n;;l')).
  red; intros.
  apply WN_occurs with (n;;l).
  constructor; auto.
  apply F_occurs with rhos (rho --> sigma).
  destruct H0; red; auto.
 destruct (above_apps _ _ H4); auto.

 rewrite <- apps_app in H7; simpl in *.
 destruct H0.
 constructor 2 with taus etak; auto.
 simp; omega.
 inversion H5; auto.
 replace [k] with (k;;nil) in H6;auto.
 assert (H16:=apps_form_unique2 _ _ _ _ H6 (refl_equal false) (refl_equal false)).
 subst.
 assert (H16:=apps_form_unique1 _ _ _ _ H6 (refl_equal false) (refl_equal false)).
 injection H16; clear H16; intro; subst; auto.
 inversion H9; subst; auto.

 discriminate H1.

 destruct l. 
 clear IHWN.
 simpl in *.
 injection H1; clear H1; intros.
 subst.
 assert (rho0 = rho).
  destruct H as [(H,H1) _].
  simpl in H1; injection H1; auto.
 subst.
 assert (S1 : sub1 k = (map Var (k::nil))#0); auto.
 rewrite S1 in H0. 
 destruct (WN_subk H0 (k::nil) 0 r) as [t0 (H3,H4)]; auto.
 rewrite <- S1 in H0; rewrite <- S1 in H3; clear S1.
 destruct H.
 exists (\rho, t0).
 apply WN_abs; auto.
 subst t; rename t0 into t.
 rewrite <- (sub_sub_swap0 t k).
 replace (\ rho, sub_swap0 (sub t k) k) with (\!k:rho, (sub t k)); auto.
 constructor 2 with taus; auto.
 simp; omega.
 red; intros.
 apply WN_occurs with r; auto.
 rewrite (S_pred n 0); try omega.
 replace (occurs (S (pred n)) r) with (occurs (pred n) (\rho,r)); auto.
  apply F_occurs with rhos (rho-->sigma); split; auto; omega.

 destruct (@exists_last _ (t0::l)) as [l' (t',Htl)]; try discriminate.
 rewrite Htl in H1; rewrite Htl in H0; rewrite Htl in IHWN; clear Htl t0 l.
 simpl in H1; rewrite <- apps_app in H1; simpl in H1.
 injection H1; clear H1; intros.
 subst t'.
 destruct (IHWN ((sub r s);;l') s0 k rho0 sigma taus rhos); auto.
  rewrite <- apps_app; auto.
  subst r0.
  destruct H; red; intuition.
  elim H; intros.
  assert (CorTyp rhos ((\rho,r);s)).
   eapply CorTyp_apps;eauto.
  inversion H5; subst.
  inversion H8; subst.
  simpl in H11; injection H11; clear H1; intros.
  apply TypJ_apps with ((\ rho, r); s) sigma0; auto.
  replace rhos with (nil++rhos); auto.
  apply TypJ_sub1 with (rho::nil); auto.
  intros.
  simpl in H7.
  inversion H7; auto.
  inversion H13.
 exists t0; auto.
 subst.
 change (((\ rho, r); s);; l') with ((\rho,r);;(s::l')); auto.
 Qed.

 Inductive A (rhos:context): type -> term -> term -> Prop := 
 | AVar : forall rho k, TypJ rhos [k] rho -> A rhos rho [k] [k]
 | AApp : forall rho sigma r s r' s', 
   A rhos (rho-->sigma) r s -> 
   TypJ rhos r' rho -> N rhos rho r' s' -> A rhos sigma (r;r') (s;s').
 Hint Constructors A. 

 Inductive H' : term -> term -> Prop := 
  | H'_intro : forall rho r s l, H' ((\rho,r;s);;l) ((sub r s);;l).
 Hint Constructors H'. 

 Definition H (rhos:context)(rho:type)(r s:term) := H' r s.
 Hint Unfold H.

 Inductive Abis (rhos:context) : type -> term -> term -> Prop := 
  | Abis_intros : forall n l l' l'' sigmas sigma, 
     WNs l l' -> EtaExps rhos sigmas l' l'' -> 
     TypJ rhos [n] (sigmas--->sigma) ->
     Abis rhos sigma ([n];;l) ([n];;l'').

 Lemma A_Abis : forall rhos rho r s, 
  A rhos rho r s -> Abis rhos rho r s.
 Proof.
 induction 1.
 apply (@Abis_intros rhos k nil nil nil nil); intuition.
 inversion IHA; subst.
 change (Abis rhos sigma ((n;; l);; (r'::nil)) ((n;; l'');; (s'::nil))).
 do 2 rewrite apps_app.
 inversion H2;subst.
 apply (@Abis_intros rhos n (l++r'::nil) (l'++t::nil) (l''++s'::nil) (sigmas++rho::nil)).
 apply WNs_app; auto.
 apply EtaExps_app; auto.
 rewrite arrows_app; simpl; auto.
 Qed.

 Lemma Ax2 : forall rhos r s, A rhos Iota r s -> N rhos Iota r s.
 Proof.
 intros.
 assert (H1:=A_Abis H0).
 inversion H1; subst.
 exists (n;;l'); eauto.
 Qed.
 
 Lemma Ax3 : forall rhos rho k, TypJ rhos [k] rho -> A rhos rho [k] [k].
 Proof.
 auto. 
 Qed.

 Lemma Ax4 : forall rhos rho sigma r r' s s', 
  TypJ rhos s rho -> 
  A rhos (rho-->sigma) r r' -> N rhos rho s s' -> A rhos sigma (r;s) (r';s').
 Proof.
 eauto. 
 Qed.

 Lemma Ax5 : 
   forall rhos rho r s t, H rhos rho r s -> N rhos rho s t -> N rhos rho r t.
 Proof.
 unfold H.
 destruct 1.
 destruct 1.
 exists t0; auto.
 generalize (WN_beta rho0 r s l H0); simpl; auto.
 Qed. 

 Lemma Ax6 : forall rhos rho sigma r s rs, 
  H rhos sigma ((sub (\rho,r) rs);s) (sub r ((s::rs)#(rs.(shift)))).
 Proof.
 intros; red; simpl.
 rewrite <- Sub_Sub_Ad_Hoc. 
 exact (H'_intro rho _ _ nil).
 Qed. 

 Lemma Ax7 : forall rhos rho sigma r s t, 
  H rhos (rho-->sigma) r s -> H rhos sigma (r;t) (s;t).
 Proof. 
 destruct 1; red.
 generalize (H'_intro rho0 r s (l++t::nil)).
 do 2 rewrite <- apps_app; auto.
 Qed. 

 Lemma Ax_H_ext_ctx :  forall rhos sigmas rho r s, TypJ rhos r rho -> 
  H rhos rho r s -> H (rhos++sigmas) rho r s.
 Proof. 
 auto.
 Qed.

(* begin hide *)
End Rename.
Import Rename.

Definition abstr := abstr.
Definition N:=N.
Definition A:=A.
Definition H:=H.

Definition Ax1:=Ax1.
Definition Ax2:=Ax2.
Definition Ax3:=Ax3.
Definition Ax4:=Ax4.
Definition Ax5:=Ax5.
Definition Ax6:=Ax6.
Definition Ax7:=Ax7.
Definition Ax_H_ext_ctx := Ax_H_ext_ctx.
(* end hide *)

End RequirementsProofEtaExp.

Module CompleteEtaExpProof := 
 NormalizationProof(RequirementsProofEtaExp).

Require Export TaitCoreNc.

Module CompleteEtaExpProofNc := 
 NormalizationProofNc(RequirementsProofEtaExp).
