(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Export TaitCore.
Require Export Eta. 
Require Export WN. 

Module RequirementsProofEtaRed <: Requirements.
 (* begin hide *)
 Module Rename.
 (* end hide *)
 
 Inductive N (rhos:context)(rho:type)(r s:term) : Prop := 
   N_intro : forall t, WN r t -> eta_red t = s -> N rhos rho r s.
 
 Definition abstr (k:nat)(rho:type)(r:term) := 
  if is_eta_core r k then left_app r else \rho, sub_swap0 r k.

 Notation " \! k : rho , r " := (abstr k rho r) (at level 20, k at level 99).
    
 Lemma Ax1 : forall r s rhos rho sigma k, 
  F rhos (rho-->sigma) r k -> 
  N (rhos++ext_ctx rhos k rho) sigma (r;k) s -> 
  N rhos (rho-->sigma) r (\!k:rho, s).
 Proof.
 intros.
 set (u:=r;k).
 assert (u=r;k).
  auto.
 clearbody u.
 rewrite <- H1 in H0.
 destruct H0.
 generalize H2 H1 H; clear H2 H1 H.
 generalize r s k rho sigma; clear r s k rho sigma.
 induction H0; intros.

 (* destruct l into l++[k]::nil, and idem for l' *) 
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
   inversion H2.
   replace [k] with ([k];;nil) in H; auto.
   assert (H5:=apps_form_unique2 _ _ _ _ H).
   intuition; subst.   
   inversion H3; auto.
   replace [k] with ([k];;nil) in H; auto.
   replace (((\ rho0, r); s);; l0) with ((\ rho0, r);; (s::l0)) in H; auto.
   assert (H5:=apps_form_unique1 _ _ _ _ H).
   intuition; discriminate.
 subst; clear H2.
 exists (n;;l').
 apply WN_var; auto. 
 rewrite <- apps_app; simpl.
 unfold abstr.
 simpl.
 unfold is_eta_core.
 simpl.
 destruct (term_dec [k] [k]); intuition.
 simpl.
 assert (occurs k (eta_red (n;;l'))=false).
  rewrite eta_red_occurs.
  apply WN_occurs with (n;;l); auto.
  eapply F_occurs; eauto.
 rewrite H; auto.
 
 discriminate.

 destruct l. 
 clear IHWN.
 simpl in *.
 injection H1; clear H1; intros.
 subst.
 assert (rho0 = rho).
  destruct H.
  destruct H.
  simpl in H2; injection H2; auto.
 subst.
 assert (S1 : sub1 k = (map Var (k::nil))#0); auto.
 rewrite S1 in H0. 
 destruct (WN_subk H0 (k::nil) 0 r) as [t0 (H2,H3)]; auto.
 rewrite <- S1 in H0; rewrite <- S1 in H2; clear S1.
 exists (\rho, t0).
 apply WN_abs; auto.
 subst t; rename t0 into t.
 rewrite eta_subk.
 unfold abstr; simpl.
 assert (occurs (S k) t = false).
  apply WN_occurs with r; auto.
  replace (occurs (S k) r) with (occurs k (\rho,r)); auto.
  eapply F_occurs; eauto.
 rewrite <- eta_core_sub; try rewrite eta_red_occurs; auto.
 dcase (is_eta_core (eta_red t) 0); intros.
 unfold is_eta_core in H2.
 destruct (eta_red t); simpl in H2; try discriminate.
 simpl.
 destruct (term_dec t0_2 [0]); simpl in H2; try discriminate.
 subst; simpl.
 rewrite (down_sub t0_1 0 [k]); auto.
 replace false with (negb true); auto; apply negb_sym; auto.
 rewrite sub_sub_swap0; auto.
 red; intros; rewrite eta_red_occurs.
 apply WN_occurs with r; auto.
 rewrite (S_pred n 0); try omega.
 change (occurs (pred n) (\rho, r) = false).
 apply F_occurs with rhos (rho-->sigma); split; destruct H; auto; omega. 

 destruct (@exists_last _ (t0::l)) as [l' (t',Htl)]; try discriminate.
 rewrite Htl in H1; rewrite Htl in H0; rewrite Htl in IHWN; clear Htl t0 l.
 simpl in H1; rewrite <- apps_app in H1; simpl in H1.
 injection H1; clear H1; intros.
 subst t'.
 destruct (IHWN ((sub r s);;l') s0 k rho0 sigma); auto.
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
  simpl in H6.
  inversion H6; auto.
  inversion H12.
 exists t0; auto.
 subst.
 change (((\ rho, r); s);; l') with ((\rho,r);;(s::l')); auto.
 Qed.

 Inductive A (rhos:context): type -> term -> term -> Prop := 
 | AVar : forall rho k, A rhos rho [k] [k]
 | AApp : forall rho sigma r s r' s', 
   A rhos (rho-->sigma) r s -> N rhos rho r' s' -> A rhos sigma (r;r') (s;s').
 Hint Constructors A. 

 Inductive H' : term -> term -> Prop := 
  | H'_intro : forall rho r s l, H' ((\rho,r;s);;l) ((sub r s);;l).
 Hint Constructors H'. 

 Definition H (rhos:context)(rho:type)(r s:term) := H' r s.
 Hint Unfold H.

 Lemma A_apps : forall rhos rho r s, A rhos rho r s -> 
   exists n:nat, exists l, exists l', r = n;;l /\ s = n;;(map eta_red  l') /\ 
     WNs l l'.
 Proof.
 induction 1.
 exists k; exists (nil:list term); exists (nil:list term); intuition.
 destruct IHA as [n (l,(l',(H2,(H3,H4))))].
 destruct H1.
 exists n; exists (l++r'::nil); exists (l'++t::nil).
 rewrite map_app; simpl.
 do 2 rewrite <- apps_app.
 subst; intuition.
 Qed. 

 Lemma Ax2_gen : forall rhos r s rho, A rhos rho r s -> N rhos rho r s.
 Proof.
 intros.
 destruct (A_apps _ _ _ _ H0) as [n (l,(l',(H2,(H3,H4))))].
 exists (n;;l').
 subst; constructor; auto.
 subst.
 assert (forall l r, eta_red (r;;l) = (eta_red r);;(map eta_red l)).
 clear H0 H4 l rho n l l'.
 induction l.
 simpl; auto.
 simpl; intros; rewrite IHl; auto.
 rewrite H1; simpl; auto. 
 Qed.

 Lemma Ax2 : forall rhos r s,  A rhos Iota r s -> N rhos Iota r s.
 Proof. 
 intros; apply Ax2_gen; auto.
 Qed.
 
 Lemma Ax3 : forall rhos rho k, TypJ rhos [k] rho -> A rhos rho [k] [k].
 Proof.
 auto. 
 Qed.

 Lemma Ax4 : forall rhos rho sigma r r' s s', TypJ rhos s rho ->
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

End RequirementsProofEtaRed.

Module CompleteEtaRedProof := 
 NormalizationProof(RequirementsProofEtaRed).

Require Export TaitCoreNc.

Module CompleteEtaRedProofNc := 
 NormalizationProofNc(RequirementsProofEtaRed).
