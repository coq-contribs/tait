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


Require Export Subst2. 

(** Lists for coding typing contexts. First comes the type of [Var 0] *)

Definition context := list type.

(** *** Typing judgment. *)

(** An unsafe typing function : *) 

Fixpoint typ (rhos: context)(r:term) {struct r} : type := 
  match r with 
   | [n] => nth n rhos dtype
   | r;s => arrow_right (typ rhos r)
   | \rho,r => rho --> typ (rho::rhos) r
  end.

(** A predicate checking whether the output of the previous typ is ok *)

Inductive CorTyp : context -> term -> Prop := 
  | CorVar : forall rhos n, n < length rhos -> CorTyp rhos [n]
  | CorApp : 
      forall rhos r s, CorTyp rhos r -> CorTyp rhos s -> 
        forall sigma, typ rhos r = ((typ rhos s) --> sigma) ->
           CorTyp rhos (r;s) 
  | CorAbs : forall rhos rho r, 
      CorTyp (rho::rhos) r -> CorTyp rhos (\rho,r).
Hint Constructors CorTyp.

Definition TypJ (rhos:context)(r:term)(rho:type) := 
  (CorTyp rhos r) /\ (typ rhos r = rho).

Hint Unfold TypJ.

(** Facts about TypJ *)

Lemma TypJ_Abs : forall rhos rho sigma mu r, 
  sigma = rho --> mu -> 
  TypJ (rho::rhos) r mu -> TypJ rhos (\rho,r) sigma.
Proof.
destruct 2; split; simpl; auto; congruence.
Qed.

Lemma TypJ_App : forall rhos rho sigma r s, 
 TypJ rhos r (rho-->sigma) -> TypJ rhos s rho -> TypJ rhos (r;s) sigma.
Proof.
do 2 destruct 1; split.
apply CorApp with sigma; auto; congruence.
simpl; rewrite H0; auto.
Qed.

Lemma TypJ_App_inv1 : forall rhos rho sigma r s, 
 TypJ rhos (r;s) rho -> sigma = typ rhos s ->
 TypJ rhos r (sigma-->rho).
Proof.
destruct 1; split; inversion_clear H; auto.
simpl in H0; rewrite H4 in H0; simpl in H0; congruence.
Qed.

Lemma TypJ_App_inv2 : forall rhos rho sigma r s, 
 TypJ rhos (r;s) rho -> sigma = typ rhos s -> TypJ rhos s sigma.
Proof.
destruct 1; split; inversion_clear H; auto.
Qed.
Hint Resolve TypJ_App TypJ_App_inv1 TypJ_App_inv2.

Lemma TypJ_ext_ctx : forall r rhos sigmas rho, 
  TypJ rhos r rho -> TypJ (rhos++sigmas) r rho.
Proof.
induction r; simpl; auto.
destruct 1; simpl in *; split.
inversion_clear H.
constructor; rewrite app_length; omega.
simpl; rewrite app_nth1; auto.
inversion_clear H; auto.

intros; elim H; intros.
inversion_clear H0.
simpl in H1.
rewrite H4 in H1; simpl in H1; subst.
elim (IHr2 rhos sigmas (typ rhos r2)); intros.
apply TypJ_App with (typ (rhos++sigmas) r2).
rewrite H1.
rewrite <- H4.
apply IHr1; split; auto.
rewrite H1.
apply IHr2; split; auto.
split; auto.

destruct 1; simpl in *; intros.
inversion_clear H.
elim (IHr (t::rhos) sigmas (typ (t::rhos) r)); [intros|split; auto].
split; auto.
simpl; subst; simpl in H2; rewrite H2; auto.
Qed.
Hint Resolve TypJ_ext_ctx.

Lemma TypJ_red_ctx : forall r rhos sigmas rho, 
  above (length rhos) r ->  
  TypJ (rhos++sigmas) r rho -> TypJ rhos r rho.
Proof.
induction r; unfold above; simpl; intros.
destruct (le_lt_dec (length rhos) n).
 generalize (H n l).
 destruct (eq_nat_dec n n); intuition; try discriminate.
destruct H0; simpl in *.
split; simpl; auto.
rewrite app_nth1 in H1; auto.

apply TypJ_App with (typ (rhos++sigmas) r2).
apply IHr1 with sigmas; eauto.
red; intros; destruct (orb_false_elim _ _ (H n H1)); auto.
apply IHr2 with sigmas; eauto.
red; intros; destruct (orb_false_elim _ _ (H n H1)); auto.

apply TypJ_Abs with (typ (t::rhos++sigmas) r).
inversion H0; auto.
apply IHr with sigmas; eauto.
red; simpl; intros; rewrite (S_pred n) with 0; intuition.
inversion H0; split; auto.
simpl; inversion H1; auto.
Qed.

Lemma TypJ_up : forall r sigmas rhos rho sigma k, 
  length sigmas = k -> 
  TypJ (sigmas++rhos) r rho -> 
  TypJ (sigmas++sigma::rhos) (up k r) rho.
Proof. 
induction r; simpl; intros.
destruct H0; inversion_clear H0; simpl in *.
generalize H2; simpl_list; clear H2; intros.
rewrite H in H2.
simp.
split.
constructor.
simpl_list; simpl; omega.
simpl.
rewrite app_nth2.
rewrite H.
replace (S n - k) with (S (n-k)); try omega.
simpl.
rewrite app_nth2 in H1.
rewrite H in H1; auto.
omega.
omega.
rewrite app_nth1 in H1; auto; try omega.
apply TypJ_ext_ctx.
split.
constructor; auto.
omega.
simpl; auto.

eapply TypJ_App; eauto.

rename t into mu.
destruct H0; inversion_clear H0; simpl in *.
assert (TypJ ((mu::sigmas)++sigma::rhos) (up (S k) r) (typ (mu :: sigmas ++ rhos) r) ).
apply IHr; simpl; auto with arith.
destruct H0.
split; auto.
simpl in *; rewrite H3; auto.
Qed.

(** Extension of context up to variable k *)

Definition ext_ctx (rhos:context)(k:nat)(rho:type) := 
 consn (S k - length rhos) rho nil.

Lemma ext_ctx_length : forall rhos k rho, length rhos <= k -> 
 length (rhos ++ ext_ctx rhos k rho) = S k.
Proof.
intros.
unfold ext_ctx.
simpl_list.
simpl length.
omega.
Qed.

Lemma ext_ctx_TypJ : forall rhos k rho, length rhos <= k -> 
 TypJ (rhos ++ ext_ctx rhos k rho) k rho.
Proof.
intros; split; auto.
constructor.
rewrite ext_ctx_length; auto with arith.
simpl.
unfold ext_ctx.
rewrite app_nth2; auto.
apply consn_nth1.
omega.
Qed.

Lemma ext_ctx_last : forall rhos k rho, length rhos <= k -> 
  last (ext_ctx rhos k rho) dtype = rho.
Proof.
intros.
unfold ext_ctx.
set (S k - length rhos). 
assert (0 < n).
 unfold n; omega.
clearbody n; clear H.
induction n.
inversion H0.
inversion H0.
simpl; auto.
simpl; fold (consn n rho nil); rewrite IHn; auto.
destruct (consn n rho nil); auto.
Qed.

(** Typing substitutions. *)

Lemma TypJ_sub1 : forall r rhos sigmas mus rho (rs:substitution), 
  length rhos = length rs -> 
  length mus = rs.(shift) -> 
 TypJ (rhos++sigmas) r rho ->  
  (forall n d d', n<length rhos ->  
   TypJ (mus++sigmas) (nth n rs d) (nth n rhos d')) ->  
 TypJ (mus++sigmas) (sub r rs) rho. 
Proof. 
induction r.

intros; simpl.
destruct H1. 
inversion_clear H1.
generalize H4; simpl_list; clear H4; intros.
rewrite H in H4.
destruct (le_lt_dec (length rs) n).
rewrite nth_overflow; auto.
simpl in H3.
rewrite app_nth2 in H3; try omega.
split.
constructor; simpl_list; omega.
simpl.
rewrite app_nth2; auto; try omega.
rewrite H0; simpl_arith.
rewrite H in H3.
replace (n - length rs + shift rs - shift rs) with (n - length rs); auto; try omega.
simpl in H3.
rewrite app_nth1 in H3; try omega.
rewrite H in H2.
subst.
apply H2; auto.

intros.
simpl. 
eapply TypJ_App; eauto.

intros.
rename t into sigma.
simpl.
destruct H1.
inversion_clear H1.
simpl in H3.
set (mu := typ (sigma :: rhos ++ sigmas) r) in *.
assert (TypJ ((sigma::mus)++sigmas) (sub r (sublift rs)) mu).
apply (IHr (sigma::rhos) sigmas (sigma::mus)); auto.
simpl; simpl_list; simpl; congruence.
simpl; simpl_list; simpl; congruence.
intros.
destruct n.
simpl. 
split; auto.
constructor; simpl; auto with arith.
simpl in H1; simpl.
rewrite nth_indep with (d':=up 0 d); simp; try omega.
replace (sigma :: mus ++ sigmas) with (nil ++ (sigma :: mus ++ sigmas)); auto.
apply TypJ_up; simpl; auto with arith.
eapply TypJ_Abs; eauto.
Qed.

(* Not used elsewhere (yet?), but quite nice to have ... *)

Lemma SubRed : forall rhos rho sigma r s, 
 TypJ rhos ((\sigma,r);s) rho ->
 TypJ rhos (sub r s) rho.
Proof.
intros.
destruct H.
simpl in H0.
inversion_clear H.
inversion_clear H1.
simpl in *. 
injection H3; clear H3; intros.
replace rhos with (nil++rhos); auto.
apply TypJ_sub1 with (sigma::nil); auto.
intros.
simpl in H4.
assert (n=0); try omega.
subst n.
simpl.
auto.
Qed.

Lemma TypJ_sub2 : forall r sigmas rhos rho (rs:substitution),
 length rhos <= length rs -> 
 TypJ rhos r rho -> 
 (forall n d d', n<length rhos ->  
   TypJ sigmas (nth n rs d) (nth n rhos d')) ->  
 TypJ sigmas (sub r rs) rho. 
Proof. 
induction r.

intros; simpl.
destruct H0. 
inversion_clear H0.
simpl in H2.
subst.
apply H1; auto.

intros.
simpl. 
eapply TypJ_App; eauto.

intros.
rename t into sigma.
simpl.
destruct H0.
inversion_clear H0.
simpl in H2.
set (mu := typ (sigma::rhos) r) in *.
assert (TypJ (sigma::sigmas) (sub r (sublift rs)) mu).
apply (IHr (sigma::sigmas) (sigma::rhos)); auto.
simpl; simpl_list; simpl; auto with arith.
intros; destruct n.
simpl. 
split; auto.
constructor; simpl; auto with arith.
simpl in H0; simpl.
rewrite nth_indep with (d':=up 0 d); simp; try omega.
replace (sigma :: sigmas) with (nil ++ (sigma :: sigmas)); auto.
apply TypJ_up; simpl; auto with arith.
eapply TypJ_Abs; eauto.
Qed.
