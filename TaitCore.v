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


Require Export Typing. 

Set Implicit Arguments.

(* Redefinition of pairs on [Type] instead of [Set] *)

Inductive prod (A B:Type) : Type :=
    pair : A -> B -> prod A B.
Notation "x * y" := (prod x y) : type_scope.

Definition fst (A B:Type)(ab:prod A B) := let (a,_) := ab in a.
Definition snd (A B:Type)(ab:prod A B) := let (_,b) := ab in b.

Inductive halfprod (A:Prop)(B:Type) : Type := 
   halfpair : A -> B -> halfprod A B. 
Notation "x ** y" := (halfprod x y) (at level 40) : type_scope.

Definition F (rhos:context)(rho:type)(r:term)(k:nat) := 
  TypJ rhos r rho /\ length rhos <= k.

Hint Unfold F.

Lemma F_occurs : forall r rhos rho k, 
  F rhos rho r k -> occurs k r = false.
Proof.
  induction r; destruct 1; simpl; intros.
  case (eq_nat_dec n k); auto.
  intros; subst.
  destruct H; inversion_clear H.
  cut False; try contradiction.
  omega. 

  rewrite (IHr1 rhos (typ rhos r2 --> rho)); [simpl|red; intuition eauto].
  apply (IHr2 rhos (typ rhos r2)); red; intuition eauto.
 
  rename rho into sigma; rename t into rho.
  destruct H; simpl in *. 
  inversion_clear H.
  apply (IHr (rho::rhos) (typ (rho::rhos) r) (S k)); red; intuition eauto.
  simpl; auto with arith.
Qed.  


Module Type Requirements.

 Parameter abstr : nat -> type -> term -> term. 
 Notation " \! k : rho , r " := (abstr k rho r) (at level 20, k at level 99).

 Parameter N : context -> type -> term -> term -> Prop.
 Parameter A : context -> type -> term -> term -> Prop.
 Parameter H : context -> type -> term -> term -> Prop.

 Axiom Ax1 : forall r t rhos rho sigma k, F rhos (rho-->sigma) r k -> 
  N (rhos++ext_ctx rhos k rho) sigma (r;k) t -> 
  N rhos (rho-->sigma) r (\!k:rho, t).

 Axiom Ax2 : forall rhos r s,  A rhos Iota r s -> N rhos Iota r s.

 Axiom Ax3 : forall rhos rho k, TypJ rhos [k] rho ->  A rhos rho [k] [k].

 Axiom Ax4 : forall rhos rho sigma r r' s s', TypJ rhos s rho -> 
  A rhos (rho-->sigma) r r' -> N rhos rho s s' -> A rhos sigma (r;s) (r';s').

 Axiom Ax5 : forall rhos rho r s t, 
  H rhos rho r s -> N rhos rho s t -> N rhos rho r t.

 Axiom Ax6 : forall rhos rho sigma r s rs, 
  H rhos sigma ((sub (\rho,r) rs);s) 
  (sub r ((s::rs)#rs.(shift))).

 Axiom Ax7 : forall rhos rho sigma r s t, 
  H rhos (rho-->sigma) r s -> H rhos sigma (r;t) (s;t).

 Axiom Ax_H_ext_ctx :  forall rhos sigmas rho r s, TypJ rhos r rho -> 
  H rhos rho r s -> H (rhos++sigmas) rho r s.

End Requirements.

Module NormalizationProof (R:Requirements).

Import R.

Definition SN (rhos:context)(rho:type)(r:term) := 
  forall k sigmas, F (rhos++sigmas) rho r k -> 
    { s:term | N (rhos++sigmas) rho r s }. 

Definition SA (rhos:context)(rho:type)(r:term) := 
 forall k sigmas, F (rhos++sigmas) rho r k -> 
    { s:term | A (rhos++sigmas) rho r s }. 

Open Scope type_scope.

Fixpoint SC (rhos:context)(rho:type)(r:term) {struct rho} : Type := 
  (TypJ rhos r rho) **
  match rho with 
  | Iota => SN rhos Iota r
  | rho-->sigma => 
    forall s sigmas, SC (rhos++sigmas) rho s -> 
      SC (rhos++sigmas) sigma (r;s)
  end.

Lemma SN_ext_ctx : forall rho rhos sigmas r, 
 TypJ rhos r rho -> SN rhos rho r -> SN (rhos++sigmas) rho r.
Proof.
unfold SN; intros.
rewrite app_ass in H2; rewrite app_ass. 
apply (H1 k _ H2); auto.
Qed.
Hint Resolve SN_ext_ctx.

Lemma SC_TypJ : forall rhos rho r, SC rhos rho r -> TypJ rhos r rho.
Proof.
 destruct rho; destruct 1; auto.
Qed. 
Hint Resolve SC_TypJ.

Lemma SC_ext_ctx : forall rho rhos sigmas r, 
 SC rhos rho r -> SC (rhos++sigmas) rho r.
Proof.
destruct rho; simpl; intuition.
destruct a; auto.
rewrite app_ass; rewrite app_ass in X; auto.
Qed.

Lemma one :  
 forall rho rhos r, TypJ rhos r rho -> 
 (SC rhos rho r -> SN rhos rho r)*(SA rhos rho r -> SC rhos rho r).
Proof.
induction rho.
simpl.
split.
intuition.
unfold SA, SN.
intros.
split; auto.
intros.
destruct (H1 k _ H2) as [s Hs].
exists s.
apply Ax2; auto.

rename rho1 into rho.
rename rho2 into sigma.
split.
rename H0 into T.
simpl.
unfold SN.
destruct 1 as [_ X].
intros k mus; intros.
set (rhos':=rhos++mus).
set (sigmas := ext_ctx rhos' k rho).
assert (T' : TypJ (rhos'++sigmas) k rho).
 unfold sigmas; apply ext_ctx_TypJ; destruct H0; auto.
assert (SA (rhos'++sigmas) rho [k]). 
 red; intros.
 exists [k].
 apply Ax3.
 destruct H1; auto.
assert (SC (rhos'++sigmas) sigma (r;k)).  
 unfold rhos' in *.
 assert (Eq:=app_ass rhos mus sigmas); rewrite_all Eq; clear Eq.
 apply X.
 refine (snd (IHrho1 (rhos++mus++sigmas) [k] _) _); auto.
assert (SN (rhos'++sigmas) sigma (r;k)).
 refine (fst (IHrho2 (rhos'++sigmas) (r;k) _) _); eauto.
try rename X2 into H2.
destruct (H2 (S k) nil) as [t Ht]; auto.
 simpl_list.
 split; auto.
 unfold sigmas; rewrite ext_ctx_length; auto.
 unfold F in *; intuition.
exists (\!k:rho,t); auto.
do_in Ht simpl_list.
apply Ax1; auto.

unfold SA; simpl; split; auto; intros.
rename H0 into T.
refine (snd (IHrho2 (rhos++sigmas) (r;s) _) _); eauto.
red; intros.
destruct (H1 k (sigmas++sigmas0)) as [r' Hr'].
 rewrite <- app_ass.
 split; auto.
 unfold F in *; intuition.
rewrite <- app_ass in Hr'.
assert (IH: SN (rhos++sigmas) rho s).
 refine (fst (IHrho1 (rhos++sigmas) s _) _); eauto.
destruct (IH k sigmas0) as [s' Hs']; auto.
 unfold F in *; intuition.
exists (r';s').
eapply Ax4; eauto.
Defined.

Lemma two : forall rho rhos r r', TypJ rhos r rho -> 
  SC rhos rho r' -> H rhos rho r r' -> SC rhos rho r.
Proof.
induction rho; simpl; unfold SN; split; auto; intros.
try rename X into H1.
destruct H1 as [T H4].
destruct (H4 k sigmas) as [s Hs]; auto.
unfold F in *; intuition.
exists s.
eapply Ax5; eauto.
apply Ax_H_ext_ctx; auto.
apply IHrho2 with (r':= r';s); intuition.
eauto.
eapply Ax7; eapply Ax_H_ext_ctx; eauto.
Defined.

Fixpoint SCs (sigmas rhos: context)(rs: list term) {struct rhos} : Type := 
 match rhos, rs with 
 | nil,nil => True
 | nil, _ => False
 | _, nil => False 
 | rho::rhos, r::rs => (SC sigmas rho r)*(SCs sigmas rhos rs)
end.

Lemma SCs_length : forall sigmas rhos rs, SCs sigmas rhos rs -> 
 length rhos = length rs.
Proof.
induction rhos; destruct rs; auto; simpl; destruct 1; firstorder.
Qed.
 
Lemma SCs_nth : forall sigmas rhos rho rs r n, n < length rhos ->
  SCs sigmas rhos rs -> SC sigmas (nth n rhos rho)  (nth n rs r). 
Proof.
induction rhos; destruct rs.
intros.
elimtype False.
inversion H0.
contradiction.
contradiction.
intros.
simpl in X; destruct X.
destruct n.
simpl.
auto.
simpl.
firstorder.
Defined.

Lemma SCs_ext_ctx : forall sigmas sigmas0 rhos rs, 
 SCs sigmas rhos rs -> SCs (sigmas++sigmas0) rhos rs.
Proof.
induction rhos; destruct rs; simpl; intuition.
apply SC_ext_ctx; auto.
Qed.

Lemma three : forall r (rs:substitution) rhos sigmas rho, 
 SCs sigmas rhos rs -> 
 TypJ rhos r rho ->  SC sigmas rho (sub r rs).
Proof.
induction r.
simpl.
intros.
destruct H0.
simpl in H1.
subst rho.
apply SCs_nth; auto.
inversion_clear H0; auto.

simpl.
intros.
set (sigma := typ rhos r2).
assert (H1: TypJ rhos r1 (sigma-->rho)). eauto.
assert (H2: TypJ rhos r2 (typ rhos r2)). eauto.
assert (IH1:= IHr1 rs rhos sigmas (sigma --> rho) X H1).
assert (IH2:= IHr2 rs rhos sigmas (typ rhos r2) X H2). 
simpl in IH1.
destruct IH1 as [_ B].
replace sigmas with (sigmas++nil); [idtac|simpl_list;auto].
apply (B (sub r2 rs) nil); simpl_list; auto.

rename t into rho.
intros.
destruct H0.
subst rho0.
set (freeze:= sub (\ rho, r) rs).
assert (TypJ sigmas (sub (\ rho, r) rs) (rho --> typ (rho::rhos) r)).
 apply TypJ_sub2 with rhos.
 rewrite (SCs_length _ _ _ X); auto with arith.
 split; auto.
 intros.
 lapply (@SCs_nth sigmas rhos d' rs d n); auto.
simpl; split; auto; intros.
destruct (@one rho (sigmas ++ sigmas0) s); auto.
apply two with (sub r ((s::rs)#(rs.(shift)))); eauto.
apply IHr with (rhos:=rho::rhos).
simpl.
split; auto.
apply SCs_ext_ctx; auto.
inversion_clear H0; split; auto.
unfold freeze.
apply Ax6; auto.
Qed.

Lemma SCs_seq : forall rhos sigmas, 
  SCs (sigmas++rhos) rhos
   (map Var (seq (length sigmas) (length rhos))). 
Proof.
induction rhos.
simpl; auto.
simpl.
split.
destruct (@one a (sigmas++a::rhos) (length sigmas)).
split.
constructor.
simpl_list; simpl; omega.
simpl; simpl_list; auto.
rewrite app_nth2; auto.
simpl_arith; simpl; auto.
apply s0.
unfold SA.
exists [length sigmas].
apply Ax3.
destruct H0; auto.
replace (a::rhos) with ((a::nil) ++ rhos); auto.
rewrite <- app_ass.
replace (S (length sigmas)) with (length (sigmas++a::nil)); auto.
simpl_list; simpl; simpl_arith; auto.
Defined.

Lemma normalizeTheorem : 
 forall rhos rho r, TypJ rhos r rho -> { s:term | N rhos rho r s }. 
Proof.
intros.
destruct (@one rho rhos r); auto.
assert (SC rhos rho r).
rewrite <- (sub_id r (length rhos)).
apply three with rhos; auto.
unfold id; simpl.
generalize (SCs_seq rhos nil); simpl_list; simpl; auto.
generalize (s X (length rhos) nil); simpl_list; intuition.
Defined.

End NormalizationProof.
