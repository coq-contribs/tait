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


Require Import TaitEtaRed.
Require Import TaitEtaExp.
Extraction NoInline map.

Definition rho := Iota --> Iota.

(** First example is the identity (\rho,O) applied to a free variable.
    it should reduce to this variable. 
    We start by proving that this application is well-typed *)

Lemma Hex : TypJ (rho :: nil) ((\ rho, O); O) rho.
split; auto.
repeat econstructor; simpl; auto.
Defined.


(** More advanced example: Church numerals *)

Definition quad (sigma:type) := (sigma-->sigma)-->(sigma-->sigma).

Fixpoint f_n_x (f:term)(x:term)(n:nat) {struct n} : term := match n with 
  | O => x
  | S n => f; f_n_x f x n
end.

(* [church n sigma] is \lambda f,\lambda x, f^n x with final type (quad sigma) *)

Definition church (n:nat)(sigma:type) := 
  \(sigma-->sigma),\sigma, f_n_x 1 0 n.

(* This is well-typed: *)

Lemma Hchurch: forall sigma n, TypJ nil (church n sigma) (quad sigma).
Proof.
induction n.
unfold church; simpl.
repeat econstructor; simpl; auto.
unfold church in *; simpl.
destruct IHn.
inversion_clear H.
inversion_clear H1.
simpl in H0.
injection H0; clear H0; intros.
repeat econstructor; simpl; auto.
rewrite H0; auto.
Qed.

(* Let's now apply a church numeral to another, getting the power number *)

Definition church_church (n:nat) (m:nat) := 
  App (church n (Iota-->Iota)) (church m Iota).

(* This is still well-typed *)

Lemma Hchurch_church : 
 forall n m, TypJ nil (church_church n m) (quad Iota).
Proof.
intros.
unfold church_church.
destruct (Hchurch (Iota-->Iota) n).
destruct (Hchurch Iota m).
set (N:=church n (Iota-->Iota)) in *; clearbody N.
set (M:=church m Iota) in *; clearbody M.
repeat econstructor; simpl; eauto.
rewrite H0; rewrite H2; unfold quad; auto.
rewrite H0; simpl; auto.
Qed.


(** Main extraction test: *)

Import CompleteEtaRedProof.
Definition ex := @normalizeTheorem (rho::nil) rho (\rho,0;0) Hex.
Definition church_power := 
 fun n m => @normalizeTheorem nil (quad Iota) (church_church n m) (Hchurch_church n m).
Extraction "betaetared" normalizeTheorem ex church_power.

Import CompleteEtaRedProofNc.
Definition ex_nc := @normalizeTheorem (rho::nil) rho (\rho,0;0) Hex.
Definition church_power_nc := 
 fun n m => @normalizeTheorem nil (quad Iota) (church_church n m) (Hchurch_church n m).
Extraction "betaetared_nc" normalizeTheorem ex_nc church_power_nc.

Import CompleteEtaExpProof.
Definition ex' := @normalizeTheorem (rho::nil) rho (\rho,0;0) Hex.
Definition church_power' := 
 fun n m => @normalizeTheorem nil (quad Iota) (church_church n m) (Hchurch_church n m).
Extraction "betaetaexp" normalizeTheorem ex' church_power'.

Import CompleteEtaExpProofNc.
Definition ex'_nc := @normalizeTheorem (rho::nil) rho (\rho,0;0) Hex.
Definition church_power'_nc := 
 fun n m => @normalizeTheorem nil (quad Iota) (church_church n m) (Hchurch_church n m).
Extraction "betaetaexp_nc" normalizeTheorem ex'_nc church_power'_nc.

(*
in ocaml : 
normalizeTheorem (Cons (Iota,Nil)) Iota (App ((Abs (Iota,Var O), Var O))) : term);;
*)










