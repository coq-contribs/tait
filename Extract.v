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

Lemma Hex : TypJ (rho :: nil) ((\ rho, O); O) rho.
split; auto.
repeat econstructor; simpl; auto.
Defined.

Import CompleteEtaRedProof.
Definition ex := @normalizeTheorem (rho::nil) rho (\rho,0;0) Hex.
Extraction "betaetared" normalizeTheorem ex.

Import CompleteEtaRedProofNc.
Definition ex_nc := @normalizeTheorem (rho::nil) rho (\rho,0;0) Hex.
Extraction "betaetared_nc" normalizeTheorem ex_nc.

Import CompleteEtaExpProof.
Definition ex' := @normalizeTheorem (rho::nil) rho (\rho,0;0) Hex.
Extraction "betaetaexp" normalizeTheorem ex'.

Import CompleteEtaExpProofNc.
Definition ex'_nc := @normalizeTheorem (rho::nil) rho (\rho,0;0) Hex.
Extraction "betaetaexp_nc" normalizeTheorem ex'_nc.

(*
in ocaml : 
normalizeTheorem (Cons (Iota,Nil)) Iota (App ((Abs (Iota,Var O), Var O))) : term);;
*)
