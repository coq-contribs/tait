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
