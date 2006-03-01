Require Import Arith. 

(** misc tactics *)

Ltac __ := idtac.

Ltac rewrite_all Eq := match type of Eq with 
  ?a = ?b => 
     generalize Eq; clear Eq; 
     match goal with 
    | H : context [a] |- _ => intro Eq; try rewrite Eq in H; rewrite_all Eq
    | _ => intro Eq; try rewrite Eq
    end
 end. 

Ltac rewrite_all_rev Eq := match type of Eq with 
  ?a = ?b => 
     generalize Eq; clear Eq; 
     match goal with 
    | H : context [b] |- _ => intro Eq; try rewrite Eq in H; rewrite_all_rev Eq
    | _ => intro Eq; try rewrite Eq
    end
 end. 

Ltac break_dec dec := 
  let parse g :=  
    match g with context [dec ?a ? b] => destruct (dec a b) end
  in 
  match goal with 
  |         |- ?g => parse g
  | _:?g |-  _  => parse g
  end.

Ltac break := try break_dec eq_nat_dec; try break_dec le_lt_dec.

Ltac f_equal := 
  let c := try congruence in 
  let r := try reflexivity in 
  match goal with 
   | |- ?f ?a = ?f' ?a' => cut (a=a'); [c; r|r]
   | |- ?f ?a ?b = ?f' ?a' ?b' => 
      cut (b=b');[cut (a=a');[c; r|r]|r]
   | |- ?f ?a ?b ?c = ?f' ?a' ?b' ?c'=> 
      cut (c=c');[cut (b=b');[cut (a=a');[c; r|r]|r]|r]
   | |- ?f ?a ?b ?c ?d= ?f' ?a' ?b' ?c' ?d'=> 
      cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[c; r|r]|r]|r]|r]
  | |- ?f ?a ?b ?c ?d ?e= ?f' ?a' ?b' ?c' ?d' ?e'=> 
      cut (e=e');[cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[c; r|r]|r]|r]|r]|r]
   | _ => idtac
  end.

Ltac tomega := f_equal; omega.
Ltac impossible := intros; elimtype False; omega.
Ltac imp_or_inv := try impossible; try tomega. 

Ltac dcase x := generalize (refl_equal x); pattern x at -1; case x.

Ltac anon n e := set (n := e) in *; assert (n=e); auto; clearbody n.
Ltac do_in H tac := generalize H; try clear H; tac; try intro H.

Ltac rewriteconv e := 
 let tmp := fresh in (generalize e; simpl; intro tmp; rewrite tmp; clear tmp).
Ltac rewriteconv' e := 
 let tmp := fresh in (generalize e; simpl; intro tmp; rewrite <- tmp; clear tmp).

(** The easy part : taking advantage of autorewrite *)

Ltac simpl_arith := autorewrite with arith.
Ltac ssimpl_arith := autorewrite with arith using simpl.

Hint Rewrite 
 plus_0_r (* n + 0 = n *)
 plus_assoc (*  n + (m + p) = n + m + p *)
 minus_plus (* n + m - n = m *)
 mult_0_r (* n * 0 = 0 *)
 mult_1_r (* n * 1 = n *)
 mult_assoc (* n * (m * p) = n * m * p *)
: arith.

Hint Rewrite <- 
 plus_n_Sm (* S (n + m) = n + S m *)
 minus_plus_simpl_l_reverse (* n - m = p + n - (p + m) *)
 minus_n_O (* n = n - 0 *)
 minus_n_n (* 0 = n - n *)
 mult_n_Sm (* n * m + n = n * S m *)
: arith. 

(* NB: I choosed not to add (n-S m) = pred (n-m) *)

Lemma minus_Sn_n : forall n, S n - n = 1. induction n; auto. Qed.
Hint Rewrite minus_Sn_n : arith.



(** The harder and less satisfactory part : computational lt and le *)

Fixpoint lt' (n m:nat) {struct m} : bool := 
 match m with 
  | 0 => false 
  | S m => match n with 
     | 0 => true 
     | S n => lt' n m
  end
 end.   

(* Another attempt: 
Definition pred_opt (n:option nat) : option nat := 
 match n with 
  | Some (S n) => Some n 
  | _ => None
 end.

Fixpoint minus_opt (n:option nat)(m:nat) {struct m} : option nat := 
  match m with 
   | 0 =>  n 
   | S m => minus_opt (pred_opt n) m 
  end.

Definition lt' n m := if (minus_opt (Some n) m) then False else True.
*)

Lemma lt'_lt : forall m n, lt' n m = true -> n < m.
Proof. 
 induction m; intros; try discriminate.
 destruct n; simpl in *; auto with arith.
Qed. 

Lemma lt_lt' : forall m n, lt n m -> lt' n m = true.
Proof. 
 induction m; intros.
 inversion H.
 destruct n; simpl in *; auto with arith.
Qed.

(* we must add the definition rules in the autorewrite base, since 
  simpl can be messy (e.g. for simpl (le n (S n))). :-( *) 

Lemma lt'_def1 : forall n, lt' n 0 = false. auto. Qed.
Lemma lt'_def2 : forall n, lt' 0 (S n) = true. auto. Qed.
Lemma lt'_def3 : forall n m, lt' (S n) (S m) = lt' n m. auto. Qed.
Lemma lt'_n_Sn : forall n, lt' n (S n) = true. induction n; auto. Qed.
Lemma lt'_n_n : forall n, lt' n n = false. induction n; auto. Qed.

Hint Rewrite lt'_def1 lt'_def2 lt'_def3 lt'_n_Sn : arith.

Ltac simpl_isom A B := 
 apply B;  
 simpl_arith; auto; 
 try apply A. 

Ltac simpl_isom_hyp A B H := 
 let tmp := fresh in 
  (generalize (A _ _ H); 
   simpl_arith; 
   intro tmp; 
   auto; 
   try discriminate tmp; 
   clear H; 
   try assert (H := B _ _ tmp); 
   clear tmp).

Ltac simpl_lt := simpl_isom lt_lt' lt'_lt.
Ltac simpl_lt_hyp := simpl_isom_hyp lt_lt' lt'_lt.

Lemma test_lt : forall n m, n+2<m+3 ->  n+5 < m+8.
intros.
simpl_lt.
simpl_lt_hyp H.
auto with arith.
Qed.

Fixpoint le' (n m:nat) {struct n} : bool := 
 match n with 
  | 0 => true 
  | S n => match m with 
     | 0 => false 
     | S m => le' n m
  end
 end.   

Lemma le'_le : forall n m, le' n m = true -> n <= m.
Proof. 
 induction n; intros; auto with arith.
 destruct m; simpl in *; try discriminate; auto with arith.
Qed. 

Lemma le_le' : forall n m, le n m -> le' n m = true.
Proof. 
 induction n; auto.
 destruct m; simpl in *; intros; [inversion H|firstorder].
Qed.

Lemma le'_def1 : forall n, le' 0 n = true.  auto. Qed.
Lemma le'_def2 : forall n, le' (S n) 0 = false. auto. Qed.
Lemma le'_def3 : forall n m, le' (S n) (S m) = le' n m. auto. Qed.
Lemma le'_refl : forall n, le' n n = true.  induction n; auto. Qed.
Lemma le'_n_nk : forall n k, le' n (n+k) = true. induction n; auto. Qed.
Lemma le'_Sn_n : forall n, le' (S n) n = false. induction n; auto. Qed.

Hint Rewrite le'_def1 le'_def2 le'_def3 le'_refl le'_n_nk le'_Sn_n: arith.

Ltac simpl_le := simpl_isom le_le' le'_le.
Ltac simpl_le_hyp := simpl_isom_hyp le_le' le'_le.

Lemma test_le : forall n m, n+2<=m+3 ->  n+5 <= m+8.
intros.
simpl_le.
simpl_le_hyp H.
auto with arith.
Qed.


