Require Export Compare_dec.
Require Export Arith.
Require Export Bool.
Require Export List.
Require Export Omega.
(* Facultative: for beautiful unicode notations.*)
(* Load "misc_notations". *)
Require Export minlog_mode. 
Require Export MoreList.

Ltac simp := repeat (progress (break; simpl_list;simpl_arith;simpl)).

Set Implicit Arguments.

(** The [type] and [term] datatypes *)

Inductive type : Set := 
 | Iota : type
 | Arrow : type -> type -> type.

Notation " rho --> sigma " := (Arrow rho sigma) (at level 20, right associativity).

Inductive term : Set  := 
 | Var : nat -> term 
 | App : term -> term -> term 
 | Abs : type -> term -> term.

Coercion Var : nat >-> term.

Notation " [ n ] " := (Var n).
Notation " r ; s " := (App r s) (at level 20).
Notation " \ rho , r " := (Abs rho r) (at level 20).

(** Operations on [type] and [term] *)

(* an unknown default term (in fact [0]). *)
Lemma dterm : term.
 exact 0.
Qed.

(* an unknown default type (in fact Iota). *)
Lemma dtype : type.
 exact Iota.
Qed.

Definition arrow_left (sigma:type) := 
  match sigma with 
   | Iota => dtype
   | sigma --> _ => sigma
  end. 

Definition arrow_right (sigma:type) := 
  match sigma with 
   | Iota => dtype
   | _--> sigma  => sigma
  end. 

Definition type_dec : forall r s: type, { r = s } + { ~ r = s}. 
Proof.
 decide equality.
Defined.

Definition term_dec : forall r s: term, { r = s} + { ~ r = s}.
Proof.
 decide equality.
 apply eq_nat_dec.
 apply type_dec.
Qed.

Fixpoint occurs (k:nat)(r:term) {struct r} : bool := match r with 
  | [n] => if eq_nat_dec n k then true else false
  | r;s => orb (occurs k r) (occurs k s)
  | \rho,r => occurs (S k) r
 end.

Fixpoint lift (l:nat)(k:nat)(r:term) {struct r}: term := 
  match r with 
   | [n] => if le_lt_dec l n then k+n else n
   | r;s => (lift l k r);(lift l k s)
   | \rho,r => \rho, lift (S l) k r
  end.

Notation " r |\ [ l , k  ] " := (lift l k r) (at level 60, no associativity).

Fixpoint up (l:nat)(r:term) {struct r}: term := 
  match r with 
   | [n] => if le_lt_dec l n then S n else n
   | r;s => (up l r);(up l s)
   | \rho,r => \rho, up (S l) r
  end.

Fixpoint down (l:nat)(r:term) {struct r}: term := 
  match r with 
   | [n] => if le_lt_dec l n then pred n else n
   | r;s => (down l r);(down l s)
   | \rho,r => \rho, down (S l) r 
  end.

Lemma lift_up : forall r l, up l r = lift l 1 r.
Proof. 
 induction r; simpl; intros; auto.
 rewrite IHr1; rewrite IHr2; auto.
 rewrite IHr; auto.
Qed.


Lemma lift_lift : forall r l k k', (r |\ [l,k]) |\ [l,k'] = r |\ [l,k+k'].
Proof.
 induction r; simpl; intros.
 simp; tomega.
 rewrite IHr1; rewrite IHr2; auto.
 rewrite IHr; auto.
 Qed.

Lemma lift_lift2 : forall r m n k, (r|\ [m,n]) |\ [m+n, k] = r |\ [m, n+k].
Proof.
induction r; simpl; intros.
simp; tomega.
rewrite IHr1; rewrite IHr2; auto.
rewrite <- IHr; auto.
Qed.

Lemma lift_lift3 : 
  forall r m n m' n', (r |\ [m,n]) |\ [m+m'+n, n'] = (r |\ [m+m', n']) |\ [m,n].
Proof.
induction r; simpl; intros.
simp; tomega.
rewrite IHr1; rewrite IHr2; auto.
change (S (m+m')) with (S m+m'); rewrite <- IHr; auto.
Qed.

Lemma lift_null : forall r l, lift l 0 r = r.
Proof.
 induction r; simpl; intros.
 simp; auto.
 rewrite IHr1; rewrite IHr2; auto.
 rewrite IHr; auto.
 Qed.

Lemma down_up : forall r l, down l (up l r) = r.
Proof.
 induction r; simpl; intros.
 simp; tomega.
 rewrite IHr1; rewrite IHr2; auto.
 rewrite IHr; auto.
Qed.

Lemma up_down : forall r l, occurs l r = false -> up l (down l r) = r.
Proof.
 induction r; simpl; intros.
 simp; try discriminate; tomega.
 destruct (orb_false_elim _ _ H).
 rewrite IHr1; auto; rewrite IHr2; auto.
 rewrite IHr; auto. 
Qed.

(** Results about [occurs] *)

 Lemma lift_occurs : forall r l n k, n <= k ->  
   occurs (l+k) (lift n l r) = occurs k r.
 Proof.
 induction r; simpl; intros.
 simp; auto; impossible.
 rewrite IHr1; auto; rewrite IHr2; auto.
 replace (S (l+k)) with (l+(S k)); auto with arith.
 Qed. 

 Lemma down_occurs : forall r n k, S n <= k ->  
   occurs k (down n r) = occurs (S k) r.
 Proof.
 induction r; simpl; auto with arith; intros.
 simp; auto; impossible.
 rewrite IHr1; auto; rewrite IHr2; auto.
 Qed. 

 Lemma down_occurs2 : forall r n,  occurs n r = false -> 
   occurs n (down n r) = occurs (S n) r.
 Proof.
 induction r; simpl; auto with arith; intros.
 simp; auto; impossible.
 destruct (orb_false_elim _ _ H).
 rewrite IHr1; auto;rewrite IHr2; auto.
 Qed. 
