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


Require Import List.
Require Import Zmisc.
Require Import Arith.
Require Import Bool.

Set Implicit Arguments.

(* Should be added to the List Standard Library ... *)

Section MoreLists.

Variable A:Set.

Section Nth.

Lemma nth_overflow : forall (l:list A) n d, length l <= n -> nth n l d = d.
Proof.
induction l; destruct n; simpl; intros; auto.
inversion H.
apply IHl; auto with arith.
Qed.

Lemma nth_indep : 
 forall (l:list A) n d d', n < length l -> nth n l d = nth n l d'.
Proof.
induction l; simpl; intros; auto.
inversion H.
destruct n; simpl; auto with arith.
Qed.

End Nth.

Section App.

Lemma app_length : forall l l':list A, length (l++l') = length l + length l'.
Proof.
induction l; simpl; auto.
Qed.

Lemma app_nth1 : 
 forall (l l':list A) d n, n < length l -> nth n (l++l') d = nth n l d.
Proof.
induction l.
intros.
inversion H.
intros l' d n.
case n; simpl; auto.
intros; rewrite IHl; auto with arith.
Qed.

Lemma app_nth2 : 
 forall (l l':list A) d n, n >= length l -> nth n (l++l') d = nth (n-length l) l' d.
Proof.
induction l.
intros.
simpl.
rewrite <- minus_n_O; auto.
intros l' d n.
case n; simpl; auto.
intros.
inversion H.
intros.
rewrite IHl; auto with arith.
Qed.

Lemma fold_left_app : forall (B: Set)(f : A -> B -> A)(l l':list B)(a:A), 
 fold_left f (l++l') a = fold_left f l' (fold_left f l a).
Proof.
induction l. 
simpl; auto.
intros.
simpl.
auto.
Qed.

End App.

Section Rev.

Lemma rev_length : forall l:list A, length (rev l) = length l.
Proof.
induction l;simpl; auto.
rewrite app_length.
rewrite IHl.
simpl; rewrite plus_comm; auto.
Qed.

Lemma rev_nth : forall (l: list A)(d:A)(n:nat),  n < length l ->  
 nth n (rev l) d = nth (length l - S n) l d.
Proof.
induction l.
intros; inversion H.
intros.
simpl in H.
simpl (rev (a :: l)).
simpl (length (a :: l) - S n).
inversion H.
rewrite <- minus_n_n; simpl.
rewrite <- rev_length.
rewrite app_nth2; auto.
rewrite <- minus_n_n; auto.
rewrite app_nth1; auto.
rewrite (minus_plus_simpl_l_reverse (length l) n 1).
replace (1 + length l) with (S (length l)); auto with arith.
rewrite <- minus_Sn_m; auto with arith; simpl.
apply IHl; auto.
rewrite rev_length; auto.
Qed.

End Rev.

Section Rev_acc.

(* finally not used here, but might be useful some day *)

Fixpoint rev_acc (l l': list A) {struct l} : list A := 
 match l with 
  | nil => l' 
  | a::l => rev_acc l (a::l')
 end.

Lemma rev_acc_rev : forall l l', rev_acc l l' = rev l ++ l'.
Proof.
induction l; simpl; auto; intros.
rewrite <- ass_app; firstorder.
Qed.

Lemma rev_rev_acc : forall l, rev l = rev_acc l nil.
Proof.
intros; rewrite rev_acc_rev.
apply app_nil_end.
Qed.

End Rev_acc.

Section Seq. 

Fixpoint seq (start len:nat) {struct len} : list nat := 
 match len with 
  | 0 => nil
  | S len => start :: seq (S start) len
 end. 

Lemma seq_length : forall len start, length (seq start len) = len.
Proof.
induction len; simpl; auto.
Qed.

Lemma seq_nth : forall len start n d, 
  n < len -> nth n (seq start len) d = start+n.
Proof.
induction len; intros.
inversion H.
simpl seq.
destruct n; simpl.
auto with arith.
rewrite IHlen;simpl; auto with arith.
Qed.

Lemma seq_shift : forall len start,
 map S (seq start len) = seq (S start) len.
Proof. 
induction len; simpl; auto.
intros.
rewrite IHlen.
auto with arith.
Qed.

End Seq.

Section Map.

Variable B: Set.
Variable f : A-> B.

Lemma In_map2 : forall l y, In y (map f l) -> exists x, f x = y /\ In x l.
Proof.
induction l; firstorder.
Qed.

Lemma map_length : forall l, length (map f l) = length l.
Proof.
induction l; simpl; auto.
Qed.

Lemma map_nth : forall l d n, 
 nth n (map f l) (f d) = f (nth n l d).
Proof.
induction l; simpl map; destruct n; firstorder.
Qed.

Lemma map_app : forall l l',  
 map f (l++l') = (map f l) ++ (map f l').
Proof. 
induction l; simpl; auto.
intros; rewrite IHl; auto.
Qed.

Lemma map_rev : forall l, map f (rev l) = rev (map f l).
Proof. 
induction l; simpl; auto.
rewrite map_app.
rewrite IHl; auto.
Qed.

Lemma map_map : forall (C:Set)(f:A->B)(g:B->C) l, 
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
induction l; simpl; auto.
rewrite IHl; auto.
Qed.

Lemma map_ext : 
 forall g, (forall a, f a = g a) -> forall l, map f l = map g l.
Proof.
induction l; simpl; auto.
rewrite H; rewrite IHl; auto.
Qed.

End Map.

Section SplitLast. 

Fixpoint last (l:list A)(d:A)  {struct l} : A := 
 match l with 
  | nil => d 
  | a :: nil => a 
  | a :: l => last l d
 end.

Fixpoint removelast (l:list A) {struct l} : list A := 
 match l with 
  | nil =>  nil 
  | a :: nil => nil 
  | a :: l => a :: removelast l
 end.

Lemma app_removelast_last : 
 forall l d, l<>nil -> l = removelast l ++ (last l d :: nil).
Proof.
induction l.
destruct 1; auto.
intros d _.
destruct l; auto.
pattern (a0::l) at 1; rewrite IHl with d; auto; discriminate.
Qed.

Lemma exists_last : 
 forall l, l<>nil -> { l' : list A & { a : A | l = l'++a::nil}}. 
Proof. 
induction l.
destruct 1; auto.
intros _.
destruct l.
exists (@nil A); exists a; auto.
destruct IHl as [l' (a',H)]; try discriminate.
rewrite H.
exists (a::l'); exists a'; auto.
Qed.

End SplitLast.

Section ConsN.

(* [consn n a l] adds [n] times the element [a] in head position of [l]. *)

Definition consn n a (l:list A) := iter_nat n _ (cons a) l.

Lemma consn_length : forall n a l, length (consn n a l) = n + length l.
Proof.
unfold consn; induction n; simpl; auto.
Qed.

Lemma consn_nth1 : 
forall n a l k d,  k < n -> nth k (consn n a l) d = a.
Proof. 
unfold consn; induction n.
inversion 1.
destruct k; simpl; auto with arith.
Qed.

Lemma consn_nth2 : 
forall n a l k d,  n <= k -> nth k (consn n a l) d = nth (k-n) l d.
Proof. 
unfold consn; induction n.
intros; rewrite <- minus_n_O; auto.
destruct k; [ inversion 1 | simpl; auto with arith ].
Qed.

End ConsN.

Section Existsb. 

 Fixpoint existsb (f:A->bool)(l:list A) {struct l}: bool := 
   match l with 
    | nil => false
    | a::l => f a || existsb f l
   end.

 Lemma existsb_nth : forall (f:A->bool)(l:list A) n d, n < length l ->
  existsb f l = false -> f (nth n l d) = false.
 Proof.
 induction l.
 inversion 1.
 simpl; intros.
 destruct (orb_false_elim _ _ H0); clear H0; auto.
 destruct n ; auto. 
 rewrite IHl; auto with arith.
 Qed.

End Existsb.


(* finally unused *)
Fixpoint firstn (n:nat)(l:list A) {struct n} : list A := 
 match n with 
  | 0 => nil 
  | S n => match l with  
       | nil => nil 
       | a::l => a::(firstn n l)
   end
  end.

End MoreLists.

Implicit Arguments consn [A].

Hint Rewrite 
 rev_involutive (* rev (rev l) = l *)
 rev_unit (* rev (l ++ a :: nil) = a :: rev l *)
 map_nth (* nth n (map f l) (f d) = f (nth n l d) *)
 map_length (* length (map f l) = length l *)
 seq_length (* length (seq start len) = len *)
 app_length (* length (l ++ l') = length l + length l' *)
 rev_length (* length (rev l) = length l *)
 consn_length (* length (consn n a l) = n + length l *)
 : list.

Hint Rewrite <- 
 app_nil_end (* l = l ++ nil *)
 : list.
 
Ltac simpl_list := autorewrite with list.
Ltac ssimpl_list := autorewrite with list using simpl.
