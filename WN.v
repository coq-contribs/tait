Require Export Apps. 
Require Import Subst2.

Set Implicit Arguments.

Inductive WN : term -> term -> Prop := 
 | WN_var : forall n l l', WNs l l' -> WN ([n];;l) ([n];;l')
 | WN_abs : forall rho r s, WN r s -> WN (\rho,r) (\rho,s)
 | WN_beta : forall rho (r s:term) l t, 
     WN ((sub r s);;l) t -> WN ((\rho,r);;(s::l)) t
with 
(* Inductive*) WNs : list term -> list term -> Prop := 
 | WNs_nil : WNs nil nil
 | WNs_cons : forall r s l l', WN r s -> WNs l l' -> WNs (r::l) (s::l').

Hint Constructors WN.
Hint Constructors WNs.

Lemma WNs_app : forall l ll l' ll', WNs l l' -> WNs ll ll' -> 
 WNs (l++ll) (l'++ll').
Proof.
induction l; simpl; intros; inversion_clear H; simpl; auto.
Qed.
Hint Resolve WNs_app.

Lemma WNs_rev : forall l l', 
 WNs l l' -> WNs (rev l) (rev l').
Proof.
induction l; simpl; intros; inversion_clear H; simpl; auto.
Qed.

Lemma WNs_last: forall l l' r r', 
 WNs (l++r::nil) (l'++r'::nil) -> WNs l l' /\ WN r r'.
Proof.
intros.
generalize (WNs_rev H).
simpl_list.
inversion_clear 1.
generalize (WNs_rev H2).
simpl_list; auto.
Qed.

(** Here we define an ad-hoc induction principle (hidden in the doc) *)
(* begin hide *)
Definition WN_WNs_ind := 
fun (P : term -> term -> Prop)
      (Q : list term -> list term -> Prop)
  (f : forall (n : nat) (l l' : list term), WNs l l' -> Q l l' -> P (n;; l) (n;; l'))
  (f0 : forall (rho : type) (r s : term),
        WN r s -> P r s -> P (\ rho, r) (\ rho, s))
  (f1 : forall (rho : type) (r s : term) (l : list term) (t : term),
        WN (sub r s;; l) t ->
        P (sub r s;; l) t -> P ((\ rho, r);; (s :: l)) t) 
  (g0 : Q nil nil) 
  (g1 : forall r r' l l', WN r r' -> P r r' -> WNs l l' -> Q l l' -> Q (r::l) (r'::l'))
  =>
fix F (t t0 : term) (w : WN t t0) {struct w} : P t t0 :=
  match w in (WN t1 t2) return (P t1 t2) with
  | WN_var n l l' w0 => f n l l' w0 (G l l' w0)
  | WN_abs rho r s w0 => f0 rho r s w0 (F r s w0)
  | WN_beta rho r s l t1 w0 => f1 rho r s l t1 w0 (F (sub r s;; l) t1 w0)
  end
with 
 G (l l' : list term) (w: WNs l l') {struct w} : Q l l' := 
   match w in (WNs l0 l0') return (Q l0 l0') with 
   | WNs_nil => g0
   | WNs_cons r r' l l' w ws => g1 r r' l l' w (F r r' w) ws (G l l' ws)
  end
for F.
(* end hide *)

Lemma WN_occurs : 
  forall r r', WN r r' -> forall k, occurs k r = false -> occurs k r' = false.
 Proof.
 intros r r' w. 
 set (P:= fun r r' => forall k, occurs k r = false -> occurs k r' = false).
 change (P r r').
 set (Q:= fun l l' => forall k, (existsb (occurs k) l = false) -> 
                                           (existsb (occurs k) l' = false)).
 apply  WN_WNs_ind with Q; unfold P, Q in *; clear P Q.

 intros.  
 rewrite apps_occurs.
 rewrite apps_occurs in H1.
 destruct (orb_false_elim _ _ H1); clear H1.
 rewrite H0; auto with bool.
 
 intros.
 simpl in *.
 rewrite H0; auto.

 intros.
 simpl in H1.
 rewrite apps_occurs in H1.
 simpl in H1.
 destruct (orb_false_elim _ _ H1); clear H1.
 destruct (orb_false_elim _ _ H2); clear H2.
 apply H0.
 rewrite apps_occurs.
 rewrite H3.
 rewrite (orb_b_false).
 apply sub_occurs; simpl; auto with bool.
 simpl; simpl_arith; auto.

 simpl; auto.

 simpl; intros.
 destruct (orb_false_elim _ _ H3); clear H3.
 rewrite H0; auto.
 rewrite H2; auto.

 auto with bool.
Qed.

  
 Lemma WN_subk : 
   forall r t, WN r t -> 
   forall (lk:list nat) sk r', 
     let rs := (map Var lk)#sk in 
     r = sub r' rs -> exists t',  t = sub t'  rs /\ WN r' t'.
(* begin hide *)
 Proof. 
 intros r t w.
 set (P:= fun r t => forall lk sk r', 
    let rs := (map Var lk)#sk in  r = sub r' rs -> exists t',  t = sub t' rs /\ WN r' t').
 set (Q:= fun l lt => forall lk sk l', 
    let rs := (map Var lk)#sk in l = map (fun r => sub r rs) l' -> 
             exists lt', lt = map (fun r => sub r rs) lt' /\ WNs l' lt').
 change (P r t); apply WN_WNs_ind with Q; auto; unfold P, Q in *; clear r t w P Q.

 intros.
 set (rs := (map Var lk)#sk) in *. 
 rewrite (apps_form r') in H1; rewrite (apps_form r').
 rewrite sub_apps in H1.
 assert (is_app (sub (head_apps r') rs) = false).
  dcase (head_apps r'); unfold sub; simpl; auto.
  intros; simp; auto.
  intros; destruct (head_apps_not_App _ H2).
 assert (sub (head_apps r') rs = [n]).
  eapply apps_form_unique1; eauto.
 assert (l = map (fun r : term => sub r rs) (get_apps r')).
  eapply apps_form_unique2; eauto.
 clear H1.
 set (r0 := head_apps r') in *; set (l0 := get_apps r') in *.
 destruct (H0 lk sk l0 H4) as [lt' (H5,H6)].
 exists (r0;;lt'). 
 rewrite sub_apps.
 rewrite H3.
 unfold rs. 
 rewrite <- H5. 
 split; auto.
 destruct r0; simpl in H3; try discriminate; constructor; auto.

 intros.
 destruct r'; generalize H1; clear H1; simp; try (intro; discriminate).
 injection 1;clear H1; intros; subst t.
 set (lk':=0::(map S lk)).
 assert (sublift (map Var lk # sk) = map Var lk' # S sk).
  unfold lk', sublift; simpl.
  do 2 rewrite map_map; simpl; auto.
 rewrite H2 in H1. 
 destruct (H0 lk' (S sk) r' H1) as [t' (H3,H4)].
 exists (\rho,t'). 
 split.
 simpl; rewrite H2; congruence.
 constructor; auto.

 intros.
 set (rs := (map Var lk)#sk) in *. 
 rewrite (apps_form r') in H1; rewrite (apps_form r').
 rewrite sub_apps in H1.
 assert (is_app (sub (head_apps r') rs) = false).
  dcase (head_apps r'); unfold sub; simpl; auto.
  intros; simp; auto.
  intros; destruct (head_apps_not_App _ H2).
 assert (sub (head_apps r') rs = (\rho,r)).
  eapply apps_form_unique1; eauto.
 assert (s::l = map (fun r : term => sub r rs) (get_apps r')).
  eapply apps_form_unique2; eauto.
 clear H1.
 set (r0 := head_apps r') in *; set (l0 := get_apps r') in *.
 clearbody r0; clearbody l0.
 destruct r0; simpl in H3; try discriminate.
  generalize H3; simp; intro; discriminate.
  injection H3; clear H3; intros.
  subst t0.
 destruct l0 as [|s0 l0]; simpl in H4; try discriminate.
 injection H4; clear H4; intros.
 set (lk':=0::(map S lk)).
 assert (sublift rs = map Var lk' # S sk).
  unfold lk', sublift; simpl.
  do 2 rewrite map_map; simpl; auto.
 rewrite H5 in H1. 
 destruct (H0 lk sk ((sub r0 s0);;l0)) as [t' (H6,H7)].
 rewrite sub_apps.
 fold rs; rewrite <- H3.
 f_equal.
 subst r s.
 rewrite <- H5.
 replace (map Var lk) with (support rs); auto.
 replace sk with rs.(shift); auto.
 rewrite Sub_Sub.
 apply Sub_Sub_Ad_Hoc; auto.
 exists t'; auto.

 intros.
 destruct l'; try discriminate.
 exists (@nil term); simpl; split; auto.  

 intros.
 destruct l'0; try discriminate.
 simpl in H3.
 injection H3; clear H3; intros.
 destruct (H0 lk sk t H4) as [r0' (H5,H6)].
 destruct (H2 lk sk l'0 H3) as [l0' (H7,H8)].
 exists (r0'::l0'); simpl; auto.
 split. 
 congruence.
 constructor; auto.
 Qed.
(* end hide *)
