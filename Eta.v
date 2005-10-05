Require Export Apps.
Require Export Subst2.

Set Implicit Arguments.

(** *** First, the eta reduction *)

Definition is_eta_core (r:term)(k:nat) := 
    is_app r &&
    (if term_dec (right_app r) [k] then true else false) &&
    negb (occurs k (left_app r)).

Fixpoint eta_red (r:term) : term := match r with 
  | [n] => [n]
  | r;s => (eta_red r);(eta_red s)
  | \rho,r => 
     let r':= eta_red r in 
     if is_eta_core r' 0 then down 0 (left_app r') else \rho, r'
 end.  

(** Here we define an ad-hoc induction principle (hidden in the doc) *)
(* begin hide *)
Definition term2_ind : forall P : term -> Prop,
   (forall n, P [n]) ->
   (forall t1 t2, P t1 -> P t2 -> P (t1; t2)) ->
   (forall rho n, P (\ rho, [n])) ->
   (forall rho t1 t2, P t1 -> P t2 -> P (\ rho, (t1;t2))) ->
   (forall rho sigma t, P (\sigma,t) -> P (\ rho, \sigma, t)) ->
       forall t : term, P t :=
  fun P Pv Pp Pav Pap Paa => 
  fix F (t : term) : P t :=
   match t return (P t) with
   | [n] => Pv n
   | t0; t1 => Pp t0 t1 (F t0) (F t1)
   | \rho, t0 => (match t0 return (P t0  -> P (\rho,t0)) with 
         | [n] => fun _ => Pav rho n
         | t1;t2 => fun _ => Pap rho t1 t2 (F t1) (F t2)
         | \sigma, t => fun p => Paa rho sigma t p
       end
     (F t0))
  end.
(* end hide *)

Lemma eta_red_occurs : forall r k, occurs k (eta_red r) = occurs k r.
Proof.
 intro r; pattern r; apply term2_ind; clear r.
 simpl; auto.
 intros t1 t2 IHr1 IHr2 k; simpl; rewrite <- IHr1; rewrite <- IHr2; auto.
 simpl; auto. 

 intros; simpl.
 dcase (is_eta_core (eta_red t1; eta_red t2) 0); simpl; auto; intros.
 unfold is_eta_core in *.
 simpl in H1.
 destruct (term_dec (eta_red t2) [0]); simpl in H1; try discriminate; subst.
 rewrite <- H0.
 rewrite e; simpl.
 rewrite (orb_b_false).
 generalize (negb_sym _ _ (sym_eq H1)); clear H1; intros.
 simpl in H1.
 destruct k.
 rewrite down_occurs2; auto.
 rewrite down_occurs; auto with arith. 

 rewrite H; rewrite H0; auto.

 intros.
 set (t0:=\sigma,t) in *; clearbody t0.
 simpl. 
 dcase (is_eta_core (eta_red t0) 0); intros; simpl; auto.
 unfold is_eta_core in H0.
 destruct (andb_prop _ _ H0); clear H0.
 destruct (andb_prop _ _ H1); clear H1.
 destruct (eta_red t0); try discriminate; simpl in *.
 destruct (term_dec t1_2 0); try discriminate; subst t1_2.
 rewrite <- H; clear H H3 H0. 
 rewrite (orb_b_false).
 generalize (negb_sym _ _ (sym_eq H2)); clear H2; simpl; intros.
 destruct k.
 apply down_occurs2; auto.
 apply down_occurs; auto with arith.
 Qed. 

Lemma eta_core_sub : forall r (k:nat), 
   occurs (S k) r = false -> 
   is_eta_core r 0 = is_eta_core (sub r k) k.
Proof.
 induction r; simpl; intros.
 destruct n; auto.
 destruct n; simpl_arith; auto.

 unfold is_eta_core; simpl.
 destruct (term_dec r2 [0]); simpl.
 rewrite e; simpl.
 destruct (term_dec k k); intuition; simpl.
 f_equal; apply subk_occurs; simpl.
 destruct (orb_false_elim _ _ H); auto. 
 destruct (term_dec (sub r2 k) k).
 destruct n.
 destruct (orb_false_elim _ _ H); clear H.
 destruct r2; try discriminate.
 simpl in e; simpl in H1.
 destruct (eq_nat_dec n (S k)); try discriminate. 
 destruct n; auto.
 destruct n; auto; injection e; intros; subst; tomega.
 simpl; auto. 
 
 unfold is_eta_core; simpl; auto.
 Qed.

Lemma eta_core_sub2 : forall r (l k:nat), 
   is_eta_core r 0 = is_eta_core (sub r ((id (S l) ++ [S k] :: nil) # S l)) 0.
Proof.
 induction r; intros.
 simpl; destruct n; auto.
 replace ([S k]::nil) with (map Var (S k::nil)); auto.
 rewrite <- map_app.
 simp; unfold is_eta_core; auto.

 set (rs:= (id (S l) ++ [S k] :: nil)#S l).
 unfold is_eta_core; simpl.
 destruct (term_dec r2 [0]); simpl.
 rewrite e; simpl.
 destruct (term_dec 0 0); intuition; simpl.
 f_equal; unfold rs. 
 apply (sub_occurs2 r1 (S l) 0); auto with arith.
 destruct (term_dec (sub r2 rs) 0); simpl; auto.
 destruct n.
 generalize e; clear e.
 destruct r2; simpl; try (intros; discriminate).
 unfold rs;simpl.
 destruct n; auto.
 destruct (le_lt_dec l n). 
 rewrite app_nth2; simpl_list; try omega.
 destruct (eq_nat_dec n l).
 subst; simpl_arith; simpl; inversion 1.
 rewrite nth_overflow; simpl_list; simpl_arith; simpl.
 intro H; inversion H.
 omega.
 rewrite app_nth1; simpl_list; try omega.
 rewrite seq_nth; simpl; try omega; inversion 1.

 unfold is_eta_core; simpl; auto.
Qed.

Lemma eta_subk_gen : forall r (l k:nat), 
   eta_red (sub r ((id l ++ [k]::nil)#l)) = sub (eta_red r) ((id l ++[k]::nil)#l).
Proof. 
 induction r; simpl; intros.
 replace ([k]::nil) with (map Var (k::nil)); auto.
 rewrite <- map_app; simpl.
 simp; auto.
 simpl in *.
 rewrite IHr1; rewrite IHr2; auto.
 rewriteconv sublift_id_s; simpl.
 rewriteconv (IHr (S l) (S k)); simpl.

 rewriteconv' eta_core_sub2.
 dcase (is_eta_core (eta_red r) 0); intros.
 unfold is_eta_core in *.
 destruct (eta_red r); try discriminate.
 simpl in *.
 destruct (andb_prop _ _ H); clear H.
 assert (H2:= negb_sym _ _ (sym_eq H1)); simpl in *.
 generalize (down_sub2 t0_1 l k H2).
 unfold sublift; simpl.
 rewrite map_app; simpl.
 rewrite map_up; auto.
 rewrite seq_shift; auto.

 simpl; rewriteconv sublift_id_s; simpl; auto.
Qed.


Lemma eta_subk : forall r (k:nat), 
   eta_red (sub r k) = sub (eta_red r) k.
Proof. 
 exact (fun r => eta_subk_gen r 0).
Qed.

(** *** Secondly, the eta expansion *)

(* Beware: we eta-expanse only terms that are already beta-normal. *)
(* This allow us to skip one case in the EtaExp inductive definition. *)

Notation " \! k : rho , r " := (\rho, sub_swap0 r k) (at level 20, k at level 99).

Inductive Eta : context -> type -> term -> term -> Prop := 
  | Eta_Iota : forall rhos r, Eta rhos Iota r r
  | Eta_Arrow : forall rhos sigmas rho sigma k etak r s, 
      length rhos <= k -> 
      length (rhos++sigmas) = k ->
      Eta (rhos++sigmas++rho::nil) rho [k] etak -> 
      Eta (rhos++sigmas++rho::nil) sigma (r;etak) s -> 
      Eta rhos (rho-->sigma) r (\! k : rho, s).

Inductive EtaExp : context -> type -> term -> term -> Prop := 
  | EtaExp_Var : forall rhos sigmas rs ss k t rho, 
     TypJ rhos [k] (sigmas--->rho) -> 
     EtaExps rhos sigmas rs ss -> 
     Eta rhos rho ([k];;ss) t -> 
     EtaExp rhos rho ([k];;rs) t
  | EtaExp_Abs : forall rhos sigmas rho sigma r s k, 
     length rhos <= k -> 
     length (rhos++sigmas) = k -> 
     EtaExp (rhos++sigmas++rho::nil) sigma r s -> 
     EtaExp rhos (rho--> sigma) (\! k : rho, r) (\! k : rho, s)
with EtaExps: context -> list type -> list term -> list term -> Prop := 
  | EtaExps_nil : forall rhos, EtaExps rhos nil nil nil
  | EtaExps_cons : forall rhos sigma sigmas r s rs ss, 
      EtaExp rhos sigma r s -> EtaExps rhos sigmas rs ss -> 
      EtaExps rhos (sigma::sigmas) (r::rs) (s::ss).

  Hint Constructors Eta. 
  Hint Constructors EtaExp.
  Hint Constructors EtaExps.

Lemma EtaExps_app : forall rhos s1 s2 l1 l2 l1' l2', 
  EtaExps rhos s1 l1 l1' -> EtaExps rhos s2 l2 l2' -> 
  EtaExps rhos (s1++s2) (l1++l2) (l1'++l2').
Proof.
 induction s1; simpl; intros; inversion_clear H; simpl; auto.
Qed.
Hint Resolve EtaExps_app.

Lemma EtaExps_rev : forall rhos s l l', 
  EtaExps rhos s l l' -> EtaExps rhos (rev s) (rev l) (rev l').
Proof.
 induction s; simpl; intros; inversion_clear H; simpl; auto.
Qed.

Lemma EtaExps_last : forall rhos sigmas sigma l r l' r', 
    EtaExps rhos (sigmas++sigma::nil) (l++r::nil) (l'++r'::nil) -> 
    EtaExps rhos sigmas l l'  /\ EtaExp rhos sigma r r'.
Proof.
 intros.
 generalize (EtaExps_rev H).
 simpl_list.
 inversion_clear 1.
 generalize (EtaExps_rev H2).
 simpl_list; auto.
Qed.

(** Here we define an ad-hoc induction principle (hidden in the doc) *)
(* begin hide *)
Definition EtaExp_EtaExps_ind := 
fun (P : context -> type -> term -> term -> Prop)
      (Q : context -> list type -> list term -> list term -> Prop)
  (f0 : forall rhos sigmas rs ss k t rho, 
     TypJ rhos [k] (sigmas--->rho) ->  
     EtaExps rhos sigmas rs ss -> Q rhos sigmas rs ss -> 
     Eta rhos rho ([k];;ss) t -> P rhos rho ([k];;rs) t) 
  (f1 : forall rhos sigmas rho sigma r s k, 
       length rhos <= k -> 
       length (rhos++sigmas) = k -> 
       EtaExp (rhos ++ sigmas ++ rho :: nil) sigma r s ->
       P (rhos ++ sigmas ++ rho :: nil) sigma r s -> 
       P rhos (rho --> sigma) (\! k : rho, r) (\! k : rho, s))
  (g0 : forall rhos, Q rhos nil nil nil) 
  (g1 : forall rhos s ss r r' l l', 
       EtaExp rhos s r r' -> P rhos s r r' -> 
       EtaExps rhos ss l l' -> Q rhos ss l l' -> Q rhos (s::ss) (r::l) (r'::l'))
  =>
fix F (rhos:context)(rho:type)(t t0 : term) (e : EtaExp rhos rho t t0) 
  {struct e} : P rhos rho t t0 :=
  match e in (EtaExp rhos rho t1 t2) return (P rhos rho t1 t2) with
  | EtaExp_Var rhos sigmas rs ss k t rho T e0 e1 => 
       f0 rhos sigmas rs ss k t rho T e0 (G rhos sigmas rs ss e0) e1 
  | EtaExp_Abs rhos sigmas rho sigma r s k T1 T2 e0 => 
      f1 rhos sigmas rho sigma r s k T1 T2 e0 
         (F (rhos ++ sigmas ++ rho :: nil) sigma r s e0)
 end
with 
 G (rhos:context)(sigmas:list type)(l l' : list term) (e: EtaExps rhos sigmas l l') 
  {struct e} : Q rhos sigmas l l' := 
   match e in (EtaExps rhos sigmas l0 l0') return (Q rhos sigmas l0 l0') with 
   | EtaExps_nil rhos => g0 rhos
   | EtaExps_cons rhos s ss r r' l l' e0 e1 => 
      g1 rhos s ss r r' l l' e0 (F rhos s r r' e0) e1 (G rhos ss l l' e1)
  end
for G.
(* end hide *)

Lemma Eta_red_ctx : forall rhos mus sigma r r', 
    Eta (rhos++mus) sigma r r' ->
    Eta rhos sigma r r'.
Proof.
 induction sigma.
 intros.
 inversion H; subst; auto.
 intros.
 inversion H; subst.
 constructor 2 with (mus++sigmas) etak.
 simp; auto with arith.
 simp; auto.
 rewrite app_ass; rewrite app_ass in H5; auto.
 rewrite app_ass; rewrite app_ass in H8; auto.
Qed.

Lemma EtaExps_red_ctx : forall rhos sigmas l l', 
    EtaExps rhos sigmas l l' ->
    forall rhos' mus, rhos = rhos'++mus -> 
    (forall k, length rhos' <= k -> existsb (occurs k) l = false) ->  
    EtaExps rhos' sigmas l l'.
Proof.
  set (P := fun rhos sigma r r' => 
    forall rhos' mus, rhos = rhos'++mus -> above (length rhos') r -> 
    EtaExp rhos' sigma r r').
  set (Q := fun rhos sigmas l l' => 
    forall rhos' mus, rhos = rhos'++mus -> 
    (forall k, length rhos' <= k -> existsb (occurs k) l = false) ->  
    EtaExps rhos' sigmas l l').
  change (forall rhos sigmas l l', EtaExps rhos sigmas l l' ->  Q rhos sigmas l l').
  apply EtaExp_EtaExps_ind with P; auto.

 red; intros.
 destruct (above_apps _ _ H4); clear H4.
 subst.
 constructor 1 with sigmas ss; eauto.
 eapply TypJ_red_ctx; eauto. 
 eapply Eta_red_ctx; eauto.
 
 red; intros.
 constructor 2 with (mus++sigmas); eauto.
 generalize H; rewrite H3; simp; intros; omega. 
 generalize H0; rewrite H3; simp; intros; omega.
 rewrite app_ass; auto.
 rewrite H3 in H1; rewrite app_ass in H1; auto.
  
 red; intros; auto.

 red; intros.
 constructor.
 unfold P in H0; apply H0 with mus; auto.
 red; intros.
 destruct (orb_false_elim _ _ (H4 n H5)); auto.
 unfold Q in H2; apply H2 with mus; auto.
 intros.
 destruct (orb_false_elim _ _ (H4 k H5)); auto.
Qed.
