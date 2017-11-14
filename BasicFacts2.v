
(* This file contains some more facts about subsets and powersets -------------

 1.Lemma Inc_Exclusion:  |A U B| = |A|+|B|-|A.B| 
                           Here A.B represents intersection of A and B
 2.Lemma U_card_less:    |A U B|<= |A|+|B|      

 3.Lemma Exists_a_subset_m:  Let A be a set. Then, for every m <= |A|, 
                             there exists a subset of A of size  m.     
 4.Lemma U_Bound1: Let A be a collection of sets such that every set in
                    A has size less than equal to r. Then,
                    |Union_over A|<= |A|*r.
 5. Lemma U_Bound3: Let A be a collection of sets such that,
                    |Union_over A| = m*n+1 for some m and n. If |A|<=m then
                    there exists a set A0 in A such that |A0|>= n+1.      *)



Require Export Combi_1.
Require Export omega.Omega.


Section BasicFacts2.
  
  Variable U:Type.
 (* -----------------------Basic Arithmetic facts------------------------------------ *) 

Lemma nat_P7: forall n m :nat, n=m -> ~ (n < m).
  Proof. intros. cut (m<=n). auto with arith.  rewrite H. auto. Qed.
  
  Lemma nat_P8: forall n m :nat, n=m -> ~ (n > m).
  Proof. intros. cut (n<=m). auto with arith.  rewrite H. auto. Qed.
  
  Lemma mult_r_compat_eq: forall m n p:nat, p<> 0 -> m *p = n*p -> m=n.
  Proof. { intros. SearchPattern  (?m * ?p = ?n * ?p -> ?p <> 0 -> ?m = ?n). destruct p.
          absurd (0=0);auto. replace (m * S p) with (S p * m) in H0.
          replace (n * S p) with (S p * n) in H0.
          assert (~ S p * m < S p * n).
          { eapply nat_P7. auto.  }
          assert ( S p * m <= S p * n).
          { rewrite H0. auto.  }
          assert (m <= n).
          { eapply mult_S_le_reg_l. instantiate (1 := p). auto. }
          assert ( m<n \/ m=n).
          { eapply le_lt_or_eq. auto. }
          elim H4.
          { intro. absurd (S p * m < S p * n). auto.  auto with arith. }
          { tauto. }
          auto with arith. 
          auto with arith. } Qed.
  
  Lemma mult_l_compat_eq:  forall m n p:nat, p<> 0 -> p * m = p * n -> m=n.
  Proof. { intros. eapply mult_r_compat_eq. exact H.
         replace (m*p) with (p * m) ; replace (n* p) with (p *n).
         auto. auto with arith. auto with arith. auto with arith. } Qed. 

   Lemma nat_P9:  forall m n: nat, m * n = 0 -> (m=0 \/ n=0).
   Proof. apply mult_is_O. Qed.

   
  Lemma fact_pos : forall k:nat, fact k > 0.
  Proof. { induction k; simpl; auto with arith. }  Qed.

  Hint Resolve mult_is_O mult_l_compat_eq mult_r_compat_eq fact_pos mult_le_compat_r: arith0.
  Hint Resolve Definition_of_Power_set cardinalO_empty card_soustr_1: sets0.

  
  (* ---------------------------Facts on SETS------------------------------------------ *)

  (* Variable r0 s0: nat. *)
  (* Variable C_S: Ensemble (Ensemble U).*)

  Lemma Card_set_minus: forall (A B C: Ensemble U) (m n:nat), Union _ A B = C -> Disjoint _ A B ->
                                                       cardinal _ B n -> cardinal _ C m ->
                                                       cardinal _ A (m-n).
  Proof. { intros.
         assert (Finite _ A).
         { cut (Included _ A C). auto_with_sets0. auto_with_sets0. eauto. rewrite <- H.
           auto with sets. }
         assert (exists p, cardinal _ A p).
         {auto_with_card0. auto. } destruct H4 as [p H4].
         assert (cardinal _ C (p+n)).
         { rewrite <- H. auto_with_card0;tauto. }
         assert (m=p+n). eapply cardinal_unicity;eauto. replace (m-n) with p.
         auto. omega. } Qed.

  Lemma Inc_Exclusion: forall (m n p:nat) (A B: Ensemble U), cardinal _ A m -> cardinal _ B n ->
                                                      cardinal _ (Intersection _ A B) p ->
                                                      cardinal _ (Union _ A B) (m+n-p).
  Proof. { intros.
         pose (B0:= Setminus _ B A).
         pose (AB:= Intersection _ A B).

         assert (F0: p<=n).
         { auto_with_card0. eauto. eauto. auto with sets. }

         assert (F1: Union _ A B = Union _ A B0).
         { unfold B0.  auto_with_sets0. }

         assert (F2: Disjoint _ A B0).
         {  unfold B0; apply Disj_comm; auto_with_sets0. }

         assert (F3: Union _ B0 AB = B).
         { unfold B0; unfold AB. unfold_equal.
           unfold Included. destruct 1. apply H2.
           destruct H2. auto.
           unfold Included. intros. elim (classic (In _ A x)).
           intro. auto with sets. intro. auto with sets. }

         assert (F4: Disjoint _ B0 AB).
         { unfold B0. unfold AB. Print Disjoint.  apply Disjoint_intro.
           intros. intro.  absurd (In _ A x); destruct H2. apply H2.
           destruct H3;auto.  }

         assert (F5: cardinal _ B0 (n-p)).
         { eapply Card_set_minus. eauto. eauto. unfold AB. auto. auto.  }

         rewrite F1. replace (m+n-p) with (m+(n-p)). eapply Disjoint_card;tauto.
         cut (n>=p). omega. cut(p<=n). omega. auto. } Qed.

 
  Lemma U_card_less: forall (A B: Ensemble U)(m n q:nat),
        cardinal _ A m -> cardinal _ B n -> cardinal _ (Union _ A B) q -> q <= m+n.
  Proof. { intros.
           assert (exists p, cardinal _ (Intersection _ A B) p).
           { pose (AB:= (Intersection _ A B)).
             cut ( exists p : nat, cardinal U AB p). unfold AB;tauto.
             auto_with_card0. cut(Included _ AB A). auto_with_sets0.
             auto_with_card0;eauto.
             unfold AB; auto with sets. }
           destruct H2 as [p H2]. replace q with (m+n-p).
           omega. auto_with_card0. eapply Inc_Exclusion;eauto. auto. } Qed. 

  Lemma Exists_a_subset_m: forall (m n:nat)(S:Ensemble U), (cardinal _ S n /\ m<=n)->
                                    (exists S0:Ensemble U, Included _ S0 S /\ cardinal _ S0 m).
  Proof. {
    (* Easy to prove using induction on n *)
    induction n.
    { intro C. intros.  exists C. split. auto with sets.
      replace m with 0. tauto. omega. }

    { intro C. intros. destruct H.
      assert (m<= n \/ m = S n). omega. elim H1.
      { intro.
        assert (exists C0 , (exists x, C = Add U C0 x /\ ~ In U C0 x /\ cardinal U C0 n)).
        { eapply cardinal_invert with (p:= S n). auto. }
        destruct H3 as [C0 H3].  destruct H3 as [c H3]. destruct H3. destruct H4.
        assert ( exists S0 : Ensemble U, Included U S0 C0 /\ cardinal U S0 m).
        { eapply IHn. tauto. } destruct H6 as [S0 H6].
        exists S0. split. cut (Included _ C0 C). intro. eapply_trans0. apply H6. auto.
        rewrite H3. auto with sets. tauto. }
      { intro. exists C. rewrite H2. split. auto with sets. tauto. } } } Qed. 

  Lemma U_Bound1: forall (s0:nat)(r:nat)(C_S: Ensemble (Ensemble U)), (cardinal _ C_S r)->
  (forall (S:Ensemble U)(m:nat), (In _ C_S S /\ cardinal _ S m) -> m<=s0) ->
                                  (forall q:nat, cardinal _ (Union_over  C_S) q -> q <= r*s0).
  Proof. { induction r.
         (* Base case when r=0 *)
         { intro C_A. intros. 
           assert (C_A = Empty_set _ ).
           eapply cardinal_invert with (p:=0). auto.
           assert (Union_over C_A = Empty_set _).
           rewrite H2. auto_with_sets0. rewrite H3 in H1.
           cut (q=0). omega. eapply cardinal_unicity. apply H1.
           auto with sets. }

         (* Induction Step *)
         { intro C_A. intros.
           assert (exists C : _, (exists A : _, C_A = Add _ C A /\ ~ In _ C A /\ cardinal _ C r)).
           eapply cardinal_invert with (p:= S r). auto.
           destruct H2 as [C H2]. destruct H2 as [A H2]. destruct H2. destruct H3.
           assert (Union_over C_A = Union _ (Union_over C) A).
           { rewrite H2. auto_with_sets0. }
           assert (exists q0, cardinal _ (Union_over C) q0).
           { cut (Finite _ (Union_over C)). auto with sets0.
             cut (Included _ (Union_over C) (Union_over C_A)).
             auto_with_sets0. eapply cardinal_finite.  apply H1.
             rewrite H5. auto with sets. }
           destruct H6 as [q0 H6].
           assert (q0<= r*s0).
           { eapply IHr. eauto. intros.
             cut (In (Ensemble U) C_A S /\ cardinal U S m). apply H0.
             split. rewrite H2. cut ( In (Ensemble U) C S).
             auto with sets. tauto. tauto. tauto. }
           assert (exists s, cardinal _ A s).
           { cut (Finite _ A). auto with sets0.
             cut (Included _ A (Union_over C_A)). auto_with_sets0.
             auto_with_card0.  apply H1.
             cut (In _ C_A A). auto_with_sets0. rewrite H2. auto with sets. }
           destruct H8 as [s H8].
           assert (s<=s0).
           { eapply H0 with (S:=A). split. rewrite H2;auto with sets. auto. }
           assert (q<= q0+s).
           { eapply  U_card_less. eauto. eauto. rewrite <- H5. auto. }

           assert (q<= r*s0 +s). omega.
           assert (q<= r*s0 +s0). omega.
           replace (r*s0 +s0) with ((S r)*s0) in H12. auto.
           replace (S r) with (r+1). ring.  omega.  }    } Qed.


  Lemma U_Bound2: forall(r0 s0:nat) (r:nat)(C_S: Ensemble (Ensemble U)),
      (cardinal _ C_S r /\ r<=r0)->(forall (S:Ensemble U)(m:nat), (In _ C_S S /\ cardinal _ S m) -> m<=s0) ->
      (forall q:nat, cardinal _ (Union_over  C_S) q -> q <= r0*s0).
  Proof. { intros r0 s0. intros. cut (q<= r*s0). intro. destruct H. cut (r*s0 <= r0*s0).
         omega. auto with arith0.
         assert (forall q:nat, cardinal _ (Union_over  C_S) q -> q <= r*s0).
         {eapply U_Bound1. tauto. tauto. } auto. } Qed. 


  Lemma U_Bound3: forall(r0 s0:nat) (r:nat)(C_S: Ensemble (Ensemble U)),
      (cardinal _ C_S r /\ r<=r0)->(cardinal _ (Union_over  C_S) (r0*s0+1))->
      (exists (S:Ensemble U)(m:nat), In _ C_S S /\ cardinal _ S m /\ m >s0).
  Proof. {
    intros.
    elim (EM ( exists (S : Ensemble U) (m : nat), In (Ensemble U) C_S S /\ cardinal U S m /\ m > s0)).
    auto. intro.
    assert (forall (S:Ensemble U)(m:nat),( In _ C_S S /\ cardinal _ S m) -> m<=s0).
    { cut (forall (S : Ensemble U) (m : nat), ~ (In (Ensemble U) C_S S /\ cardinal U S m /\ m > s0)).
      { intro.  intro. intro. cut ( ~ (In (Ensemble U) C_S S /\ cardinal U S m /\ ~ m <= s0)).
        tauto. cut (~ (In (Ensemble U) C_S S /\ cardinal U S m /\ m > s0)).
        intro. intro. apply H3. split. apply H4. split. tauto. cut (~ m <= s0). omega.
        tauto. auto.  }
      cut (forall (S : Ensemble U), ~ exists m : nat , (In (Ensemble U) C_S S /\ cardinal U S m /\ m > s0)).
      intro. intro.  apply not_ex_all_not. auto. 
        apply not_ex_all_not. auto. }  
    assert (forall q:nat, cardinal _ (Union_over  C_S) q -> q <= r0*s0).
    { apply U_Bound2 with (r:=r);auto. }
    absurd (r0*s0+1 <= r0*s0). omega.  auto. } Qed. 
    
         
         



 (* Following definitions are from /trunk/Orsay/FSets/PowerSet.v *)
  (* Written by Pierre Letouzey *)

    
  (* Fixpoint fact n := match n with 
	  | O => 1 
	  | S n' => n * (fact n') 
	             end. *)  

   
(* -----------------------------BINOMIAL Coeficient properties----------------------- *)
  Fixpoint binomial n k { struct n } := match n, k with 
	  | _, O => 1
	  | O, _ => 0 
	  | S n', S k' => binomial n' k' + binomial n' k
                                        end.

  Definition powerset_k (S: Ensemble U)(k: nat)(e: Ensemble U):= Included _ e S /\ cardinal _ e k.

 


  Lemma binomial0 : forall n k:nat, k>n -> binomial n k = 0.
  Proof. {
    induction n; destruct k; simpl; auto.
    inversion 1.
    inversion 1.
    intros.
    do 2 (rewrite IHn; auto with arith). } Qed.
  
  Lemma binomial_rec : forall n k:nat, k<=n ->  (binomial n k)*(fact k * fact (n-k)) = fact n.
  Proof. {
	induction n; destruct k.
	simpl; auto.
	inversion 1.
	simpl;intros; ring.
	intros.
	change (fact (S n)) with ((1+n)*(fact n)).
	change (fact (S k)) with ((1+k)*(fact k)).
	simpl (S n - S k).
	simpl binomial.
	inversion_clear H.
	rewrite (binomial0 n (S n)); auto.
	pattern (fact n) at 2; rewrite <- (IHn n); auto; ring.
	cut ((binomial n k)*(fact k*fact (n-k))*(1+k) + 
	     (binomial n (S k))*(fact (S k)*fact (n-S k))*(n-k) = 
	     (1+n)*fact n).
	intros H; rewrite <- H.
	replace (n-k) with (S (n-S k)) by omega.
	simpl; ring.
	rewrite (IHn k); auto with arith.
	rewrite (IHn (S k)); auto with arith.
	cut (((1+k)+(n-k))*(fact n) = (1+n)*(fact n)).
	intro H; rewrite <- H; ring.
	replace (1+k+(n-k)) with (1+n) by omega; auto. } Qed. 

	
  Lemma binomial_den_pos : forall n k:nat, fact k * fact (n-k) > 0.
  Proof. { intros; generalize (fact_pos k) (fact_pos (n-k)).
	 unfold gt; intros.
	 change 0 with (0*(fact (n-k))).
	 apply mult_lt_compat_r; auto with arith. } Qed.

  Definition C (n:nat)(k:nat):= binomial n k.

  Lemma binomial1: forall n:nat, binomial n n = 1.
  Proof. { induction n. simpl. auto. simpl.
           rewrite IHn. rewrite binomial0; auto with arith.  } Qed.
 
  Lemma binomial2 : forall n i:nat, (i <= n) -> C n i = C n (n - i).
  Proof. { intros n i. intro. unfold C.
         assert ((binomial n (n-i))*(fact (n-i) * fact (n- (n-i))) = fact n). 
         { apply binomial_rec. omega.  }
         replace (n- (n-i)) with i in H0.
         replace  (fact (n - i) * fact i) with  (fact i * fact(n- i)) in H0.
         assert ( (binomial n i) * (fact i * fact (n - i)) = fact n).
         { apply binomial_rec. auto. }
       cut (binomial n i * (fact i * fact (n - i))=binomial n (n - i) * (fact i * fact (n - i))).
         auto with arith. SearchPattern (?p <>0 -> ?m * ?p = ?n * ?p -> ?m = ?n).
         apply mult_r_compat_eq.
         cut (fact i * fact (n-i) > 0).
         intros. intro. rewrite H3 in H2. inversion H2. apply binomial_den_pos.
         rewrite H0;rewrite H1. auto. auto with arith. omega. } Qed.
 
  Lemma binomial3: forall n i:nat, C n i + C n (S i) = C (S n) (S i).
  Proof. { intros.  simpl. reflexivity. } Qed. 
  
 
  Lemma Finite_powerset_k: forall (S: Ensemble U)(k: nat), Finite _ S -> Finite _ (powerset_k S k).
  Proof. { intros. cut (Included _ (powerset_k S k) (Power_set _ S)).
          auto_with_sets0.  auto_with_sets0. auto. unfold Included.
          intros. unfold In in H0. unfold powerset_k in H0.
          destruct H0. auto with sets0. } Qed.

  Lemma powerset_k0: forall (S0: Ensemble U ), Singleton _ (Empty_set U)=  powerset_k S0 0 .
  Proof. { intro. unfold_equal. unfold Included.
           intros. destruct H. unfold In. unfold powerset_k. split; auto with sets.
           unfold Included. intros. unfold In in H. unfold powerset_k in H.
           destruct H. cut (x= Empty_set U). intro. rewrite H1. auto with sets.
           generalize H0. auto with sets0. } Qed. 

  Lemma powerset_k_cardinal: forall (S0: Ensemble U) (k:nat)(n:nat),
      cardinal _ S0 n -> cardinal _  (powerset_k S0 k) (C n k).
  Proof. { intros S k0 n. generalize S as S0. generalize k0 as k. clear S. clear k0.
         induction n.
         { destruct k.
         { intros. simpl. replace (powerset_k S0 0) with (Singleton _ (Empty_set U)).
           auto_with_card0.  apply powerset_k0. } 
         { intros. simpl.
           assert ( S0= Empty_set U). auto with sets0. rewrite H0. 
           replace (powerset_k (Empty_set U) (Datatypes.S k)) with
           (Empty_set (Ensemble U)).  auto with sets.
           unfold_equal.
           { unfold Included. intros.  inversion H1. }
           { unfold Included.  intros. unfold In in H1. unfold powerset_k in H1.
             destruct H1.
             assert (x= Empty_set U). auto with sets.
             assert (Inhabited _ x). auto with sets. eapply cardinal_elim with (p:= (S k)).
             auto. absurd (x= Empty_set U). auto with sets. auto. } } } 
         { intros. destruct k.
           { simpl.
           replace (powerset_k S0 0) with ( Singleton _ (Empty_set U)).
           auto_with_card0. apply powerset_k0. } 
           { simpl.
             apply cardinal_invert with (X:= S0) (p:= S n) in H as H1.
             destruct H1 as [A H1]. destruct H1 as [a H1].
             destruct H1. destruct H1.
             (* At this point we have S0 = A U {a} *)
             (* We use the notation SK1 to represent collection of subsets of S0 of size k+1 *)
             (* i,e SK1 = (powerset_k S0 (S k)) *)
               (* SK_a is a collection of subsets from SK1 which contains a *)
               (* SK_na is a collection of subsets from SK1 that doesnot contain a *)
               (* Hence we can show that SK1 = Union SK_a  SK_na  *)
               (* Moreover SK_a and SK_na are mutually disjoint *)
               (* Hence | SK1| = |SK_a| + |SK_na| *)
               (* We prove that |SK_a|= C n k and |SK_na|= C n (S k) *)
               (* For this we show a bijection, say g, between AK and SK_a *)
               (* We also show a bijection, say f, between AK1 and SK_na *)
               (* Here AK is collection of subset of A of size k *)
               (* Here AK1 is collection of subset of A of size k+1 *)
             (* Where f(e):= e and g(e):= e U {a} *)

             assert (F0: A = Subtract _ S0 a).
             { rewrite H0.  auto with sets. }

             pose (SK1:= (powerset_k S0 (S k)) ).
             pose (SK_a(e: Ensemble U):= SK1 e /\ In _ e a).
             pose (SK_na(e: Ensemble U):= SK1 e /\ ~ In _ e a).

             assert (F1: SK1 = Union _ SK_a SK_na).
             { unfold_equal.
               { unfold Included. intro e. intro.
               elim (classic (In _ e a)). intro. apply Union_introl. unfold In.
               unfold SK_a. tauto.
               intro. apply Union_intror. unfold In. unfold SK_na. tauto. }
               { unfold Included. intro e. intro. destruct H3. apply H3. apply H3. } }
             
             assert (F2: Disjoint _ SK_a SK_na).
             { Print Disjoint. apply  Disjoint_intro.
              intro. intro. destruct H3.
              absurd (In U x a). apply H4. apply H3.  } 

             pose (AK:= (powerset_k A k)).
             pose (AK1:= (powerset_k A (S k))).

             assert (F3: cardinal _ AK (C n k)).
             { unfold AK. auto. }
             assert (F4: cardinal _ AK1 (C n (S k)) ).
             { unfold AK1. auto. }
             
             pose (f (e1 e2: Ensemble U):= e1 = e2).
             pose (g0 (e: Ensemble U):= Add _ e a). (* g cant not be bijection *)
             pose (g (e1 e2: Ensemble U) := e2 = Add _ e1 a).

             assert (F5: cardinal _ SK_na (C n (S k))).
             { eapply Bijection_Relation3 with (A:= AK1) (R:= f).
               { intros. exists x. unfold In. unfold f. unfold SK_na. unfold SK1.
                 unfold In in H3. unfold AK1 in H3. unfold powerset_k in H3.
                 unfold powerset_k. split. split. destruct H3. rewrite H0. split.
                 unfold Add. auto with sets. tauto. intro. apply H1.
                 cut (Included _ x A). auto with sets. tauto. reflexivity. }
               { unfold In. unfold SK_na. unfold AK1. unfold f. unfold SK1.
                 unfold powerset_k. rewrite H0. intros. destruct H3. destruct H3.
                 exists b. split. split.
                 unfold Included in H3. unfold Included. intros.
                 assert (In U (Add U A a) x). auto.
                 destruct H7. auto. destruct H7. contradiction. auto. tauto. }
               { unfold f. intros. cut (y=b). cut (x=b). intros.
                 rewrite H4. rewrite H5. tauto. tauto. tauto. }
               { unfold f. intros. cut (a0=y). cut (a0=x). intros.
                 rewrite <- H4. rewrite <- H5. tauto. tauto. tauto. }
               { auto. } } 
              

             assert (F6: cardinal _ SK_a (C n k)).
             { eapply Bijection_Relation3 with (A:= AK) (R:= g).
               { unfold In. unfold AK. unfold SK_a. unfold SK1. unfold powerset_k.
                 unfold g. intros. destruct H3. exists (Add _ x a). repeat (split).
                 rewrite H0. auto with sets. apply card_add. auto. intro.
                 absurd (In _ A a ). auto. auto with sets. auto with sets. }
               { unfold In;unfold AK; unfold SK_a; unfold SK1; unfold powerset_k.
                 unfold g;intros. destruct H3. destruct H3.
                 pose (a0:= Subtract _ b a).
                 assert ( b = Add _ a0 a). unfold a0; auto with sets.
                 assert (cardinal _ a0 k). unfold a0;replace k with (pred (S k)).
                 auto with sets0. omega.
                 exists a0. repeat (split).
                 unfold a0;unfold Included;intros;rewrite F0.
                 destruct H8. unfold Subtract;unfold In; unfold Setminus.
                 split; (auto with sets|| tauto). tauto. tauto. }
               {  unfold In;unfold AK; unfold SK_a; unfold SK1; unfold powerset_k.
                  unfold g;intros. destruct H3;destruct H4;destruct H5.
                  assert ( ~ In _ x a ).
                  { intro; destruct H3; apply H1;auto with sets. }
                  assert (~ In _ y a).
                  { intro; destruct H4; apply H1; auto with sets. }
                  destruct H6.
                  assert (x= Subtract _ b a). rewrite H6; auto with sets.
                  assert (y= Subtract _ b a). rewrite H9; auto with sets.
                  rewrite H10; rewrite H11; tauto.  }
               {  unfold In;unfold AK; unfold SK_a; unfold SK1; unfold powerset_k.
                  unfold g;intros.  destruct H3;destruct H4;destruct H5.
                  replace x with (Add U a0 a). replace y with (Add U a0 a). tauto.
                  symmetry;tauto. symmetry;tauto. }
               { tauto. } } 

             replace (powerset_k S0 (S k)) with SK1. rewrite F1.
             auto_with_card0. tauto. unfold SK1. reflexivity. } }   } Qed.
             
 (*------------------------------Binomial coefficient properties--------------------------*)

End BasicFacts2.


Hint Resolve mult_is_O mult_l_compat_eq mult_r_compat_eq fact_pos: arith0.
Hint Resolve binomial0 binomial1 binomial2 binomial3 : arith0.
  
Hint Resolve Definition_of_Power_set cardinalO_empty card_soustr_1: sets0.
Hint Resolve Finite_powerset_k powerset_k0 powerset_k_cardinal: sets0.

Hint Resolve card_soustr_1 powerset_k_cardinal: card0.





          
        
  
 

  