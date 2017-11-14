(* This File contains the proof of Hall's marriage theorem on Bipartite Graphs. 
   Let G=(L,R,Edge) be a bipartite graph and V= L U R. Then we have, 

    Theorem Halls_Thm:  (forall (S: Ensemble U), Included _ S L -> 
           (forall m n :nat, (cardinal _ S m /\ cardinal _ (N S) n) -> m <=n ) )
       <-> ( exists Rel': Relation U, Included_in_Edge Rel' /\ Is_L_Perfect Rel').

   where, Included_in_Edge is defined as,

   Definition Included_in_Edge (Rel: Relation U): Prop := 
                    forall x y:U, Rel x y -> Edge x y.

It states that, for any bipartite graph G=(L,R,E),
 forall S in L,|N(S)|>=|S| if and only if there exists an L-perfect matching. 

Here, a matching is said to be L-perfect if each vertex in L is part of some edge
of the matching. *)



Require Export Combi_1.
Require Export Graph.
Require Import FiniteDilworth_AB.
Require Import FiniteDilworth.


Section Halls_Thm.

  Variable U: Type.

  Print Finite_Graph.
  Print Graph.
  Print Biper_Graph.

  
  Variable G: Biper_Graph U. Check (Edge_Rel_of G). 

  Let Edge := (Edge_Rel_of (Graph_of_BG G )).
  Let V:= (Vertices_of (Graph_of_BG G)).
  Let L:= L_of G.
  Let R:= R_of G.

  Set Implicit Arguments. 

  Check Edge. Check V. Check L. Check R.
  
  Lemma BG1: Finite _ V.
  Proof. apply  F_Graph_cond. Qed.

   Lemma BG2: Inhabited _ V.
  Proof. apply  NonEmpty_cond. Qed.

  Lemma BGa2: Inhabited _ L.
  Proof. apply LR_Inhabited. Qed.

  Lemma BGb2: Inhabited _ R.
  Proof. apply LR_Inhabited. Qed.

  
  Lemma BG3: Disjoint _ L R.
  Proof. apply LR_Disj. Qed.

  Lemma BGa3: forall x y: U, Edge x y -> ~ In _ L y.
  Proof. { intros x y H0 H1.
         assert (H2: In _ L x /\ In _ R y). apply LR_Rel. auto.
         assert (H3: Disjoint _ L R). apply LR_Disj. destruct H3.
         absurd (In U (Intersection U L R) y). auto. 
         apply Intersection_intro; tauto.  } Qed. 
 

  Lemma BGb3: forall x y: U, Edge x y -> ~ In _ R x.
  Proof. { intros x y H0 H1.
         assert (H2: In _ L x /\ In _ R y). apply LR_Rel. auto.
         assert (H3: Disjoint _ L R). apply LR_Disj. destruct H3.
         absurd (In U (Intersection U L R) x). auto. 
         apply Intersection_intro; tauto.  } Qed. 

  Lemma BGd3:  forall x y : U, Included U (Couple U x y) L -> ~ Edge x y.
  Proof. { intros x y H0 H1.
         assert (H2: In _ L x /\ In _ L y). { unfold Included in H0.
         split; apply H0; (apply Couple_l || apply Couple_r). }
         absurd (In _ L y). eapply BGa3. exact H1. tauto. } Qed.
 

  Lemma BGe3:  forall x y : U, Included U (Couple U x y) R ->  ~ Edge  x y. 
  Proof.  { intros x y H0 H1.
         assert (H2: In _ R x /\ In _ R y). { unfold Included in H0.
         split; apply H0; (apply Couple_l || apply Couple_r). }
         absurd (In _ R x). eapply BGb3. exact H1. tauto. } Qed.

 
   Ltac EdgeThm
    :=first [ eapply BGa3 | eapply BGb3   |  eapply BGd3 |  eapply BGe3 ].

  Lemma BG4: V = Union _ L R.
  Proof. apply LR_Union. Qed.

  Lemma BG5: forall x y: U, Edge x y -> (In _ L x /\ In _ R y ).
  Proof. apply LR_Rel. Qed.

  Lemma BGa5: Included _ L V.
    Proof. rewrite BG4.  unfold Included. apply Union_introl. Qed.  

  Lemma BGb5: Included _ R V.
   Proof. rewrite BG4.  unfold Included. apply Union_intror. Qed. 

  Hint Resolve BG1 BG2 BGa2 BGb2 BG3 BGa3 BGb3 BG4 BG5 BGa5 BGb5 : BG.

  Lemma BG6: Order _  (fun (x: U)(y:U)=> Edge x y \/ x=y ).
  Proof. { Print Order. apply Definition_of_order.
         unfold Reflexive. intro. right; reflexivity.
         unfold Transitive. {
         intros x y z H0 H1.
         elim H0; elim H1. 
         { intros. absurd (In _ R y). EdgeThm. exact H. Print Biper_Graph.
           assert (H3: In _ L x /\ In _ R y  ). auto with BG. tauto. }
         { intros. subst. left. tauto. }
         { intros. subst. left. tauto. }
         { intros. subst. right. tauto. } }
         unfold Antisymmetric. {
           intros x y H0 H1. elim H0;elim H1.
           { intros. absurd ( In _ L y). EdgeThm. exact H2.
             assert (H3: In _ L y /\ In _ R x  ). auto with BG. tauto. }
           { intros; subst; reflexivity. }
           { intros; subst; reflexivity. } 
           { intros. tauto. } }  } Qed. 

 
 Definition N (S: Ensemble U): Ensemble U:= fun (y: U)=> exists x:U, In _ S x /\ Edge x y.
  Check N V. 

  Lemma BG7: forall (e: Ensemble U) (x: U)(y: U), (In _ e x /\ Edge x y )-> In _ (N e) y.
  Proof. intros. unfold In. unfold N.  exists x. tauto. Qed.

  Ltac reduce_N H := try (unfold In in H); unfold N in H.

  Ltac reduce_NG := try (unfold In); unfold N.
  
  

  Lemma BG8:  forall x y: U, Edge x y -> (In _ R y ).
  Proof. { intros x y H0. cut (In _ L x /\ In _ R y ). tauto.  auto with BG. } Qed. 

  Lemma BG9:  forall x y: U, Edge x y -> (In _ L x ).
  Proof . { intros x y H0. cut (In _ L x /\ In _ R y ). tauto.  auto with BG. } Qed.

  Hint Resolve BG6 BG7 BG8 BG9: BG.

  Lemma BG10: Included _ (N L) R.
  Proof. { unfold Included. intros y H0. reduce_N H0.   destruct H0 as [x H0].
           destruct H0. eauto with BG. } Qed.

  Lemma BG11: Included _ (N L) V.
  Proof. unfold Included. intros. rewrite BG4. apply Union_intror. apply BG10. auto. Qed.

  Lemma BG12: Finite _ (N L).
    Proof.  { apply Finite_downward_closed with (A:= V). auto with BG. apply BG11. } Qed.

  Lemma BG13:  exists m' : nat, cardinal U (N L) m'.
  Proof.  apply finite_cardinal.  apply BG12. Qed.

 

  Lemma BG14: Finite _ L.
  Proof. apply Finite_downward_closed with (A:= V). auto with BG. auto with BG.  Qed.

  Lemma BG15: Finite _ R.
  Proof. apply Finite_downward_closed with (A:= V). auto with BG. auto with BG.  Qed.

  Lemma BG16: exists m: nat, cardinal U L m.
  Proof. apply finite_cardinal. apply BG14. Qed. 

  Lemma BG17: exists n:nat, cardinal U R n.
    Proof. apply finite_cardinal. apply BG15. Qed. 
  
  
    Hint Resolve  BG10 BG11 BG12 BG13 BG14 BG15 BG16 BG17 : BG. 
    

    

 (* --------------------------------------------------------------------------------- *)   
 (* _____________________ PROOF OF HALL'S THEOREM ___________________________________ *)   




  Definition Is_a_matching (Rel: Relation U): Prop:=
     ( forall x y z: U, ((Rel x z /\ Rel y z)\/ (Rel z x /\ Rel z y)) -> x=y). 

  Definition Is_L_Perfect (Rel: Relation U): Prop:=
          (Is_a_matching Rel /\ (forall x: U, In _ L x -> (exists y: U, Rel x y)) ).

  Definition Included_in_Edge (Rel: Relation U): Prop := forall x y:U, Rel x y -> Edge x y.
  Check Included_in_Edge.


  Theorem Hall_B:  ( exists Rel': Relation U, Included_in_Edge Rel' /\ Is_L_Perfect Rel')-> 
                   (forall (S: Ensemble U),
                  Included _ S L -> (forall m n :nat, (cardinal _ S m /\ cardinal _ (N S) n) -> m <=n ) ). 

  
  Proof. { intros. destruct H as [Rel' H]. destruct H as [Ha Hb].
         unfold Is_L_Perfect in Hb. destruct Hb as [Hb Hc].
         unfold Is_a_matching in Hb. unfold Included_in_Edge in Ha.
         pose (N'(S: Ensemble U)(y: U) := exists x:U, In _ S x /\ Rel' x y).
         
         assert (H2: cardinal _ (N' S) m).
         { eapply Bijection_Relation3 with (A:= S) (R:= Rel').
           { intros.
             assert (H2: exists y : U, Rel' x y).
             { apply Hc. apply H0. auto. } destruct H2 as [y H2].
             assert (H3: Edge x y).
             { auto. }
             exists y. unfold In. unfold N'. split. exists x. tauto. tauto.  }

           { intros.  destruct H. exists x; tauto.  }
           { intros. eapply Hb with (z:=b). left; tauto. }
           { intros. eapply Hb with (z:=a). right;tauto. }
           { tauto. } }

         assert (H3: Included _ (N' S) ( N S)).
         { unfold Included. intros. destruct H. unfold N. unfold In.
           exists x0. split. apply H.  apply Ha.  tauto.  }

         eapply incl_card_le. exact H2. Focus 2. exact H3. tauto. 

          }  Qed. 


  
  

  Theorem Hall_A: (forall (S: Ensemble U),
                 Included _ S L -> (forall m n :nat, (cardinal _ S m /\ cardinal _ (N S) n) -> m <=n ) ) ->
                 ( exists Rel': Relation U, Included_in_Edge Rel' /\ Is_L_Perfect Rel'). 
  Proof. {

    (* We need a POSET reflecting the property of bipertite graph. *)
    pose (Rel (x: U)(y: U) := (Edge x y \/ x=y) ).
    pose (C:= Union _ L R).
    assert (F: C= V ).
    { unfold C. symmetry. auto with BG. }
   
   assert (F1: Inhabited U C).
    { rewrite F. auto with BG. }  Print PO. 
    assert (F2: Order U Rel). Print FPO.
    { auto with BG. }
    assert (F3: Finite U C).
    { rewrite F. auto with BG. }  Print FPO. Print PO.
    pose ( P := {| PO_of:= {|Carrier_of := C; Rel_of:= Rel; PO_cond1:= F1; PO_cond2:= F2 |};
                   FPO_cond:= F3|} ).

    (* Here we have a POSET P which reflects the Bipertite graph G *)
    intros.
    (* At this point we have assumption H : forall S included in L , |S| <= | N(S)| *)

    
    assert ( F4:  exists m' : nat, cardinal U (N L) m').
    { auto with BG. } destruct F4 as [m' F4].

    (* We can deduce that the size of L is less than equal to the size of R *)
    assert (F5: forall m n: nat, cardinal _ L m -> cardinal _ R n -> m<=n ).
    { intros m n. intros.
      assert (H2: m<= m'). { apply H with (S:= L). unfold Included.  tauto. tauto. }
      assert (H3: m'<= n). { eapply incl_card_le.  exact F4.  exact H1.  auto with BG. }
      auto with arith. SearchPattern ( _ <= ?x1 -> ?x1 <= _ -> _ <= _). eapply le_trans. exact H2.
      auto. }

    (* Let m be the size of L *)
    assert ( F6: exists m: nat, cardinal U L m).
    { auto with BG. }
    destruct F6 as [m F6].
    
    
    assert (F7: exists n:nat, cardinal U R n).
    { auto with BG. } destruct F7 as [n F7].

    (* At this point we have  |L|= m and |R|= n as sizes *)

    assert (F8: m<= n). { eauto. }  (* We have at this point |L| < = |R| *)

     (* L is an antichain *)
    assert ( Hc1: Is_an_antichain_in  P L).
    {  Print Is_an_antichain_in.  unfold Is_an_antichain_in. split.
       
       split. simpl. unfold C. unfold Included. apply Union_introl.  auto with BG.
       auto. auto with BG. simpl. unfold Rel.  intros x y F12. intro F13.
       elim F13.
       intro F14. elim F14. intro F15. absurd ( Edge x y).
       generalize F12. EdgeThm.  auto. auto.
       intro F14. elim F14. intro F15. absurd ( Edge  y x ).  apply BGd3.
       generalize F12. rewrite <- Couple_comm.  tauto. tauto.
       intro. symmetry. tauto.  }

    assert (Hc2: Is_an_antichain_in  P R).
    {  Print Is_an_antichain_in. unfold Is_an_antichain_in. split.
       split. simpl. unfold C. unfold Included. apply Union_intror.  auto with BG.
       auto. auto with BG. simpl. unfold Rel.  intros x y F12. intro F13.
       elim F13.
       intro F14. elim F14. intro F15. absurd ( Edge x y).
       generalize F12. EdgeThm.  auto. auto.
       intro F14. elim F14. intro F15. absurd ( Edge  y x ).  apply BGe3.
       generalize F12. rewrite <- Couple_comm.  tauto. tauto.
       intro. symmetry. tauto.  }                   

     assert (F9:  Is_largest_antichain_in  P R) .
    {  Print Is_largest_antichain_in. apply largest_antichain_cond.
         auto. 
         intros A n1 n0 T1 T2 T3.
         assert (Tn: n = n1).
         { eapply cardinal_unicity. exact F7.  tauto. }
         rewrite <- Tn in T2. rewrite <- Tn. clear T2.

         pose (AL:= Intersection _ A L).
         pose (AR:= Intersection _ A R).

         assert (T4: Disjoint _ AL AR).
         { apply Disjoint_intro. intros x T4.
           destruct T4 as [x Ta4 T4]. 
           assert (T5: In _ L x /\ In _ R x). unfold AL in Ta4. unfold AR in T4.
           destruct Ta4. destruct T4.  tauto.
           assert (T6: In _ (Intersection _ L R) x).
           { apply Intersection_intro; tauto. }
           assert (Ta6: Disjoint _ L R ). { auto with BG. }
           absurd (In U ( Intersection U L R) x). destruct Ta6. apply H0.  auto.  }
         
         assert (T5: Finite _ AL /\ Finite _ AR).
         { split.
           apply Finite_downward_closed with (A:= L).
           auto with BG. unfold AL. auto with sets.
           apply Finite_downward_closed with (A:= R).
           auto with BG. unfold AR. auto with sets.  } 

         
         assert (T6: exists ln0: nat, cardinal _ AL ln0 ).
         { apply finite_cardinal.  tauto.  } destruct T6 as [ln0 T6].
         assert (T7: exists rn0: nat, cardinal _ AR rn0 ).
         { apply finite_cardinal.  tauto. } destruct T7 as [rn0 T7].
         clear T5. 

         assert (T0: A = Union _ AL AR).
         { apply Extensionality_Ensembles.
           unfold Same_set.
           split.
           { unfold Included. intros x. intro.
             assert ( H1: In _ C x).
             { destruct T1. destruct H1. simpl in H1. auto.  }
             unfold C in H1.
             destruct H1. apply Union_introl. unfold AL. auto with sets.
             apply Union_intror. unfold AR. auto with sets. }
           { unfold Included.  intro x. intro. destruct H0.
             unfold AL in H0. destruct H0.  tauto.
             unfold AR in H0. destruct H0.  tauto. }   } 
         
         assert (T: ln0 + rn0 = n0 ).
         { assert (Temp: cardinal _ A (ln0 + rn0) ).
           rewrite T0. eapply Disjoint_card. tauto.
           eapply cardinal_unicity. exact Temp. auto.  } 

         assert (T8: exists ln0': nat, cardinal _ (N AL) ln0' ).
         { assert (Temp: Finite _ (N AL)).
           {  assert(Included _ (N AL) R ).
              { unfold Included. intros x Temp. destruct Temp.
                destruct H0. cut (In _ L x0 /\ In _ R x ).
                tauto. auto with BG. }
              
              eapply Finite_downward_closed with (A:=R).  auto with BG.
              tauto. }
           apply finite_cardinal. auto.   }
         destruct T8 as [ ln0' T8]. 

         assert ( T9: ln0 + rn0 <= ln0' + rn0). 
         { assert (Temp: ln0 <= ln0').
           { eapply H with (S:= AL).
             unfold AL. auto with sets. tauto.  }
           omega.  } 

         pose (TS:= Union _ AR (N AL)).

         assert (T10: Included _ TS R).
         {   unfold TS.
             assert(Temp1: Included _ (N AL) R ).
              { unfold Included. intros x Temp. destruct Temp.
                destruct H0. cut (In _ L x0 /\ In _ R x ).
                tauto. auto with BG. }
              assert (Temp2: Included _ AR R).
              {  unfold AR. auto with sets.  }
              auto with sets.  }

         assert (Ta10: Disjoint _ AR (N AL)).
         { Print Disjoint. apply Disjoint_intro.
           intros x Temp. destruct Temp as [y H0 H1]. unfold In in H1.
           unfold N in H1. destruct H1 as [x H1].

           assert ( Temp: In _ R y).
           { destruct H1. eauto with BG. }

           assert (Temp1: In _ L x).
           { destruct H1. eauto with BG. }

           assert (Temp2: x<>y).
           { intro Temp3. absurd (In _ R x).  destruct H1.  generalize H2. EdgeThm.
             rewrite Temp3. tauto. }

           assert (Temp3: Rel x y).
           { unfold Rel. left. tauto. }
           destruct T1.

           assert (H4: Included _ (Couple _ x y) A).
           { rewrite T0. unfold Included. intros x0 Temp4.
             destruct Temp4. apply Union_introl. tauto. apply Union_intror. tauto. }

           assert (Temp4: x =y).
           { eapply H3. tauto. left. simpl. tauto. }

           absurd (x=y). tauto. tauto. } 
             

         assert (T11: cardinal _ TS (rn0 + ln0')).
         { unfold TS.  eapply Disjoint_card. tauto. }

         assert ( T12: ln0' + rn0 <= n).
         { eapply incl_card_le with (U:= U) (X:=TS).
           assert (Temp: ln0' + rn0 = rn0 + ln0').
           { auto with arith. } rewrite Temp. auto. exact F7.
           auto.  } 

         assert (Temp: n0 <= ln0' + rn0).
         { rewrite <- T.  auto. }

         eauto with arith.     
       

    }

    

    assert (Fb9:  (exists (cv: Ensemble (Ensemble U)), Is_a_chain_cover  P cv /\
                                                  cardinal _ cv n)).
    { apply DilworthB with (P:= P). exists R. tauto. }

    assert (FS:  exists cv : Ensemble (Ensemble U), Is_a_smallest_chain_cover  P cv /\
                                               cardinal (Ensemble U) cv n).
    { destruct Fb9 as [cv H0]. exists cv. split. Print Is_a_smallest_chain_cover.
      apply smallest_cover_cond.
      { tauto. }
      { intros.  destruct H1. destruct H2.
        assert (sn = n).
        { eapply cardinal_unicity with (X:= cv). auto.  tauto. }
        rewrite H4.
        assert (~ n > n0).
        { eapply DilworthA with (P:=P)(cv:= cover)(a:= R). auto.  auto. auto. auto. }
        assert ( (~n<= n0) <-> n >n0 ).
        { Check nat_P5. eapply nat_P5. }
        destruct H6. elim (classic (n<= n0)). tauto.
        intro. absurd (n>n0). auto. auto.   }
      { apply H0. } } 

    assert (F10: (exists cv': Ensemble (Ensemble U), Is_a_disjoint_cover  P cv' /\ cardinal _ cv' n)).
    { apply exists_disjoint_cover. auto.  }

    destruct F10 as [cover F10]. destruct F10 as [F10 F11].  destruct F10 as [F10 Fb10].
    destruct F10 as [F10 Fa10].

    (* Properties of chain cover *)

    (* No two element from L can lie in a chain from cover *)
    assert (HC: forall (x y : U) (c: Ensemble U), In _ cover c -> 
               (In _ L x /\ In _ L y /\ In _ c x /\ In _ c y) -> x = y).
    { intros x y c T1 T2. eapply NoTwoCommon with (P:= P) (X:= c) (Y:= L).  apply F10.
      auto.  auto.  intros x0 T3; destruct T3;tauto. intros x0 T3; destruct T3;tauto.  }
     (* No two element from R can lie in a chain from cover *)
     assert (HC0: forall (x y : U) (c: Ensemble U), In _ cover c ->
                (In _ R x /\ In _ R y /\ In _ c x /\ In _ c y) -> x = y).
    { intros x y c T1 T2. eapply NoTwoCommon with (P:= P) (X:= c) (Y:= R).  apply F10.
      auto.  auto.  intros x0 T3; destruct T3;tauto. intros x0 T3; destruct T3;tauto. } 


    (* Every element from R lies on some chain from cover *)
    assert (HCa1: forall x: U, In _ R x -> (exists chain: Ensemble U, In _ cover chain /\ In _ chain x)).
    { intros x Temp. eapply Fa10. simpl.  unfold C. apply Union_intror. auto.  } 

    (* Every chain from cover has one element from R *) 
    assert (HC1: forall chain: Ensemble U, In _ cover chain -> (exists y:U, In _ R y /\ In _ chain y)).
    { eapply Bijection_Relation. auto.
      intros x y b T. eapply HC0 with (c:= b). tauto.  tauto. exact F7. tauto. } 

    (* Every element from L lies on some chain from cover *)
    assert (HC2: forall x: U, In _ L x -> (exists chain: Ensemble U, In _ cover chain /\ In _ chain x)).
    { intros x Temp. eapply Fa10. simpl.  unfold C. apply Union_introl. auto. }

    (* For every element in L there is a chain from cover and an element from R such that
       both lies on the chain  *)
    assert (HC3: forall x: U, In _ L x -> (exists (chain: Ensemble U)(y: U), In _ cover chain /\ In _ R y /\
                                                                  In _ chain x /\ In _ chain y)).
    { intros x T.
      assert (T1:  exists chain : Ensemble U, In (Ensemble U) cover chain /\ In U chain x).
      { eauto. } destruct T1 as [chain T1].
      exists chain.
      assert (T2:  exists y : U, In U R y /\ In U chain y).
      { apply HC1. tauto.  } destruct T2 as [y T2].
      exists y. tauto. } 

    pose (Rel' (x:U)(y:U) := exists c: Ensemble U, (In _ cover c /\ In _ L x /\ In _ R y) /\
                                              In _ c x /\ In _ c y /\ x <> y ). 

    exists Rel'.

    (* We need to prove that Rel' is included in Edge Relation *) 
    assert (HR1: Included_in_Edge Rel' ).
    { unfold Included_in_Edge. intros x y T1. unfold Rel' in T1.
      destruct T1 as [c T1].

      assert ( T2: Is_a_chain_in P c).
      { eapply F10. tauto. }
      assert (T3: Included _ (Couple _ x y) c ).
      { unfold Included.  intros x0 T. destruct T; tauto. }
      destruct T2.
      assert (T4: Rel x y \/ Rel y x).
      { auto. }
      unfold Rel in T4.
      assert (T5: Edge x y \/ Edge y x).
      { elim T4.
        { intro T6; left. elim T6. {trivial. }
                                   { intro T7. absurd (x=y);tauto.  } }
        { intro T6; right. elim T6. {trivial. }
            { intro T7. absurd (x=y). tauto.   symmetry. auto. } }
        } 

      elim T5.
      { trivial. } { intro T6. absurd ( In _ R y). (* eapply BGb3 *) EdgeThm . exact T6. tauto. } }  


    (* Now we prove that Rel' is L_Perfect *)
    assert (HR2: Is_L_Perfect Rel' ).
    { unfold Is_L_Perfect.
      split.
      (* We prove that Rel' is a matching *)
      { unfold Is_a_matching. intros x y z.  intro HR.
        elim HR.
        { intro Hra.  destruct Hra as [Hra Hrb].
          unfold Rel' in Hra. unfold Rel' in  Hrb.
          destruct Hra as [c1 Hra]. destruct Hrb as [c2 Hrb].
          Print Disjoint.
          assert (c1 = c2 \/ Disjoint _ c1 c2).
          { eapply Fb10. tauto. }
           elim H0.
          { intro. eapply NoTwoCommon with (X:= c1) (P:=P)(Y:=L). apply F10. tauto. auto.
            unfold Included. intros. destruct H2. tauto. rewrite H1. tauto.
            unfold Included. intros. destruct H2. tauto.  tauto. }
          intro. 
          absurd ( Disjoint _ c1 c2).
            intro T.  destruct T.
            absurd ( In U (Intersection U c1 c2) z).
            auto. apply Intersection_intro; tauto.
            tauto.  } 

        { intro Hra.  destruct Hra as [Hra Hrb].
          unfold Rel' in Hra. unfold Rel' in  Hrb.
          destruct Hra as [c1 Hra]. destruct Hrb as [c2 Hrb].
          Print Disjoint.
          assert (c1 = c2 \/ Disjoint _ c1 c2).
          { eapply Fb10. tauto. }
           elim H0.
          { intro. eapply NoTwoCommon with (X:= c1) (P:=P)(Y:=R). apply F10. tauto. auto.
            unfold Included. intros. destruct H2. tauto. rewrite H1. tauto.
            unfold Included. intros. destruct H2. tauto.  tauto. } 
          intro. 
          absurd (Disjoint _ c1 c2).
            intro T.  destruct T.
            absurd ( In U (Intersection U c1 c2) z).
            auto. apply Intersection_intro; tauto.
            tauto. } }
      
      
      (* We prove that for every x in L there is a y in R such that Rel' x y *)
      { intros x HL.
        assert( HL1: exists (chain : Ensemble U) (y : U),
                  In (Ensemble U) cover chain /\ In U R y /\ In U chain x /\ In U chain y).
        { apply HC3. auto. } destruct HL1 as [chain HL1]. destruct HL1 as [y HL1].
        exists y. exists chain.
        split. { tauto. }
               { split. tauto. split. tauto. intro T.
                 absurd (Disjoint _ L R). { intro T1. destruct T1.
                 absurd ( In _ (Intersection _ L R) x). auto.
                 apply Intersection_intro. tauto. rewrite T. tauto. }
                                          { auto with BG. } }   }  }

    tauto.          }   Qed.

  
  Theorem Halls_Thm:  (forall (S: Ensemble U),
                 Included _ S L -> (forall m n :nat, (cardinal _ S m /\ cardinal _ (N S) n) -> m <=n ) ) <->
                      ( exists Rel': Relation U, Included_in_Edge Rel' /\ Is_L_Perfect Rel').
    Proof.  unfold iff.  split; ( eapply Hall_A ||  eapply Hall_B) . Qed. 

  
End Halls_Thm.


