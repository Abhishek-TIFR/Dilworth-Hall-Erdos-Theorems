(* This File contains the proof of Mirsky's Theorem which is named Dual_Dilworth 
   in this file. Mirsky's theorem relates the size of an antichain cover and a 
   chain in a poset.It states that in any poset the maximum size of a chain is 
   equal to the minimum number of antichains in any antichain cover. In other words,
   if c(P) represents the size of a smallest antichain cover of P,
   then height(P)=c(P). Here height(P) represents the size of longest chain in P. 
   
   MAIN THEOREM: 

   Definition Dual_Dilworth_statement:=  fun (P: FPO U)=>
     forall (m n: nat), (Is_height P m) ->
            (exists cover: Ensemble (Ensemble U),
            (Is_a_smallest_antichain_cover P cover)/\ (cardinal _ cover n))-> m=n.
  

    Theorem Dual_Dilworth: forall (P: FPO U), Dual_Dilworth_statement P.  *)


Require Export Combi_1.
Require Export BasicFacts2.
Require Export FPO_Facts3.


Section Dual_Dilworth.

  

  Variable U:Type.

  Definition Dual_DilworthA_statement:=
  fun (P: FPO U)=> forall (n m : nat)(cv: Ensemble (Ensemble U))(c: Ensemble U),
               Is_an_antichain_cover P cv -> Is_a_chain_in P c ->        
               cardinal _  cv n -> cardinal _  c m ->
               ~(m > n).

  Theorem Dual_DilworthA: forall (P: FPO U), Dual_DilworthA_statement P.
  Proof. {
        intro P. unfold Dual_DilworthA_statement.
        intros n m cv lc. intros.  intro.
        pose (R:= fun (x:U) (y: Ensemble U) => In _ y x).
        assert (H4: (exists (x y: U) (z: Ensemble U) ,
                        In _ lc x /\ In _ lc y /\ In _ cv z /\ x<>y /\ (R x z /\ R y z))).
        { apply Pigeon_Relation with
          (U:= U) (V:= Ensemble U) (A:= lc) (B:= cv) (R:=R) (m:=n) (n:=m).
          { destruct H.  intro x. intro. unfold R. apply H4. apply H0. tauto. }
          { auto. }
          { auto. }
          { auto. }
        }

        destruct H4 as [x H4]. destruct H4 as [y H4]. destruct H4 as [anti_chain H4].
        destruct H4 as [ H4a H4]. destruct H4 as [ H4b H4]. destruct H4 as [ H4c H4].
        destruct H4 as [ H4d H4]. unfold R in H4.
        assert (H5: Is_an_antichain_in P anti_chain). { destruct H. apply H. auto. }
        assert (H6: x = y). { apply NoTwoCommon with (P:= P)(X:=lc)(Y:= anti_chain).
          auto. auto. unfold Included; intros; destruct H6; tauto.
          unfold Included; intros; destruct H6; tauto. }
        absurd (x=y);tauto.  }  Qed.

  Lemma Union_setminus1: forall (L C: Ensemble U), Included U L C -> C = Union U (Setminus U C L) L.
  Proof. { intros. unfold_equal.
           { unfold Included. intros. elim (classic (In _ L x)). auto with sets.
             intro. apply Union_introl. auto with sets. }
           {  unfold Included. destruct 1. apply H0. auto with sets. } } Qed. 

  Hint Resolve Union_setminus1: sets0.
  Hint Resolve PO_cond1 PO_cond2 FPO_cond: fpo.
  Hint Resolve Finite_downward_closed finite_cardinal cardinal_unicity : sets0. 
Lemma Largest_chain_P1: forall (P: FPO U) (c e: Ensemble U),
             Is_largest_chain_in P c -> Strict_Included _ c e -> ~ Is_a_chain_in P e.
Proof. { intros. intro. destruct H.
         assert (Finite _ e). cut (Included _ e (Carrier_of _ P)).
         intro. assert (Finite _ (Carrier_of _ P)). auto with fpo.
         eauto with sets0. apply H1.
         assert (exists n1:nat, cardinal _ e n1).
         { auto with sets0. } destruct H4 as [n1 H4].
         assert ( exists n:nat, cardinal _ c n).
         { cut (Finite _ c). auto with sets0.
         cut (Included _ c (Carrier_of _ P)). intro.
         assert (Finite _ (Carrier_of _ P)).  auto with fpo.
         eauto with sets0. apply H. } destruct H5 as [n H5].
         absurd (n1<=n).
         { cut (n1 > n). omega. eapply incl_st_card_lt;eauto. }
         eauto. } Qed.


 Lemma Card_same_largest1
     : forall (U : Type) (FP : FPO U) (e1 e2 : Ensemble U) (n : nat),
       Is_largest_chain_in FP e1 ->
       Is_a_chain_in FP e2 ->
       cardinal U e1 n -> cardinal U e2 n -> Is_largest_chain_in FP e2.
 Proof. { intros. apply_fpo_def. auto.  intros.
        cut( n0= n). intro. rewrite H6.  eapply H;eauto. eauto with sets0. }  Qed. 

 Hint Resolve Card_same_largest1: fpo.
 Print PO.

 
 

Lemma Chains_maximal: forall (P: FPO U)(c: Ensemble U),
     Is_a_chain_in P c -> exists max: U, In _ c max /\ (forall y: U, In _ c y -> Rel_of _ P y max).
Proof. { intros.
         pose (C:= c).
         pose (R:= Rel_of _ P).
         Print PO.
         assert (H1: Inhabited _ C).
         { unfold C;apply H. }
         assert (H2: Order _ R).
         { unfold R; auto with fpo. }
         Print PO.

         pose ( P_C:=  {| Carrier_of := C;
                        Rel_of := R;
                        PO_cond1 := H1;
                        PO_cond2 := H2 |}).
         Print FPO.
         assert (Finite_C: Finite _ C).
         { cut (Finite _ (Carrier_of _ P)).
         cut (Included _ C (Carrier_of _ P)).
         eauto with sets0. unfold C; apply H. auto with fpo. }
       
         pose (FP:= {| PO_of:= P_C; FPO_cond:= Finite_C |}).

         assert ( exists x: U, Is_the_largest_element_in FP x).
         { cut (Totally_ordered _ FP c). auto with fpo.
         Print Totally_ordered. apply Totally_ordered_definition.
         intros. destruct H. apply H4. auto. }
         destruct H0 as [max H0]. exists max. split. apply H0.
         intros. destruct H0. apply H4. simpl. auto. } Qed. 

Lemma Chains_minimal: forall (P: FPO U)(c: Ensemble U),
     Is_a_chain_in P c -> exists min: U, In _ c min /\ (forall y: U, In _ c y -> Rel_of _ P  min y).
Proof.  { intros.
         pose (C:= c).
         pose (R:= Rel_of _ P).
         Print PO.
         assert (H1: Inhabited _ C).
         { unfold C;apply H. }
         assert (H2: Order _ R).
         { unfold R; auto with fpo. }
         Print PO.

         pose ( P_C:=  {| Carrier_of := C;
                        Rel_of := R;
                        PO_cond1 := H1;
                        PO_cond2 := H2 |}).
         Print FPO.
         assert (Finite_C: Finite _ C).
         { cut (Finite _ (Carrier_of _ P)).
         cut (Included _ C (Carrier_of _ P)).
         eauto with sets0. unfold C; apply H. auto with fpo. }
       
         pose (FP:= {| PO_of:= P_C; FPO_cond:= Finite_C |}).

         assert ( exists x: U, Is_the_smallest_element_in FP x).
         { cut (Totally_ordered _ FP c). auto with fpo.
         Print Totally_ordered. apply Totally_ordered_definition.
         intros. destruct H. apply H4. auto. }
         destruct H0 as [min H0]. exists min. split. apply H0.
         intros. destruct H0. apply H4. simpl. auto. } Qed. 


  Lemma Largest_chain_has_maximal: forall (P: FPO U)(lc: Ensemble U),
    Is_largest_chain_in P lc -> exists common:U, In _ lc common /\ In _ (Maximal_elements_of P) common.
  Proof. { intros.
           assert( exists max: U, In _ lc max /\ (forall y: U, In _ lc y -> Rel_of _ P y max)).
           { apply Chains_maximal. apply H. }
           destruct H0 as [max H0].
           assert (F0: Order _ (Rel_of _ P)).
           { auto with fpo. } destruct F0 as [F0 F1].
           exists max. split. apply H0.
           elim (classic ( In U (Maximal_elements_of P) max )).
           {tauto. }
           { intro.
             assert (In U (Carrier_of U P) max).
             { repeat destruct H. destruct H0. auto with sets. } 
             assert (exists y : U, Is_a_maximal_element P y /\ Rel_of U P max y).
             { apply Maximal_for_every_x. auto.  }
             destruct H4 as [y H4].
             assert (y<> max).
             { intro. absurd (In U (Maximal_elements_of P) max). auto.
               unfold In. unfold Maximal_elements_of. rewrite <- H5. tauto. }
             assert (~ In _ lc y).
             { intro. apply H5. apply H1. apply H0. tauto. apply H4. }
             pose (lc1:= Add _ lc y).
             assert ( Strict_Included _ lc lc1).
             { unfold Strict_Included.  split. unfold lc1. auto with sets.
               intro. absurd (In U lc y). apply H6. rewrite H7. unfold lc1.
               auto with sets.  } 
             assert (Is_a_chain_in P lc1 ).
             { unfold Is_a_chain_in.
               split. split. unfold lc1. cut( Included _ lc (Carrier_of U P)).
               cut (In _ (Carrier_of U P) y). intros. unfold Included.
               destruct 1. auto with sets. destruct H10. auto. apply H4. apply H.
               apply Inhabited_intro with (x:= y). unfold lc1; auto with sets.

               unfold lc1. intros.
               assert (In _ (Add _ lc y) x /\ In _ (Add _ lc y) y0 ).
               split.  auto with sets. auto with sets. destruct H9.
               destruct H9;destruct H10.
               { repeat destruct H. apply H12. unfold Included. destruct 1;tauto.  }
               { destruct H10. left. eapply F1 with (y:=max). apply H0;auto. tauto. }
               { destruct H9. right. eapply F1 with (y:=max). apply H0;auto. tauto. }
               { destruct H9; destruct H10. left. apply F0. }  }
             absurd (Is_a_chain_in P lc1).
             eapply  Largest_chain_P1. apply H. auto. auto.  } } Qed. 
  

  Lemma Largest_chain_has_minimal: forall (P: FPO U)(lc: Ensemble U),
    Is_largest_chain_in P lc -> exists common:U, In _ lc common /\ In _ (Minimal_elements_of P) common.
  Proof.  { intros.
           assert( exists min: U, In _ lc min /\ (forall y: U, In _ lc y -> Rel_of _ P min y )).
           { apply Chains_minimal. apply H. }
           destruct H0 as [min H0].
           assert (F0: Order _ (Rel_of _ P)).
           { auto with fpo. } destruct F0 as [F0 F1].
           exists min. split. apply H0.
           elim (classic ( In U (Minimal_elements_of P) min )).
           {tauto. }
           { intro.
             assert (In U (Carrier_of U P) min).
             { repeat destruct H. destruct H0. auto with sets. } 
             assert (exists y : U, Is_a_minimal_element P y /\ Rel_of U P y min).
             { apply Minimal_for_every_y. auto.  }
             destruct H4 as [y H4].
             assert (y<> min).
             { intro. absurd (In U (Minimal_elements_of P) min). auto.
               unfold In. unfold Minimal_elements_of. rewrite <- H5. tauto. }
             assert (~ In _ lc y).
             { intro. apply H5. apply H1. apply H4. apply H0. tauto.  }
             pose (lc1:= Add _ lc y).
             assert ( Strict_Included _ lc lc1).
             { unfold Strict_Included.  split. unfold lc1. auto with sets.
               intro. absurd (In U lc y). apply H6. rewrite H7. unfold lc1.
               auto with sets.  } 
             assert (Is_a_chain_in P lc1 ).
             { unfold Is_a_chain_in.
               split. split. unfold lc1. cut( Included _ lc (Carrier_of U P)).
               cut (In _ (Carrier_of U P) y). intros. unfold Included.
               destruct 1. auto with sets. destruct H10. auto. apply H4. apply H.
               apply Inhabited_intro with (x:= y). unfold lc1; auto with sets.

               unfold lc1. intros.
               assert (In _ (Add _ lc y) x /\ In _ (Add _ lc y) y0 ).
               split.  auto with sets. auto with sets. destruct H9.
               destruct H9;destruct H10.
               { repeat destruct H. apply H12. unfold Included. destruct 1;tauto.  }
               { destruct H10. right. eapply F1 with (y:=min). apply H4;auto. apply H0. tauto. }
               { destruct H9. left. eapply F1 with (y:=min). apply H4. apply H0;auto.  }
               { destruct H9; destruct H10. left. apply F0. }  }
             absurd (Is_a_chain_in P lc1).
             eapply  Largest_chain_P1. apply H. auto. auto.  } } Qed.  

  
                                                                 
  Definition Dual_DilworthB_statement:= fun (P: FPO U)=> forall (m: nat),
                 (exists (lc: Ensemble U ), Is_largest_chain_in P lc /\ cardinal _  lc m) ->
                 (exists (cv: Ensemble (Ensemble U)), Is_an_antichain_cover P cv /\
                      cardinal _ cv m). 


  Theorem Dual_DilworthB: forall (P: FPO U), Dual_DilworthB_statement P.
  Proof. { unfold Dual_DilworthB_statement. intros P0 m; generalize P0 as P; clear P0.
         (* We will prove this result using Induction on m *)
           induction m.
         (* Case when m =0 Trivial : no chain of length 0 possible *)
         { intros. repeat (destruct H).
           absurd (x = Empty_set U). auto with sets. apply cardinal_elim in H0. tauto. }
         (* Case when S m : we will again destruct m hence will get two cases *)
         
         { intros. destruct H as [lc H]. destruct H.

           pose (L:= Maximal_elements_of  P).
           pose (C:= Carrier_of _ P). pose (R:= Rel_of _ P).

           assert( Common: exists a: U, In _ lc a /\ In _ L a).
           { eapply Largest_chain_has_maximal. auto.  }
           
           destruct Common as [a Common].
           pose ( lc_a := Subtract _ lc a).
           assert (Flc_a1: lc = Add _ lc_a a).
           { unfold lc_a. destruct Common. auto with sets. }
           assert (Flc_a2: Included _ lc_a lc).
           { rewrite Flc_a1. auto with sets. }

           pose (C0:= Setminus _ C L).
           assert (FL: Is_an_antichain_in P L).
           { unfold L. auto with fpo. }
           assert (F0: Included _ L C).
           { apply FL.  }
           assert (F1: C = Union _ C0 L).
           { unfold C0. auto with sets0.  }

           elim (classic (Inhabited _ C0)).
           (* Non Trivial: when C <> L: when C0 is not empty *)
           { intro.
             assert (exists x:U, In _ C x /\ ~ In _ L x).
             { unfold C0 in H1. destruct H1. exists x. apply H1. }
             destruct H2 as [x0 H2]. Check Maximal_for_every_x.
             assert ( exists y : U, In _ L y /\ R x0 y).
             { unfold In. unfold L. destruct H2. unfold R. auto with fpo. }
             destruct H3 as [y H3].
             pose (chain := Couple _ x0 y ).
             assert (x0<>y).
             { intro. absurd (In _ L x0). apply H2. rewrite H4. apply H3. }

             assert (cardinal _ chain 2).
             { unfold chain. auto with card0. }

             assert ( Is_a_chain_in P chain).
             { unfold Is_a_chain_in. split. split.
               unfold chain. unfold Included. destruct 1. apply H2.
               cut (Included _ L C). intro. apply H6. apply H3.
               cut (Is_an_antichain_in P L). intro. apply H6.
               unfold L. auto with fpo. unfold chain.
               apply Inhabited_intro with (x:= x0). auto with sets.
               intros.
               assert (In _ chain x /\ In _ chain y0).
               { split. apply H6. auto with sets. apply H6. auto with sets. }
               destruct H7.
               assert (Order _ R). Print PO. apply PO_cond2. 
               destruct H7; destruct H8. left; apply H9.
               left; apply H3. right; apply H3. left; apply H9.  }

             
             destruct m.
             (* Case : when the size of lc is 1 *)
             { destruct H.
               assert (2<=1). eapply H7 with (e1:=chain).  auto. auto. auto.
               inversion H8.  inversion H10. }

             (* Case : when the size of lc is (S S m) : greater than 1 *)
             {   assert (cardinal _ lc_a (S m)).
                  { unfold lc_a. auto_with_card0. apply Common. auto. }
                 assert (H_Inhabited: Inhabited _ (Setminus _ C L ) ).
                 { apply H1.  }
                 assert (H_Finite: Finite _ C0).
                 { cut (Included _ C0 C).  
                   auto_with_sets0. apply FPO_cond.  unfold C0.
                   auto_with_sets0.  }
                 pose ( P_small0 := {|  Carrier_of := C0; Rel_of := Rel_of _ P ;
                            PO_cond1:= H1; PO_cond2:= PO_cond2 _ P |} ).
                 Print FPO. 
                 pose (P_small := {|PO_of := P_small0 ; FPO_cond:= H_Finite |}).

                 assert (HInc: Included_in _ P P_small).
                 { unfold Included_in. split.
                   simpl. unfold C0. unfold C. auto with sets0. simpl. tauto.  }

                 assert (HInc_lc: Included U lc_a C0).
                 { unfold lc_a. unfold C0. unfold Included. unfold In.
                   unfold Subtract. unfold Setminus. intros. destruct H8.
                   split.
                   assert (Included _ lc C).
                   {unfold C. apply H.  }
                   auto with sets.
                   intro. apply H9. replace a with x. auto with sets.
                   eapply NoTwoCommon with (P:=P)(X:=lc)(Y:=L).
                   apply H. auto.
                   unfold Included. destruct 1;tauto.
                   unfold Included. destruct 1;tauto. } 

                 assert ( Is_largest_chain_in P_small lc_a).
                 { apply_fpo_def.
                   { unfold Is_a_chain_in. simpl.
                     split. split. tauto.
                     eapply cardinal_elim with (p:= S m);tauto.
                     intros.
                     cut (Included U (Couple U x y0) lc).
                     intros. repeat destruct H. eapply H11;tauto.  auto with sets. } 
                   { intro e. intros.
                     assert (n= S m). eauto with card0.
                     elim (classic (n1<= n)). tauto. rewrite H11.
                     intro.
                     assert (n1> S m). omega.
                     assert (Is_a_chain_in P e ).
                     { eapply Chain_remains1. eauto. auto. }
                     assert (n1<= S (S m) /\ n1 >= S (S m)).
                     { split. destruct H. eapply H15. exact H14. tauto. tauto. apply H13. }
                     assert (n1= S (S m)).
                     { omega. }
                     assert (Is_largest_chain_in P e ).
                     { rewrite H16 in H10. eauto with fpo. }
                     assert (exists a0: U, In U e a0 /\ In U L a0).
                     { unfold L. apply Largest_chain_has_maximal. auto. }
                     destruct H18 as [a0 H18].
                     assert (In _ C0 a0).
                     { cut (Included _ e C0). destruct H18. auto with sets.
                       apply H8.  }
                     unfold C0 in H19.
                     absurd (In _ L a0). apply H19. apply H18. }  }

                 assert ( exists cv0 : Ensemble (Ensemble U),
                            Is_an_antichain_cover P_small cv0 /\ cardinal (Ensemble U) cv0 (S m)).
                 { apply IHm. exists lc_a. tauto. } destruct H9 as [cv0 H9].

                 pose (cv:= Add _ cv0 L).
                 assert ( ~ In (Ensemble U) cv0 L).
                 { intro.
                   assert (Included _ L C0).
                   { repeat destruct H9. cut (Is_an_antichain_in P_small L).
                     intro.  apply H13. apply H9. auto. } 
                   unfold C0 in H11. unfold Included in H11.
                   absurd (In U L y). cut (In U (Setminus U C L) y).
                   unfold In at 1. unfold Setminus. tauto. apply H11. apply H3. apply H3. }
                 
                 assert (cardinal _ cv (S (S m))).
                 { unfold cv. apply card_add. apply H9. auto. }
                 repeat destruct H9.

                 exists cv. split.
                 apply_fpo_def.
                 { unfold cv. destruct 1.
                   cut (Is_an_antichain_in P_small x). intro.
                   eapply Antichain_remains2. eauto. apply H15. auto.
                   apply H9. auto. destruct H14. auto. }
                 { replace (Carrier_of U P) with C. rewrite F1.
                   intros. destruct H14. unfold cv.
                   cut (exists e : Ensemble U, In (Ensemble U) cv0 e /\ In U e x).
                   intro. destruct H15 as [e H15]. destruct H15.
                   exists e. split. auto with sets. tauto. apply H13. apply H14.
                   exists L. unfold cv. split. auto with sets. auto. unfold C. tauto.  } 
                 { tauto. }  }  }

           
           (* Trivial: when C = L  *)
           { intro.
             assert ( Included _ C L).
             { unfold C0 in H1. unfold Included. intros.
               elim (EM (In U L x)). tauto. intro.
               absurd (Inhabited _ (Setminus U C L)). tauto.
               Print Inhabited. apply Inhabited_intro with (x:=x). auto with sets. }
             exists (Singleton _ L).
             split.
             { Print Is_an_antichain_cover. eapply AC_cover_cond.
               intro. destruct 1. unfold L. auto with fpo.
               intros. exists L. split. auto with sets. auto with sets. }
             destruct m.
             { auto with card0.  }
             { assert (cardinal _ lc_a (S m)).
               { unfold lc_a. auto_with_card0. apply Common. auto. }
               eapply cardinal_elim with (p:= S m) in H3 as H4.
               destruct H4.
               assert (x<>a).
               { intro. rewrite H5 in H4. unfold lc_a in H4. destruct H4.
                 apply H6. auto with sets. }
               absurd (x=a). tauto. eapply NoTwoCommon with (P:=P)(X:=lc)(Y:=L).
               { apply H. }
               { unfold L. auto with fpo. }
               { unfold Included. destruct 1. apply H4. apply Common. }
               { unfold Included. destruct 1. apply H2.
                 repeat destruct H. apply H. apply H4. apply Common.  }  }  }   }
         } Qed. 

         

        




  (* ______________________________MAIN THEOREM_________________________________________ *)

 

 Definition Dual_Dilworth_statement:=  fun (P: FPO U)=>
     forall (m n: nat), (Is_height P m) ->
                 (exists cover: Ensemble (Ensemble U),
                     (Is_a_smallest_antichain_cover P cover)/\ (cardinal _ cover n)) ->
                  m=n.
  

 Theorem Dual_Dilworth: forall (P: FPO U), Dual_Dilworth_statement P.

 Proof.  { intro P. unfold Dual_Dilworth_statement. intros m n. intros.
            destruct H. destruct H as [lc H]. destruct H0 as [cover H0].
            
            (* We prove that there is an antichain cover of size m using Dual_DilworthB *)
            assert (H1:  (exists (cv: Ensemble (Ensemble U)), Is_an_antichain_cover P cv /\
                                                      cardinal _ cv m)).
            { apply (Dual_DilworthB  P ).  exists lc.  auto. }
            (* Hence n<= m, since n is the size of smallest chain cover *)
            assert (H2: n<= m ).
            { destruct H1 as [cv H1].
             destruct H0 as [H_cover H0].
             destruct H_cover . 
             apply H3 with ( cover0:= cv) ( sn:= n) (n:= m). tauto.
            }
            (* We prove n>=m or ~ (n<m) using Dual_DilworthA *)
             assert (H3: n>= m).
              { apply nat_P1. apply ( Dual_DilworthA  P) with (cv:= cover) (c:= lc).
                apply H0.  apply H. tauto.  tauto. } 
           (* Hemce combining H2 and H3 we have m=n  *)
           auto with arith.  }   Qed.
        


End Dual_Dilworth.

