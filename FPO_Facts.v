
  
(* This file contains  DEFINITIONS of some basic notions related to Finite Partial Orders.
     It also contains some elementary RESULTS on Chains, antichains and finite posets. Following 
     is a partial list of these definitions and results. 


DEFINITIONS: ---------------------------------------------------------------------------
  1. Record FPO: Defines the notion of Finite Partial orders.
  
  2. Is_a_chain_in: Defines a chain as a predicate.

  3. Is_an_antichain_in: Defines antichain as a predicate.

  4. Is_the_largest_element_in: Defines the largest element  of a finite poset. 
            
  5. Is_the_smallest_element_in: Defines the smallest element of a finite poset.                

  6. Is_a_chain_cover: Defines a chain cover of finite posets.    

  7. Is_an_antichain_cover: Defines an antichain cover of finite posets.

  8. Is_a_disjoint_cover: Defines the notion of a disjoint chain cover.    

RESULTS on finite posets: --------------------------------------------------------------

0.Lemma NoTwoCommon: A chain and an antichain intersects at atmost one point.

1.Lemma Antichain_exists: In every finite poset there is an antichain.

2.Lemma Chain_exists: In every finite poset there is a chain.

3.Lemma Minimal_element_exists: There exists a minimal element in every finite poset. 
        
4.Lemma Maximal_element_exists: There exists a maximal element in every finite poset.  
         
5.Lemma Minimal_for_every_y: In a finite poset for every element y there exists x such that R x y

6.Lemma Maximal_for_every_x: In a finite poset for every element x there exists y such that R x y

7.Lemma Largest_element_exists: In a totally ordered finite poset there exists a largest element.

8.Lemma Maximal_is_largest:In totally ordered finite posets Maximal element is largest element. 

9.Lemma Smallest_element_exists:In a totally ordered finite poset there exists a smallest element

----------------------------------------------------------------------------------------    *)  

Require Export PigeonHole.
Require Export BasicFacts.
Require Export Partial_Order .



Section Finite_Chain_Def.


  Variable U:Type.
  
  Check PO U.
  Print PO.
  Print Finite.

  Record FPO (U : Type) : Type := Definition_of_FPO
  { PO_of :> PO U ;
    
    FPO_cond : Finite _ (Carrier_of _ PO_of  ) }.
  
  Variable P :FPO U.
  Let C := @ Carrier_of U P.

  Let R := @Rel_of U P.

  Check FPO.
  Check Carrier_of _ P.

  Lemma Finite_PO: forall (P: FPO U), Finite _ (Carrier_of _ P).
  Proof. intro. apply FPO_cond. Qed.

  Set Implicit Arguments. 
  Definition Is_a_chain_in (e: Ensemble U): Prop:=
    (Included U e C /\ Inhabited U e)/\
                (forall x y:U, (Included U (Couple U x y) e)-> R x y \/ R y x). 
    



  Definition Is_an_antichain_in (e: Ensemble U): Prop := (Included U e C /\ Inhabited U e)/\
                (forall x y:U, (Included U (Couple U x y) e)-> (R x y \/ R y x)-> x=y). 



 Inductive Is_largest_chain_in (e: Ensemble U): Prop:=
   largest_chain_cond:  Is_a_chain_in e ->
                        (forall (e1: Ensemble U) (n n1:nat),
                        Is_a_chain_in e1 -> cardinal _ e n -> cardinal _ e1 n1 ->
                        n1<= n) -> Is_largest_chain_in e.

 Inductive Is_largest_antichain_in (e: Ensemble U): Prop:=
   largest_antichain_cond:  Is_an_antichain_in e ->
                            (forall (e1: Ensemble U) (n n1: nat),
                              Is_an_antichain_in e1 -> cardinal _ e n ->
                              cardinal _ e1 n1 -> n1<=n ) ->
                              Is_largest_antichain_in e.


                                                             


 (* ---------------------- MINIMAL AND MAXIMAL ARE ANTICHAINS ------------------------ *)
 (* ---------------------------------------------------------------------------------- *)
 

Definition Is_a_maximal_element (x:U): Prop:= In _ C x /\  ~(exists y:U, In _ C y /\ x<>y /\ R x y  ).
 


Definition Is_a_minimal_element (x: U): Prop:= In _ C x /\ ~(exists y:U, In _ C y /\ x<>y /\ R y x ). 



Definition Maximal_elements_of: Ensemble U:=
    fun x:U => Is_a_maximal_element x.

  

Definition Minimal_elements_of: Ensemble U:=
    fun x:U => Is_a_minimal_element x.


Definition Is_the_largest_element_in (U:Type)(FP: FPO U)(y:U): Prop:= let C0:= Carrier_of _ FP in let R0:= Rel_of _ FP in ( In _ C0 y /\ forall x:U, (In _ C0 x -> R0 x y) ).

Definition Is_the_smallest_element_in (U:Type)(FP: FPO U)(x:U): Prop:= let C0:= Carrier_of _ FP in let R0:= Rel_of _ FP in ( In _ C0 x /\ forall y:U, (In _ C0 y -> R0 x y) ). 



  (* _________________________ CHAIN COVER AND ANTICHAIN COVER ___________________________  *)
  

  Inductive Is_a_chain_cover (cover: Ensemble (Ensemble U)): Prop:=
    cover_cond: (forall (e: Ensemble U), In _ cover e -> Is_a_chain_in e)->
                (forall x:U, In _ C x -> (exists e: Ensemble U, In _ cover e /\ In _ e x)) ->
                Is_a_chain_cover cover.

  Inductive Is_an_antichain_cover (cover: Ensemble (Ensemble U)): Prop:=
    AC_cover_cond: (forall (e: Ensemble U), In _ cover e -> Is_an_antichain_in e)->
                (forall x:U, In _ C x -> (exists e: Ensemble U, In _ cover e /\ In _ e x)) ->
                Is_an_antichain_cover cover.



                                                               
  
  Lemma NoTwoCommon : forall (X Y : Ensemble U) (x y :U),
                        Is_a_chain_in X -> Is_an_antichain_in Y ->
                        Included U (Couple U x y) X -> Included U (Couple U x y) Y ->
                        x = y.

  Proof. { intros X Y x y. intros chainX antichainY H1 H2.
         assert (H:R x y \/ R y x ). destruct chainX. apply H0.
         assumption.
         destruct antichainY. apply H3.
         assumption. assumption. }  Qed.

 

  Definition Is_a_disjoint_cover (cover : Ensemble ( Ensemble U)): Prop:=
  Is_a_chain_cover  cover /\ (forall e1 e2 : Ensemble U,
                            (In _ cover e1 /\ In _ cover e2)-> (e1=e2 \/ Disjoint _ e1 e2 )).


  Unset Implicit Arguments.

                          

End Finite_Chain_Def.




 Ltac apply_fpo_def := match goal with
                        |_:_|- Is_largest_chain_in ?P ?e => (eapply largest_chain_cond)
                        |_:_ |- Is_largest_antichain_in ?P ?e => (eapply largest_antichain_cond)
                        |_:_ |- Is_a_chain_cover ?P ?cover => (eapply cover_cond)
                        |_:_ |- Is_an_antichain_cover ?P ?cover => (eapply AC_cover_cond)
                        end.
 


Section Finite_Chain_Facts.

  Variable U: Type.
  Variable FP: FPO U.

  Let C := @ Carrier_of U FP.

  Let R := @Rel_of U FP.

  Lemma Singleton_is_chain: forall x: U, In _ C x -> Is_a_chain_in FP (Singleton _ x).
  Proof. { intros. unfold Is_a_chain_in. split. 
              { split. unfold Included. intros. destruct H0. apply H.
                apply Inhabited_intro with (x:=x). auto with sets. }
              { intros. unfold Included in H0.
                assert (In U (Singleton U x) x0).
                { apply H0. auto with sets. }
                assert (In U (Singleton U x) y).
                { apply H0. auto with sets. }
                destruct H1; destruct H2. left. apply PO_cond2.  }   }  Qed.

  Lemma Singleton_is_antichain: forall x: U, In _ C x -> Is_an_antichain_in FP (Singleton _ x).
    Proof. { intros.  unfold Is_an_antichain_in. split. 
              { split. unfold Included. intros. destruct H0. apply H.
                apply Inhabited_intro with (x:=x). auto with sets. }
              { intros. unfold Included in H0.
                assert (In U (Singleton U x) x0).
                { apply H0. auto with sets. }
                assert (In U (Singleton U x) y).
                { apply H0. auto with sets. }
                destruct H2; destruct H3. reflexivity.  }  } Qed.

Lemma Antichain_exists:  exists e: Ensemble U, Is_an_antichain_in FP e.
    Proof.  { assert (T: Inhabited _ C). Print PO. apply PO_cond1.  destruct T.
              exists (Singleton _ x). apply Singleton_is_antichain. auto. }  Qed.
    
Lemma Chain_exists:  exists e: Ensemble U, Is_a_chain_in FP e.
Proof.  { assert (T: Inhabited _ C). Print PO. apply PO_cond1.  destruct T.
              exists (Singleton _ x). apply Singleton_is_chain. auto.  }  Qed.

Lemma Chain_cover_exists: exists cover: Ensemble (Ensemble U), Is_a_chain_cover FP cover.
Proof. { pose (cover (e: Ensemble U):= exists x: U, In _ C x /\ e = Singleton _ x).
         exists cover.
         Print Is_a_chain_cover. apply cover_cond.
         { intros. unfold In in H. unfold cover in H. destruct H. destruct H.
           rewrite H0. apply Singleton_is_chain.  auto. }
         { intros. exists (Singleton _ x).  split. unfold In. unfold cover. exists x. tauto.
           auto with sets.  }  }  Qed.

Lemma Antichain_cover_exists: exists cover: Ensemble (Ensemble U), Is_an_antichain_cover FP cover.
Proof. { pose (cover (e: Ensemble U):= exists x: U, In _ C x /\ e = Singleton _ x).
         exists cover.
         Print Is_an_antichain_cover. apply AC_cover_cond.
         { intros. unfold In in H. unfold cover in H. destruct H. destruct H.
           rewrite H0. apply Singleton_is_antichain.  auto. }
         { intros. exists (Singleton _ x).  split. unfold In. unfold cover. exists x. tauto.
           auto with sets.  }   }  Qed. 

Lemma Minimal_element_exists: forall (P: FPO U), exists x: U, Is_a_minimal_element P x.
Proof. { intros P'.
       pose (C':= Carrier_of _ P').
       pose ( R':= Rel_of _ P' ).
       assert (H: exists n: nat, cardinal _ C' n).
       { apply finite_cardinal. Print FPO. eapply FPO_cond. }

       destruct H as [n' H]. generalize H. unfold C'.  generalize P' as P0.
       generalize n' as n0. clear H. clear P' C' R' n'. intro n0. 
       induction n0.
       (* Base Case: n=0 then P0 cannot be  a Poset *)
       { intros. apply cardinal_elim  with (p:= 0) in H.
         assert (H1: Inhabited _ (Carrier_of U P0)). (* since PO_cond1 says so *)
         Print PO. apply PO_cond1. rewrite H in H1.
         inversion H1. inversion H0.  } 

       (* Induction Step: When P0 is inhabited. *) 
       intros. 
       assert (H0: exists x: U, In _ (Carrier_of U P0) x).
       { Print PO. destruct (PO_cond1 _ P0). exists x. tauto.  }
       destruct H0 as [a H0].

       pose (C':= Subtract _ (Carrier_of _ P0) a).
       pose (R0:= Rel_of _ P0).

       assert (T: Carrier_of _ P0 = Add _ C' a).
       { apply Extensionality_Ensembles. unfold C'. auto with sets.  } 

       elim (EM (Inhabited _ C')).

       (* CASE1: When C' is non-empty then P' will be the Poset with carrier C' *)
       { intros. Print FPO.
         assert (PS_Finite: Finite _ C').
         { cut (Finite _ (Carrier_of _ P0)).
           intro. eapply Finite_downward_closed.  exact H2. rewrite T.
           auto with sets. apply (FPO_cond _ P0). }

         Print PO.
         pose (P_small:= {| Carrier_of:= C';
                            Rel_of:= Rel_of _ P0;
                            PO_cond1:= H1;
                            PO_cond2:= PO_cond2 _ P0 |}).
         Print FPO.
         pose (S_P0:= {| PO_of:= P_small ; FPO_cond:= PS_Finite |}).

         assert (T0: ~ In _ C' a).
         { unfold C'. intro. inversion H2. apply H4.  auto with sets.  }

         assert (H2: cardinal _ C' n0).
         { rewrite T in H.
           assert (n0 = pred (S n0)).
           { auto with arith. } rewrite H2. eapply card_soustr_1.  rewrite T. tauto.  tauto.  } 

         assert (H3: exists x : U, Is_a_minimal_element S_P0 x). (* Using IHn0 *)
         { eapply IHn0. auto.  } destruct H3 as [b H3].

         (* At this point a is an element in P0 and b is in S_P0 *)
         (* Moreover b is a minimal element of S_P0 *)
         (* Either R a b is true or false ; in each case we produce a witness *)
         elim (EM ( R0 a b)).
         (* CASE A: when R0 a b *)
         { (* In this case a is the minimal_element. We prove it by contradiction. 
              We assume that a ia not the minimal then there must exists some a0, which
              is smaller than a. by transitivity it must also be smaller than b. Hence
              b canot be the minimal of C' which contradicts H3.  *)
           intro. exists a.  unfold Is_a_minimal_element.
           split.
           { tauto. }
           { intro. (* assuming there is a a0 smaller than a we produce a contradiction *)
            destruct H5 as [a0 H5].
            assert (H6: R0 a0 b). (* Using the transitivity of R0 *)
            { Print Order. cut (Transitive _ R0). intro. eapply H6 with (y:=a); tauto.  
              apply PO_cond2. }

            assert (H7: a <> b). (* since b is in C' and a is outside it *)
            { intro. absurd ( In _ C' a). auto. rewrite H7. apply H3. }

            assert (H8: a0 <> b). 
            (* otherwise R0 a b and R b a will become true for diffrent a and b *)
            (* this violets the antysymmetricity of R0 *)
            { intro. absurd ( R0 b a). cut (Antisymmetric _ R0).
              intro. intro. apply H7. apply H9; tauto. apply PO_cond2.
              rewrite <- H8. tauto.  } 

            assert (H9: In _ C' a0). (* since it is in P0 but not equal to a *)
            { unfold C'. unfold Subtract. unfold Setminus.  unfold In.
              split. tauto. intro. destruct H9.
              absurd (a = a). tauto. reflexivity.  }

            assert (H10: ~ Is_a_minimal_element S_P0 b).
            { intro.  unfold Is_a_minimal_element in H10.
              destruct H10 as [H10 H11]. apply H11.
              exists a0. split. tauto. split. intro. apply H8. symmetry. auto.
              simpl. auto. }

            contradiction. }   } 

         (* CASE B: When ~ R0 a b *)
         {  intro.  exists b.
            unfold Is_a_minimal_element.
            rewrite T.
            split.
            { unfold Add.  apply Union_introl. destruct H3. simpl in H3. auto. }
            { intro.  destruct H3. apply H6.
              destruct H5 as [b0 H5].
              assert ( H7: b0<>a).
              { intro. absurd (R0 a b). auto.  rewrite <- H7.   tauto.  }
              assert (H8: In _ C' b0).
              { unfold C'. unfold Subtract. unfold In. unfold Setminus.
                split. rewrite T. tauto. intro. destruct H8. tauto. }

              exists b0.  simpl. tauto.  }      }  }  
       

       (* CASE2: When C' is empty then a is the minimal element. *)
       { intros. exists a. unfold Is_a_minimal_element.  split. auto.
         intro. apply H1. destruct H2 as [b H2]. Print Inhabited.
         apply Inhabited_intro with (x:=b). unfold C'. unfold Subtract. unfold Setminus.
         unfold In.  split. tauto. intro.
         destruct H3. destruct H2 as [H2 H3]. destruct H3 as [H3 H4].
         apply H3. reflexivity.  }   }   Qed.  

Lemma Maximal_element_exists:  forall (P: FPO U), exists x: U, Is_a_maximal_element P x.
Proof. { intro P. Print PO.
         pose ( C':= Carrier_of _ P).
         pose ( R'(x:U)(y:U):= (Rel_of _ P) y x ).
         assert (T: Order _ R' ).
         { assert (T1: Order _ (Rel_of _ P)).
           { apply PO_cond2. } Print Order. destruct T1. 
           apply Definition_of_order.
           { unfold R'. apply H. }
           { unfold R'. unfold Transitive.  Print Transitive.
             intros. eapply H0. exact H3. auto. }
           { unfold R'. unfold Antisymmetric. intros. apply H1; tauto. }
         } 

         pose (PO_P':= {| Carrier_of:= C' ;
                          Rel_of:= R' ;
                          PO_cond1:= (PO_cond1 _ P);
                          PO_cond2:= T |}).

         pose (P':= {| PO_of:= PO_P' ; FPO_cond:= (FPO_cond _ P) |}).
         
         assert (T1: forall x: U, Is_a_minimal_element P' x -> Is_a_maximal_element P x ).
         { intros. unfold Is_a_maximal_element.
           split. apply H. destruct H as [H H1].
           intro H2. apply H1. destruct H2 as [y H2].
           exists y. simpl. unfold C'. unfold R'. tauto.  } 

         assert (H: exists x: U, Is_a_minimal_element P' x).
         { apply Minimal_element_exists.  } destruct H as [x H].

         exists x. auto.   }    Qed.   

Lemma Minimal_is_antichain: Is_an_antichain_in FP  (Minimal_elements_of FP).
Proof. { unfold Is_an_antichain_in. split.
         (* Minimal_elements_of is Included in C and is also Inhabited *)
         { split.
           { unfold Included.  intros. unfold Minimal_elements_of in H. unfold In in H.
             destruct H. auto. }
           { unfold Minimal_elements_of.
             assert ( H: exists x: U, Is_a_minimal_element FP x ).
             { eapply Minimal_element_exists. }
             destruct H as [x H].  eapply Inhabited_intro with (x:=x).
             unfold In. auto. } } 

         (* No two elements are related in Minimal_elements_of. *)
         { intros.
           assert (H1: Is_a_minimal_element FP x).
           { unfold Included in H. unfold In in H at 2. unfold Minimal_elements_of in H.
             apply H.  auto with sets.  }
           assert (H2: Is_a_minimal_element FP y).
           { unfold Included in H. unfold In in H at 2. unfold Minimal_elements_of in H.
             apply H.  auto with sets.  }

           
           unfold Is_a_minimal_element in H1. unfold Is_a_minimal_element in H2.
           elim (EM ( x=y )). tauto. intro.
           elim H0.
           { intro.
           absurd (exists y0 : U, In U C y0 /\ y <> y0 /\ R y0 y).
           tauto. exists x. split. tauto. split. intro. apply H3. symmetry. auto. auto. }
           { intro.
           absurd (exists y : U, In U C y /\ x <> y /\ R y x).
           tauto. exists y. split. tauto. split. intro. apply H3. symmetry. auto. auto. }  }    }   Qed.

Lemma Maximal_is_antichain: Is_an_antichain_in FP (Maximal_elements_of FP).
Proof. { unfold Is_an_antichain_in. split.
         (* Maximal_elements_of is Included in C and is also Inhabited *)
         { split.
           { unfold Included.  intros. unfold Maximal_elements_of in H. unfold In in H.
             destruct H. auto. }
           { unfold Maximal_elements_of.
             assert ( H: exists x: U, Is_a_maximal_element FP x ).
             { eapply Maximal_element_exists.  }
             destruct H as [x H].  eapply Inhabited_intro with (x:=x).
             unfold In. auto. } } 

         (* No two elements are related in Maximal_elements_of. *)
         { intros.
           assert (H1: Is_a_maximal_element FP x).
           { unfold Included in H. unfold In in H at 2. unfold Maximal_elements_of in H.
             apply H.  auto with sets.  }
           assert (H2: Is_a_maximal_element FP y).
           { unfold Included in H. unfold In in H at 2. unfold Maximal_elements_of in H.
             apply H.  auto with sets.  }

           
           unfold Is_a_maximal_element in H1. unfold Is_a_maximal_element in H2.
           elim (EM ( x=y )). tauto. intro.
           elim H0. Focus 2. 
           intro.
           absurd (exists y0 : U, In U C y0 /\ y <> y0 /\ R y y0).
           tauto. exists x. split. tauto. split. intro. apply H3. symmetry. auto. auto. 
           intro.
           absurd (exists y : U, In U C y /\ x <> y /\ R  x y).
           tauto. exists y. split. tauto. split. intro. apply H3. symmetry. auto. auto.   }    }  Qed.

Lemma Minimal_for_every_y: forall y: U, (In _ C y) -> (exists x:U, Is_a_minimal_element FP x /\ R x y ).
Proof. { intros.
         (* We consider the set of all elements Cy which are less than y and in C *)
         (* We show that it form a partial oredr with R as relation *)
         (* Therefore there must exists a minimal_element m in this set Cy *)
         (* This element is less than y i.e R m y and we show that this is also a 
            minimal element in C *)
         pose (Cy (x:U):= In _ C x /\ R x y).

         assert (T: Order _ R).
         {apply PO_cond2. }
         destruct T as [T1 T2 T3].

         assert (T4: In _ Cy y).
         {unfold In.  unfold Cy. split. auto. apply T1.  }

         assert (H0: Included _ Cy C).
         { unfold Included. intros. apply H0.  }

         assert (H1: Inhabited _ Cy).
         { Print Inhabited. apply Inhabited_intro with (x:=y). tauto. }

         assert (H2: Finite _ Cy).
         { eapply Finite_downward_closed with (A:=C). apply FPO_cond. auto. }
         
          pose (P_y:= {| Carrier_of:= Cy;
                            Rel_of:= R;
                            PO_cond1:= H1;
                            PO_cond2:= PO_cond2 _ FP |}).
         pose (FP_y:= {| PO_of:= P_y; FPO_cond:= H2 |}).

         assert (H3:  exists x: U, Is_a_minimal_element FP_y x).
         apply Minimal_element_exists. destruct H3 as [m H3].

         assert (T5: R m y).
         { unfold Is_a_minimal_element in H3. simpl in H3.  apply H3. }

         exists m.
         split.
         { unfold Is_a_minimal_element. unfold C in H0.
           split.
           { apply H0. apply H3. }
           { intro. destruct H4 as [m0 H4].
             assert (H5: R m0 y).
             { eapply T2 with (y:=m); tauto.  }
             assert (H6: In _ Cy m0).
             { unfold In. unfold Cy. tauto. }
             assert (H7: ~ R  m0 m). (* since m is the minimal in Cy and m0 is also in  Cy *)
             { intro. unfold Is_a_minimal_element in H3. destruct H3 as [H3 HT].
               apply HT. exists m0. tauto.  }
             absurd ( R m0 m );tauto.  }  }
         { tauto. } 

         
       } Qed. 

Lemma Maximal_for_every_x: forall x:U, (In _ C x) -> (exists y: U, Is_a_maximal_element FP y /\ R x y ).
Proof.  { intros.
         (* We consider the set of all elements Cx which are greater than x and in C *)
         (* We show that it form a partial oredr with R as relation *)
         (* Therefore there must exists a maximal_element m in this set Cx *)
         (* This element is bigger than x i.e R x m  and we show that this is also a 
            maximal element in C *)
         pose (Cx (y:U):= In _ C y /\ R x y).

         assert (T: Order _ R).
         {apply PO_cond2. }
         destruct T as [T1 T2 T3].

         assert (T4: In _ Cx x).
         {unfold In.  unfold Cx. split. auto. apply T1.  }

         assert (H0: Included _ Cx C).
         { unfold Included. intros.  apply H0.  }

         assert (H1: Inhabited _ Cx).
         { Print Inhabited. apply Inhabited_intro with (x:=x). tauto. }

         assert (H2: Finite _ Cx).
         { eapply Finite_downward_closed with (A:=C). apply FPO_cond. auto. }
         
          pose (P_x:= {| Carrier_of:= Cx;
                            Rel_of:= R;
                            PO_cond1:= H1;
                            PO_cond2:= PO_cond2 _ FP |}).
         pose (FP_x:= {| PO_of:= P_x; FPO_cond:= H2 |}).

         assert (H3:  exists x: U, Is_a_maximal_element FP_x x).
         apply Maximal_element_exists. destruct H3 as [m H3].

         assert (T5: R x m ).
         { unfold Is_a_maximal_element in H3. simpl in H3.  apply H3. }

         exists m.
         split.
         { unfold Is_a_maximal_element. unfold C in H0.
           split.
           { apply H0. apply H3. }
           { intro. destruct H4 as [m0 H4].
             assert (H5: R x m0 ).
             { eapply T2 with (y:=m); tauto.  }
             assert (H6: In _ Cx m0).
             { unfold In. unfold Cx. tauto. }
             assert (H7: ~ R m m0). (* since m is the maximal in Cx and m0 is also in  Cx *)
             { intro. unfold Is_a_maximal_element in H3. destruct H3 as [H3 HT].
               apply HT. exists m0. tauto.  }
             absurd ( R  m m0 );tauto.  }  }
         { tauto. } 

         
       } Qed. 



     
 Lemma Every_minimal_has_a_maximal:
    forall x:U, (In _ (Minimal_elements_of FP)  x)->
                (exists y:U, In _  (Maximal_elements_of FP)  y /\ R x y).
 Proof. { intros.
          assert (H1: In _ C x).
          { apply H. }
          assert (H2: exists y: U, Is_a_maximal_element FP y /\ R x y ).
          { apply Maximal_for_every_x. auto. }

          destruct H2 as [y H2].
          exists y. unfold Maximal_elements_of. unfold In. tauto.  } Qed. 
  
  Lemma Every_maximal_has_a_minimal:
      forall y:U, (In _ (Maximal_elements_of FP) y)->
                  (exists x:U, In _ (Minimal_elements_of FP) x /\ R x y).
  Proof.  { intros.
          assert (H1: In _ C y).
          { apply H. }
          assert (H2: exists x: U, Is_a_minimal_element FP x /\ R x y ).
          { apply Minimal_for_every_y. auto. }

          destruct H2 as [x H2].
          exists x. unfold Minimal_elements_of. unfold In. tauto.  } Qed.  

  Lemma Exists_pair_xy:
    exists (x y:U), (In _ (Minimal_elements_of FP) x)/\ (In _ (Maximal_elements_of FP) y)/\ R x y.
  Proof. { assert(H: exists x:U, In _ (Minimal_elements_of FP) x ). elim Minimal_is_antichain.
         intros. destruct H as [H H1]. destruct H1.  exists x.
         assumption. destruct H as [x0 H].
         exists x0. elim Every_minimal_has_a_maximal with (x:=x0). intros y0 H1.
         exists y0. split. assumption. assumption. assumption. }
  Qed. 



  Lemma Largest_card_same: forall (e1 e2: Ensemble U)(n:nat),
                              Is_largest_antichain_in FP e1 -> Is_largest_antichain_in FP e2 ->
                              (cardinal _ e1 n) -> cardinal _ e2 n.
  Proof. { intros.
           assert (exists m:nat, cardinal _ e2 m).
           { apply finite_cardinal. destruct H0. destruct H0.
             apply Finite_downward_closed with (A:= C). apply FPO_cond.
             tauto. } destruct H2 as [m H2].

           assert (H3: m<=n).
           {  Print Is_largest_antichain_in. destruct H.  eapply H3 with (e2:= e2).
              apply H0. auto. auto.  }

           assert (H4: n<=m).
           { destruct H0. eapply H4 with (e1:= e1). apply H. auto. auto. }

           assert (H5: m=n).
           { auto with arith.  }

           rewrite <- H5. auto. } Qed. 

  
  Lemma Card_same_largest: forall (e1 e2: Ensemble U)(n: nat),
                             Is_largest_antichain_in FP e1 -> Is_an_antichain_in FP e2 ->
                             (cardinal _ e1 n)-> (cardinal _ e2 n)->
                             Is_largest_antichain_in FP e2.
  Proof. { intros.  Print Is_largest_antichain_in.
           apply largest_antichain_cond.
           auto.
           { intros.
             assert (H6: n0=n).
             { eapply cardinal_unicity. exact H4.  auto. }
             rewrite H6.
             destruct H. eapply H7. exact H3. auto. auto.  }   }  Qed.



Lemma Largest_element_exists: Totally_ordered _ FP C ->  exists x: U, Is_the_largest_element_in FP x.
Proof. { intros. destruct H. elim Maximal_element_exists with (P:= FP).
       intro max. intro. exists max.
       assert (Order _ R).
       { apply PO_cond2. }
       destruct H1. 
       unfold Is_the_largest_element_in. unfold Is_a_maximal_element in H0.
       split. tauto. intros.
       elim (classic (max = x)).
       { intro. rewrite H5.  apply H1. }
       { intro.
         assert (Rel_of U FP x max \/ Rel_of U FP max x).
         { apply H. unfold C. auto with sets. unfold Included. intros. destruct H6.
           apply H4. apply H0. }
         elim H6. tauto.
         intro. absurd (exists y : U, In U (Carrier_of U FP) y /\ max <> y /\ Rel_of U FP max y).
         apply H0.
         exists x. tauto.   }  } Qed.

Lemma Maximal_is_largest: Totally_ordered _ FP C -> (forall x: U, Is_a_maximal_element FP x ->
                                                            Is_the_largest_element_in FP x).
  Proof.  { intro. intro max. intro. 
       assert (Order _ R).
       { apply PO_cond2. }
       destruct H1. 
       unfold Is_the_largest_element_in. unfold Is_a_maximal_element in H0.
       split. tauto. intros.
       elim (classic (max = x)).
       { intro. rewrite H5.  apply H1. }
       { intro.
         assert (Rel_of U FP x max \/ Rel_of U FP max x).
         { apply H. unfold C. auto with sets. unfold Included. intros. destruct H6.
           apply H4. apply H0. }
         elim H6. tauto.
         intro. absurd (exists y : U, In U (Carrier_of U FP) y /\ max <> y /\ Rel_of U FP max y).
         apply H0.
         exists x. tauto.   }  } Qed.

Lemma Minimal_is_smallest:  Totally_ordered _ FP C -> (forall x: U, Is_a_minimal_element FP x ->
                                                              Is_the_smallest_element_in FP x).
  Proof.  { intro. intro min. intro. 
       assert (Order _ R).
       { apply PO_cond2. }
       destruct H1. 
       unfold Is_the_smallest_element_in. unfold Is_a_minimal_element in H0.
       split. tauto. intro x.  intros.
       elim (classic (min = x)).
       { intro. rewrite H5.  apply H1. }
       { intro.
         assert (Rel_of U FP x min \/ Rel_of U FP min x).
         { apply H. unfold C. auto with sets. unfold Included. intros. destruct H6.
           apply H4. apply H0. }
         elim H6. 
         intro. absurd (exists y : U, In U (Carrier_of U FP) y /\ min <> y /\ Rel_of U FP y min).
         apply H0.
         exists x. tauto.  tauto. }  } Qed.

Lemma Smallest_element_exists: Totally_ordered _ FP C -> exists x: U, Is_the_smallest_element_in FP x.
Proof.   { intros. destruct H. elim Minimal_element_exists with (P:= FP).
       intro min. intro. exists min.
       assert (Order _ R).
       { apply PO_cond2. }
       destruct H1. 
       unfold Is_the_smallest_element_in. unfold Is_a_minimal_element in H0.
       split. tauto. intro x.  intros.
       elim (classic (min = x)).
       { intro. rewrite H5.  apply H1. }
       { intro.
         assert (Rel_of U FP x min \/ Rel_of U FP min x).
         { apply H. unfold C. auto with sets. unfold Included. intros. destruct H6.
           apply H4. apply H0. }
         elim H6. 
         intro. absurd (exists y : U, In U (Carrier_of U FP) y /\ min <> y /\ Rel_of U FP y min).
         apply H0.
         exists x. tauto.  tauto. }  } Qed.      


End Finite_Chain_Facts.

                                                                                      

Hint Resolve NoTwoCommon Singleton_is_chain Singleton_is_antichain :fpo_facts.
Hint Resolve Antichain_exists Chain_exists Chain_cover_exists Antichain_cover_exists: fpo_facts.
Hint Resolve Minimal_element_exists Maximal_element_exists: fpo_facts.
Hint Resolve Minimal_is_antichain Maximal_is_antichain: fpo_facts.
Hint Resolve Minimal_for_every_y Maximal_for_every_x: fpo_facts.
Hint Resolve Largest_card_same Card_same_largest Largest_element_exists: fpo_facts.
Hint Resolve Maximal_is_largest Minimal_is_smallest Smallest_element_exists: fpo_facts.