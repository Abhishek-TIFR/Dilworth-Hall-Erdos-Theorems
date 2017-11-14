(* This file contains the proof of Hall's marriage theorem on the collection 
   of finite sets (SDR version of Hall's theorem). Let S be a collection of sets.
   Hall's Marriage theorem then states that,

• S has an SDR iff the union of any k members of S contains at least k elements. 

  We prove the following MAIN THEOREM in this file,
  --------------------------------------------------------------------------------- 
  Theorem The_Halls_Thm:  (forall S: Ensemble (Ensemble U) , Included _ S L ->
       ( forall m n:nat, (cardinal _ S m /\ cardinal _ (Union_over S) n) -> m<= n) )
       <->
       ( exists Rel': Ensemble U -> U-> Prop,
         (forall (x:Ensemble U) (y:U), Rel' x y -> In _ x y) /\
         ( forall (x y:Ensemble U) (z: U), (Rel' x z /\ Rel' y z)-> x=y) /\
         (forall x: Ensemble U, In _ L x -> (exists y: U, Rel' x y))).     
  --------------------------------------------------------------------------------- 
Note that the existence of such a relation Rel' assures the existence of a one-one map
from S to X. Moreover, Rel' is contained in the set membership relation;
 because Rel' x y -> In _ x y. Hence, the existence of such relation implies the 
existence of an SDR and vice-versa.  

There is one technical difficulty that arises while proving Hall's theorem on sets 
using Hall's theorem on Bipartite graphs. In a Bipartite graph the members of 
sets L and R are of the same type. It is essential to define them in this way since
constructing a poset from graph and applying Dilworth's theorem becomes easy.
However, in the Hall's theorem on sets (SDR) the members of the sets S and X are
of different types. The members of S are of type Ensemble U while the members of 
X are of type U.  

Therefore it becomes difficult to prove The_Halls_Thm directly using Halls_Thm. 
To resolve this issue we consider a bipartite graph where the left and right 
vertices are of different types. Let, 

Variable L: Ensemble U.

Variable R: Ensemble V.

Variable Rel: U-> V-> Prop.

In this context we then prove the following statement,

Theorem Marriage_Thm:  (forall (S: Ensemble U), Included _ S L -> 
               (forall m n :nat, (cardinal _ S m /\ cardinal _ (Ngb S) n) -> m <=n ) )
                <->
         ( exists Rel': U-> V-> Prop, Included_in_Rel Rel' /\ Is_L_Perfect_matching Rel'). 

where Ngb and Is_L_Perfect_matching are defined as,

 Definition Ngb (S: Ensemble U):= fun (y: V)=> exists x:U, In _ S x /\ Rel x y. 

 Definition Is_L_Perfect_matching (Rel: U-> V-> Prop):=
    (forall x: U, In _ L x -> (exists y: V, In _ R y /\ Rel x y)) /\
    ( forall (x y: U)(z: V), (Rel x z /\ Rel y z) -> x=y).

Once we have the above result it can be directly used to prove The_Halls_Thm on sets. 
Proof of The_Halls_Thm using Marriage_Thm also appears in this file.    *)

Require Import Halls_Thm.


Section Container_datatype.

  Variable U V : Type.

  Definition UV:= sum U V. Check UV.

  Variable L: Ensemble U.

  Variable R: Ensemble V.

  Variable Rel: U-> V-> Prop.

  Definition Ngb (S: Ensemble U):= fun (y: V)=> exists x:U, In _ S x /\ Rel x y.

  Check Ngb.

  Definition Is_L_Perfect_matching (Rel: U-> V-> Prop):=
    (forall x: U, In _ L x -> (exists y: V, In _ R y /\ Rel x y)) /\
    ( forall (x y: U)(z: V), (Rel x z /\ Rel y z) -> x=y).

  Print contains.

  Definition Included_in_Rel (Rel': U -> V-> Prop): Prop := forall (x:U) (y:V), Rel' x y -> Rel x y.
  Check Included_in_Rel.

  Hypothesis L_inhabited: Inhabited _ L.
  Hypothesis L_Rel_R: forall (x: U)(y: V), Rel x y -> In _ L x /\ In _ R y.
  Hypothesis LR_Finite: Finite _ L /\ Finite _ R. 

  Theorem Marriage_B: ( exists Rel': U-> V-> Prop, Included_in_Rel Rel' /\ Is_L_Perfect_matching Rel')->
                      (forall (S: Ensemble U),
                Included _ S L -> (forall m n :nat, (cardinal _ S m /\ cardinal _ (Ngb S) n) -> m <=n ) ).
    Proof.  { intros. destruct H as [Rel' H]. destruct H as [Ha Hb].
         unfold Is_L_Perfect_matching in Hb. destruct Hb as [Hb Hc].
         (* unfold Is_a_matching in Hb. *) unfold Included_in_Rel in Ha.
         pose (N'(S: Ensemble U)(y: V) := exists x:U, In _ S x /\ Rel' x y).

          assert (T3: Included _ (N' S) ( Ngb S)).
         { unfold Included. intros. destruct H. unfold Ngb. unfold In.
           exists x0. split. apply H.  apply Ha.  tauto.  }

         assert (T4: Finite _ (N' S)).
         { eapply Finite_downward_closed with (A:= (Ngb S)).
           eapply Finite_downward_closed with (A:= R).
           { tauto. }  {  unfold Included. intros. unfold In in H.  unfold Ngb in H.
              destruct H as [x0 H2]. cut (In U L x0 /\ In V R x).
              tauto. eapply L_Rel_R. tauto. }
           { unfold Included. intros. destruct H. unfold Ngb. unfold In.
             exists x0. split. tauto. apply Ha. tauto. }   }

         apply finite_cardinal in T4. destruct T4 as [m' T4].

         assert (T5: m <= m').
         { eapply Bijection_Relation5 with (U:=U) (V:=V) ( A:= S) (B:= N' S)(R:= Rel').
           { intros.
             assert ( In _ L x). { apply H0. auto. }
             cut (exists y : V, In V R y /\ Rel' x y). intros. destruct H3 as [y H3].
             exists y. split. unfold In. unfold N'. exists x. tauto. tauto. auto. }

           { intros. apply Hc with (z:= b). tauto. }
           tauto. tauto. } 

        
         assert (T6: m'<= n).
         { eapply incl_card_le. exact T4. Focus 2. exact T3. tauto. }

         SearchPattern (?m<= ?n -> ?n <= ?p -> ?m <= ?p ).
         eapply le_trans. exact T5. auto. 

          }  Qed. 
  
  Theorem Marriage_A: (forall (S: Ensemble U),
                 Included _ S L -> (forall m n :nat, (cardinal _ S m /\ cardinal _ (Ngb S) n) -> m <=n ) ) ->
                      ( exists Rel': U-> V-> Prop, Included_in_Rel Rel' /\ Is_L_Perfect_matching Rel').
  Proof.   { 

    intro H0.
      assert ( T1: exists l:nat, cardinal _ L l ).
      { apply finite_cardinal. tauto. } destruct T1 as [l T1].
      assert (T2: l >0). { eapply inh_card_gt_O. exact L_inhabited. auto. }

      assert (T3: Included _ (Ngb L) R).
      { unfold Included. intros y H1.
        unfold In in H1. unfold Ngb in H1. destruct H1 as [ x H1].
        cut (In U L x /\ In V R y). tauto. apply L_Rel_R. tauto. } 
      assert (T4: Finite _ (Ngb L)).
      { eapply Finite_downward_closed with (A:=R). tauto. tauto.  } 
      assert (T5: exists lN: nat, cardinal _ (Ngb L) lN).
      { apply finite_cardinal. tauto. } destruct T5 as [lN T5].
      assert (T6: l <= lN).
      { eapply H0 with (S:=L). unfold Included. trivial. tauto. }

      assert (T7: exists r:nat, cardinal _ R r).
      { apply finite_cardinal. tauto.  } destruct T7 as [r T7].

      assert (T8: lN <= r).
      { eapply incl_card_le. exact T5. exact T7.   auto. }

      assert ( T9: r>0).
      {  assert (T10: 0< lN).
         { SearchPattern (?m < ?n -> ?n <= ?p -> ?m < ?p ).
           eapply lt_le_trans. exact T2.  auto. }
         eapply lt_le_trans. exact T10.  auto. }
      
    assert (R_inhabited: Inhabited _ R).
    (* This is true because |R| >= |Ngb L| >= |L| > 0 *)
      {  destruct r. inversion T9.
         apply cardinal_elim with (U:= V)(p:= (S r) )(X:= R).
         auto. } 

      

     

         pose (UV:= sum U V).
         Print Biper_Graph.
         Print Finite_Graph. Print Graph.

         pose (L'(x': UV ):= match x' with
                             |  inl x => In _ L x
                             |  inr _ => False end ).
         pose (R' (y' : UV):= match y' with
                              | inr y => In _ R y
                              | inl _ => False end ).

         pose ( V':= Union _ L' R').

         pose (Rel' (x': UV )(y': UV) := match (x', y') with
                                         | (inl x , inr y) => Rel x y
                                         | (inr _, _ ) => False
                                         | (_, inl _)=> False end ).

         assert (F0: forall (x:U) (y:V), Rel' (inl x) (inr y) -> Rel x y).
         { intros x y. intro. unfold Rel' in H. auto. }

         assert (F1: forall x': UV, In _ L' x' -> exists x: U, x'= (inl x) /\ In _ L x ).
         { intros. destruct x'.
           exists u. split. reflexivity. unfold L' in H. tauto.
           unfold L' in H. unfold In in H. tauto. }

         assert (F2: forall y': UV, In _ R' y' -> exists y: V, y'= (inr y) /\ In _ R y ).
         { intros. destruct y'.
           unfold R' in H. unfold In in H. tauto.
           exists v.  split. reflexivity.  tauto. }   
             

         assert (LR_Inhabited': Inhabited _ L' /\ Inhabited _ R').
         { Print Inhabited. split.
           destruct L_inhabited as [x L_Inh]. eapply Inhabited_intro with (x:= (inl x)).
           unfold L'. unfold In. auto.
           destruct R_inhabited as [y R_Inh]. Print Inhabited.
           eapply Inhabited_intro with (x:= (inr y)).
           unfold R'. unfold In. auto. }  

         assert (NEmpty_cond': Inhabited _ V').
         { destruct LR_Inhabited' as [ Inh_L Inh_R].
           destruct Inh_L as [x Inh_L]. eapply Inhabited_intro with (x:= x).
           unfold V'. apply Union_introl. auto.  }


         pose (f1(x: U):= (inl V x) ).
         pose (f2(y: V):= (inr U y) ).

         assert(f1_one_one: injective _ _ f1).
         { unfold injective. intros.  unfold f1 in H. injection H. tauto.  }
         assert (f2_one_one: injective _ _ f2).
         { unfold injective. intros.  unfold f2 in H. injection H. tauto. }

         assert (Image_LL': L'= Im _ _ L f1).
         {  cut (Same_set  _ L' (Im _ _ L f1 ) ).
            eapply Extensionality_Ensembles. unfold Same_set.
            split.
            { unfold Included. intros x'. intro.
              assert (H1: exists x: U, x'= (inl x) /\ In _ L x). auto.
              destruct H1 as [x H1]. destruct H1 as [H1 H2].
              rewrite H1. apply Im_def. auto. }

            { unfold Included. intros x. intro.
              destruct H. unfold f1 in H1. rewrite H1. unfold In.
              unfold L'. auto. }   }

         assert (Image_RR': R' = Im _ _ R f2).
         { cut (Same_set  _ R' (Im _ _ R f2 ) ).
            eapply Extensionality_Ensembles. unfold Same_set.
            split.
             { unfold Included. intros y'. intro.
              assert (H1: exists y: V, y'= (inr y) /\ In _ R y). auto.
              destruct H1 as [y H1]. destruct H1 as [H1 H2].
              rewrite H1. apply Im_def. auto. }

             { unfold Included. intros x. intro.
              destruct H. unfold f2 in H1. rewrite H1. unfold In.
              unfold R'. auto. }   }    


         assert (Finite_L': Finite _ L').
         { rewrite Image_LL'. eapply finite_image. tauto.  }

         assert (Finite_R': Finite _ R').
         { rewrite Image_RR'. eapply finite_image. tauto.  }

         assert (Finite_V': Finite _ V').
         { unfold V'. apply Union_preserves_Finite; tauto.  } 

         assert (LR_Disj': Disjoint _ L' R').
         { Print Disjoint. apply Disjoint_intro.
           intros. intro. destruct H. unfold In in H. unfold In in H1.
           unfold L' in H. unfold R' in H1. destruct x; contradiction.  } 

         assert (LR_Union': V' = Union _ L' R' ).
         { unfold V'. reflexivity.  }

         assert (LR_Rel': forall x y : UV, Rel' x y -> In _ L' x /\ In _ R' y).
         {  intros. destruct x; destruct y.
            { unfold In;try (inversion H).  }
            { unfold In;try (inversion H).  simpl. unfold Rel' in H. auto. }
            { unfold In;try (inversion H).  }
            { unfold In;try (inversion H).  } }  

         pose (G':= {| Vertices_of := V';
                          Edge_Rel_of:= Rel' ;
                          NonEmpty_cond:= NEmpty_cond' |} ).

         pose (FG':=  {| Graph_of_FG := G';
                         F_Graph_cond := Finite_V' |} ).

  pose (BG':= {| Graph_of_BG := FG';
                 L_of := L';
                 R_of := R';
                 LR_Inhabited := LR_Inhabited';
                 LR_Disj := LR_Disj';
                 LR_Union := LR_Union';
                 LR_Rel := LR_Rel' |}). 

 

         assert (Fact1: (forall (S: Ensemble UV), Included _ S L' ->
                 (forall m n :nat, (cardinal _ S m /\ cardinal _ (N BG' S) n) -> m <=n ) )). 
         { intros S'. intro. intros m' n'. intro.
           pose (S (x:U):= In _ S' (inl x)).
           assert (S_Image: S' = Im _ _ S f1).
           { cut (Same_set _ S' (Im _ _ S f1)).  auto with sets.
             unfold Same_set.
             split.
             { unfold Included. intros x' H2.
               assert (exists x : U, x' = inl x /\ In U L x ).
               apply F1. auto. destruct H3 as [x H3]. destruct H3 as [ H3 H4].
               rewrite H3 in H2. eapply Im_intro.
               unfold In. unfold S. exact H2. unfold f1. auto. }
             { unfold Included. intros. destruct H2. unfold f1 in H3.
               rewrite H3.  unfold In in H2. unfold S in H2. auto. }  } 

           assert (S_Inc: Included _ S L).
           { unfold Included. intro x. intro.
             unfold In in H2.  unfold S in H2.
             assert (H3: In _ L' ( inl x)).
             unfold Included in H. auto. unfold In in H3.
             unfold L' in H3. auto.  }
           
           assert (S_Finite: Finite _ S). (* since S is included in L *)
           { eapply Finite_downward_closed with (A:= L); tauto. } 
           apply finite_cardinal in S_Finite. destruct S_Finite as [m S_Card].

           assert (NgbS_in_R: Included _ (Ngb S) R).
           {  unfold Included. intros. unfold In in H2.  unfold Ngb in H2.
              destruct H2 as [x0 H2]. cut (In U L x0 /\ In V R x).
              tauto. eapply L_Rel_R. tauto.  } 
           
           assert (NgbS_Finite: Finite _ (Ngb S)). (* since Ngb S is included in R *)
           { eapply Finite_downward_closed with (A:= R); tauto.  }
           apply finite_cardinal in NgbS_Finite. destruct NgbS_Finite as [n NgbCard]. 

           assert (NgbS_Image: (N BG' S') = Im _ _ (Ngb S) f2).
           { cut ( Same_set _ (N BG' S') (Im _ _ (Ngb S) f2)).
             auto with sets. unfold Same_set.
             split.
             { unfold Included. intros y. intros. destruct H2.  simpl in H2.
               assert (H3: In _ L' x).
               { unfold Included in H. apply H. tauto. }
               assert (H4: exists x0 : U, x = inl x0 /\ In U L x0).
               { apply F1. tauto. } destruct H4 as [x0 H4]. destruct H4 as [H4 H5].
               
               assert (H6: In _ R' y).
               { cut (In UV L' x /\ In UV R' y). tauto.
                 apply LR_Rel'.  tauto. } 
               assert (H7: exists y0 : V, y = inr y0 /\ In _ R y0).
               { apply F2. tauto. } destruct H7 as [y0 H7]. destruct H7 as [H7 H8].
               rewrite H7. eapply Im_def. unfold In. unfold Ngb.
               exists x0. unfold In; unfold S. rewrite <- H4. split. tauto.
               destruct H2 as [Ha2 Hb2]. rewrite H4 in Hb2. rewrite H7 in Hb2.
               unfold Rel' in Hb2. tauto.   }

             { unfold Included. intros y. intros. destruct H2 as [y0 H2 y H3].
               destruct H2 as [x0 H2].
               assert ( H4: In _ S' (inl x0)). tauto.
               unfold f2 in H3. unfold In.  unfold N.
               exists (inl x0). rewrite H3. tauto.  }  } 

           assert (Fmm': m' = m).
           { eapply injective_preserves_cardinal with (f:= f1).  auto.
             exact S_Card. rewrite <- S_Image. tauto.  } 

           assert (Fnn': n' = n).
           {  eapply injective_preserves_cardinal with (f:= f2).  auto.
              exact NgbCard. rewrite <- NgbS_Image. tauto.  }

           rewrite Fmm'. rewrite Fnn'.
           eapply H0. exact S_Inc. tauto.  }

         assert (Fact2: exists Rel': Relation UV, Included_in_Edge BG' Rel' /\ Is_L_Perfect BG' Rel' ).
         { eapply Hall_A. apply Fact1.  }

         destruct Fact2 as [Rel0' Fact2].

         

         (* We need to extract a relation Rel1': U -> V-> Prop,  reflecting Rel0'  *)
          pose (Rel0(x:U)(y:V):= Rel0' (inl x) (inr y) ). 

          (* Then we produce this as certificate for Goal and prove the obligations *)
          exists Rel0.
          split.
          { unfold Included_in_Rel. intros x y H1.
            apply F0. apply Fact2. tauto. } 
          { unfold Is_L_Perfect_matching. 
            split.
            { intros x H1.
              assert ( H2: In _ L' (inl x)). { tauto. }
              assert (H3: exists y': UV, In _ R' y' /\ Rel0' (inl x) y').
              { destruct Fact2 as [Fact2 Fact3 ].  unfold Is_L_Perfect in Fact3.
                destruct Fact3 as [Fact3 Fact4 ]. unfold Is_a_matching in Fact3.
                assert (H3: exists y : UV, Rel0' (inl x) y).
                { auto. } destruct H3 as [y H3].
                exists y.  split. assert (H4: Rel' (inl x) y). apply Fact2. auto.
                cut ( In _ L' (inl x) /\ In _ R' y). tauto.  apply LR_Rel'. tauto.
                tauto. } 
              destruct H3 as [y' H3].
              assert (H4: exists y : V, y' = inr y /\ In V R y).
              { eapply F2. tauto.  }
              destruct H4 as [y H4]. destruct H4 as [H4 H5].
              exists y. split. tauto. rewrite H4 in H3. apply H3. }
            { intros.
              assert (H1: Rel0' (inl x) (inr z) /\ Rel0' (inl y) (inr z) ).
              tauto. destruct Fact2 as [Fact2 Fact3 ].  unfold Is_L_Perfect in Fact3.
              destruct Fact3 as [Fact3 Fact4 ]. unfold Is_a_matching in Fact3.
              Print inl.
              assert( H2: (inl V x) = (inl V y) ).
              { eapply Fact3. left. exact H1. }
              injection H2. tauto. }  }

    }    Qed.

  Theorem Marriage_Thm:  (forall (S: Ensemble U),
               Included _ S L -> (forall m n :nat, (cardinal _ S m /\ cardinal _ (Ngb S) n) -> m <=n ) ) <->
                         ( exists Rel': U-> V-> Prop, Included_in_Rel Rel' /\ Is_L_Perfect_matching Rel').
    Proof. unfold iff.  split; ( eapply Marriage_A ||  eapply Marriage_B) . Qed. 


End Container_datatype.








Section The_Halls_Thm.

  
  Variable U:Type.

  Variable L: Ensemble (Ensemble U).

   Check L.

   Hypothesis L_Finite: Finite _ L.

   Hypothesis All_S_Finite: forall S: Ensemble U, In _ L S -> Finite _ S.

   Definition R:= Union_over L.

   Definition Rel (S: Ensemble U) (s: U):= In _ S s /\ In _ L S.

   Lemma LR_Finite:  Finite _ L /\ Finite _ R.
   Proof. {  split. apply L_Finite. unfold R.
           apply Finite_Union_of_Finite_Sets.
           split. auto. apply All_S_Finite. }  Qed.  

   
   Lemma L_Rel_R:  forall (S: Ensemble U)(s: U), Rel S s -> In _ L S /\ In _ R s.
   Proof. { intros. unfold Rel in H.
          split.
          { tauto. }
          { unfold R. unfold In. unfold Union_over. exists S; tauto. } }  Qed. 

  Theorem The_HallsB:  ( exists Rel': Ensemble U -> U-> Prop,
                        (forall (x:Ensemble U) (y:U), Rel' x y -> In _ x y) /\
                        ( forall (x y:Ensemble U) (z: U), (Rel' x z /\ Rel' y z)-> x=y) /\
                        (forall x: Ensemble U, In _ L x -> (exists y: U, Rel' x y))) ->
                          (forall S: Ensemble (Ensemble U) , Included _ S L ->
                        ( forall m n:nat, (cardinal _ S m /\ cardinal _ (Union_over S) n) -> m<= n) ).
  Proof. { intros. destruct H as [Rel' H]. destruct H as [Ha Hb].
         unfold Is_L_Perfect_matching in Hb. destruct Hb as [Hb Hc].
         pose (N'(S: Ensemble (Ensemble U)) (y: U) := exists x: Ensemble U, In _ S x /\ Rel' x y).

          assert (T3: Included _ (N' S) ( Union_over S)).
         { unfold Included. intros. destruct H. unfold Union_over. unfold In.
           exists x0. split. apply H.  apply Ha.  tauto.  }

         assert (T2: Finite _ R).
         { unfold R. apply Finite_Union_of_Finite_Sets. tauto. }

         assert (T4: Finite _ (N' S)).
         { eapply Finite_downward_closed with (A:= (Union_over S)).
           eapply Finite_downward_closed with (A:= R).
           { tauto. }  {  unfold Included. intros. unfold In in H.  unfold Union_over in H.
              destruct H as [x0 H2]. cut (In _ L x0 /\ In _ R x).
              tauto. eapply L_Rel_R. unfold Rel. split. tauto. apply H0. tauto. }
           { unfold Included. intros. destruct H. unfold Union_over. unfold In.
             exists x0. split. tauto. apply Ha. tauto. }   } 

         apply finite_cardinal in T4. destruct T4 as [m' T4].

         assert (T5: m <= m').
         { eapply Bijection_Relation5 with (U:=Ensemble U) (V:=U) ( A:= S) (B:= N' S)(R:= Rel').
           { intros.
             assert ( In _ L x). { apply H0. auto. }
             cut (exists y : U, In _ R y /\ Rel' x y). intros. destruct H3 as [y H3].
             exists y. split. unfold In. unfold N'. exists x. tauto. tauto.
             assert (H3: exists y : U, Rel' x y).
             { auto. } destruct H3 as [y H3]. exists y. split.
             cut ( In _ L x /\ In _ R y). tauto. eapply L_Rel_R. unfold Rel.
             split. auto. tauto. auto.  } 

           { intros. apply Hb with (z:= b). tauto. }
           tauto. tauto. } 

        
         assert (T6: m'<= n).
         { eapply incl_card_le. exact T4. Focus 2. exact T3. tauto. }

         SearchPattern (?m<= ?n -> ?n <= ?p -> ?m <= ?p ).
         eapply le_trans. exact T5. auto. 

          }  Qed. 
  
 
  
  Theorem The_HallsA: (forall S: Ensemble (Ensemble U) , Included _ S L ->
                    ( forall m n:nat, (cardinal _ S m /\ cardinal _ (Union_over S) n) -> m<= n) ) ->
                    ( exists Rel': Ensemble U -> U-> Prop,
                        (forall (x:Ensemble U) (y:U), Rel' x y -> In _ x y) /\
                        ( forall (x y:Ensemble U) (z: U), (Rel' x z /\ Rel' y z)-> x=y) /\
                        (forall x: Ensemble U, In _ L x -> (exists y: U, Rel' x y))).
  Proof.  { 

   
    
      pose (R:= Union_over L).  Check R.

      elim (EM ( Inhabited _ L )).

      (* CASE1: When the collection L is non-empty *)
      (* Here H:  L is inhabited *)
      { 

        intros H H1.
        assert ( L_inhabited: Inhabited _ L). auto.

        Check Marriage_A.

        assert ( H2:  exists Rel' : Ensemble U -> U -> Prop,
                   Included_in_Rel _ _  Rel Rel' /\ Is_L_Perfect_matching _ _  L R Rel').

        { eapply Marriage_A.
          auto.
          apply  L_Rel_R.
          apply LR_Finite.
          intros.  apply H1 with (S:= S).
          auto. split. tauto.
          assert ( H3: Union_over S = (Ngb _ _ Rel S)).
          cut ( Same_set _ ( Union_over S) ( Ngb _ _ Rel S)).
          auto with sets. unfold Same_set.
          split.
          { unfold Included. intros. unfold In.  unfold Ngb.
            unfold In in H3. unfold Union_over in H3.
            destruct H3. exists x0. unfold Rel.
            split. tauto. split. tauto. apply H0. tauto. }
          { unfold Included.  intros. unfold In. unfold Union_over.
            unfold In in H3. unfold Ngb in H3. unfold Rel in H3.
            destruct H3 as [S1 H3].  exists S1; tauto.  }

          rewrite H3.  tauto.  }

        destruct H2 as [Rel' H2].
        destruct H2 as [Ha2 Hb2].
        unfold Included_in_Rel in Ha2.
        unfold Is_L_Perfect_matching in Hb2.
        destruct Hb2 as [Hb2 Hc2]. 

        exists Rel'.
        split.
        { intros x y H3.
          assert (H4: Rel x y).
          unfold Included_in_Rel in Ha2.
          apply Ha2.  auto. unfold Rel in H4. tauto.  }

        split.
        { apply Hc2. }
        { intros.
          assert ( H3: exists y : U, In U R y /\ Rel' x y).
          auto.  destruct H3 as [y H3].
          exists y.  tauto.  }   } 
        

      (* CASE2: When the collection L is empty *)
      { intros.  exists (fun (x: Ensemble U) (y: U)=> False).
        split. tauto. split. tauto.
        intros x H1. destruct H. Print Inhabited.  eapply Inhabited_intro. exact H1. }

      
    }  Qed.


  Theorem The_Halls_Thm:  (forall S: Ensemble (Ensemble U) , Included _ S L ->
                    ( forall m n:nat, (cardinal _ S m /\ cardinal _ (Union_over S) n) -> m<= n) ) <->
                    ( exists Rel': Ensemble U -> U-> Prop,
                        (forall (x:Ensemble U) (y:U), Rel' x y -> In _ x y) /\
                        ( forall (x y:Ensemble U) (z: U), (Rel' x z /\ Rel' y z)-> x=y) /\
                        (forall x: Ensemble U, In _ L x -> (exists y: U, Rel' x y))).

    Proof. unfold iff. split; (eapply The_HallsA || eapply The_HallsB). Qed. 


  
End The_Halls_Thm.


Check The_HallsA. 