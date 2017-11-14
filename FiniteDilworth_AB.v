
(* In this file we prove the forward and backward directions of Dilworth's 
   decomposition theorem. Forward direction is proved in Section DilworthA
   and the backward direction is proved in Section DilworthB. 
   1. Theorem DilworthA: It states the forward implication of Dilworth's Thm. 
   2. Theorem DilworthB: States the backward implication of Dilworth's Thm. 

   DilworthA and DilworthB are used to prove the main statement of Dilworth's
   Thm in the File FiniteDilworth.v  *)


Require Export FPO_Facts2.

Section DilworthA.
  Variable U: Type.

  
Definition DilworthA_statement:=
  fun (P: FPO U)=>forall (n m :nat)(cv: Ensemble (Ensemble U))(a: Ensemble U),
               Is_a_chain_cover P cv -> Is_an_antichain_in P a ->        
               cardinal _  cv n -> cardinal _  a m ->
               ~(m > n).

Theorem DilworthA: forall (P: FPO U), DilworthA_statement P.
Proof. {  intro P. unfold DilworthA_statement.
        intros n m cv la. intros.  intro.
        pose (R:= fun (x:U) (y: Ensemble U) => In _ y x).
        assert (H4: (exists (x y: U) (z: Ensemble U) ,
                        In _ la x /\ In _ la y /\ In _ cv z /\ x<>y /\ (R x z /\ R y z))).
        { apply Pigeon_Relation with
          (U:= U) (V:= Ensemble U) (A:= la) (B:= cv) (R:=R) (m:=n) (n:=m).
          { destruct H.  intro x. intro. unfold R. apply H4. apply H0. tauto. }
          { auto. }
          { auto. }
          { auto. }
        }

        destruct H4 as [x H4]. destruct H4 as [y H4]. destruct H4 as [chain H4].
        destruct H4 as [ H4a H4]. destruct H4 as [ H4b H4]. destruct H4 as [ H4c H4].
        destruct H4 as [ H4d H4]. unfold R in H4.
        assert (H5: Is_a_chain_in P chain). { destruct H. apply H. auto. }
        assert (H6: x = y). { apply NoTwoCommon with (P:= P)(X:=chain)(Y:= la).
          auto. auto. unfold Included; intros; destruct H6; tauto.
          unfold Included; intros; destruct H6; tauto. }
        absurd (x=y);tauto.  }  Qed.

End DilworthA.
  






Section DilworthB.

Variable U : Type.

Definition PO_Above_Carrier (P: FPO U) (e: Ensemble U): Ensemble U:=
  fun x: U =>( (Inhabited _ e /\ Included _ e (Carrier_of _ P))-> (In _ (Carrier_of _ P) x /\
              exists y:U, In _ e y /\ Rel_of _ P y x)) /\ In _ (Carrier_of _ P) x .

Definition PO_Below_Carrier (P: FPO U)(e : Ensemble U): Ensemble U :=
    fun x: U =>( (Inhabited _ e /\ Included _ e (Carrier_of _ P))-> (In _ (Carrier_of _ P) x /\
              exists y:U, In _ e y /\ Rel_of _ P x y)) /\ In _ (Carrier_of _ P) x .

Lemma la_in_P_Above: forall (P: FPO U)(la: Ensemble U), Is_an_antichain_in P la ->
                                                       Included _ la (PO_Above_Carrier P la).
Proof. {
intros. unfold Included. intro. intro. unfold In.  unfold PO_Above_Carrier.
split. split. destruct H. destruct H as [Ha H]. unfold Included in Ha.
apply Ha. assumption.  exists x. split. assumption.  assert (H2: Order U (Rel_of U P)).
apply PO_cond2. destruct H2. unfold Reflexive in H2. apply H2.
 
destruct H. destruct H as [Ha H]. unfold Included in Ha.
apply Ha. assumption. } Qed.

Lemma la_in_P_Below: forall (P: FPO U)(la: Ensemble U), Is_an_antichain_in P la ->
                                                       Included _ la (PO_Below_Carrier P la).
Proof. {
    intros. unfold Included. intro. intro. unfold In.  unfold PO_Below_Carrier.
split. split. destruct H. destruct H as [Ha H]. unfold Included in Ha.
apply Ha. assumption.  exists x. split. assumption.  assert (H2: Order U (Rel_of U P)).
apply PO_cond2. destruct H2. unfold Reflexive in H2. apply H2.

destruct H. destruct H as [Ha H]. unfold Included in Ha.
apply Ha. assumption. } Qed.

  
Lemma Inhabited_Above_Carrier:
      forall (P: FPO U)(e: Ensemble U), Inhabited U (PO_Above_Carrier P e).
Proof. {
    intros. elim (EM (Inhabited _ e /\ Included _ e (Carrier_of _ P))).
   Focus 2. 
    intro. Print Inhabited. assert (H1: Inhabited _ (Carrier_of _ P)).
   apply PO_cond1. destruct H1. apply Inhabited_intro with (x:=x).
   unfold In. unfold PO_Above_Carrier.
   split.
   apply or_to_imply . left. assumption. assumption.  
   intro. destruct H. destruct H. exists x. unfold In.  unfold PO_Above_Carrier.
   split.
   intro. split. apply H0. assumption. exists x. split. assumption.
   assert (H2: Order U (Rel_of U P)). apply PO_cond2. destruct H2. apply H2.

   apply H0. assumption.  } Qed.


 Lemma Finite_Above_Carrier:
   forall (P: FPO U)(e: Ensemble U),  Finite U ( PO_Above_Carrier P e).
 Proof. {
   intros. apply Finite_downward_closed with (A:= Carrier_of _ P).
   apply FPO_cond. unfold Included. intros. unfold In in H. unfold PO_Above_Carrier in H.
   apply H.  } Qed.
 

 Definition PO_Above (P: FPO U) (e: Ensemble U): FPO U :=
   {| PO_of := {| Carrier_of := (PO_Above_Carrier P e);
      Rel_of := Rel_of _ P ;
      PO_cond1:= Inhabited_Above_Carrier P e;
      PO_cond2:= PO_cond2 _ P |};
      FPO_cond:= Finite_Above_Carrier P e|}.
 Check PO_Above.

 
 Lemma Inhabited_Below_Carrier:
   forall (P: FPO U)(e: Ensemble U), Inhabited U (PO_Below_Carrier P e).
 Proof. {
     intros. elim (EM (Inhabited _ e /\ Included _ e (Carrier_of _ P))).
     Focus 2.
   intro. Print Inhabited. assert (H1: Inhabited _ (Carrier_of _ P)).
   Print PO. apply PO_cond1. destruct H1. apply Inhabited_intro with (x:=x).
   unfold In. unfold PO_Below_Carrier.
   split.
   apply or_to_imply . left. assumption. assumption.
   intro. destruct H. destruct H. exists x. unfold In.  unfold PO_Below_Carrier.
   split.
   intro. split. apply H0. assumption. exists x. split. assumption.
   assert (H2: Order U (Rel_of U P)). apply PO_cond2. destruct H2. apply H2.

   apply H0. assumption.  } Qed.

 Lemma Finite_Below_Carrier:
   forall (P: FPO U)(e: Ensemble U), Finite U ( PO_Below_Carrier P e).
 Proof. {
   intros. apply Finite_downward_closed with (A:= Carrier_of _ P).
   apply FPO_cond. unfold Included. intros. unfold In in H. unfold PO_Below_Carrier in H.
   apply H.  } Qed.

 

 Definition PO_Below (P: FPO U) (e: Ensemble U): FPO U :=
   {| PO_of := {| Carrier_of := (PO_Below_Carrier P e);
      Rel_of := Rel_of _ P ;
      PO_cond1:= Inhabited_Below_Carrier P e;
      PO_cond2:= PO_cond2 _ P |};
      FPO_cond:= Finite_Below_Carrier P e
   |}.
 Check PO_Above.
   
(* the following two lemma helps us give a macro for expression "PO_Above P a" later in 
    the proofs. It helps us extract a name P_Above such that "P_Above = PO_Above P a" *)
 Lemma exists_above: forall (P: FPO U)(e: Ensemble U ),
                     exists (p1:FPO U), p1 = PO_Above P e.
   Proof. intros. exists (PO_Above P e). reflexivity. Qed. 
 Lemma exists_below: forall (P: FPO U)(e: Ensemble U),
                     exists (p1:FPO U), p1 = PO_Below P e.
 Proof. intros. exists (PO_Below P e). reflexivity. Qed.


 Lemma Above_or_Below_la:  forall (P: FPO U) (la: Ensemble U),
     Is_largest_antichain_in P la ->
     (forall x:U, In _ (Carrier_of _ P) x ->
             (exists y: U, In _ la y /\ ( (Rel_of _ P) x y \/ (Rel_of _ P) y x))).

   Proof. { intros P la. intro.  
            pose (C:= Carrier_of _ P).
            pose (R:= Rel_of _ P).
            assert (T: exists n:nat, cardinal _ la n).
            { apply finite_cardinal. eapply Finite_downward_closed with (A:= C).
              apply FPO_cond. apply H.  } destruct T as [n T].
       
            assert (forall x:U, In _ C x -> (exists y: U, In _ la y /\ ( R x y \/ R y x))).
            { destruct H.  intros.
              elim ( classic ( exists y : U, In U la y /\ (R x y \/ R y x) )).
              {tauto. }
              { intro.
                assert (H3: forall y: U, In _ la y -> ~ ( R x y \/ R y x)).
                { assert ( forall y: U, ~ (In U la y /\ (R x y \/ R y x))).
                  { apply Negation8. apply H2. }
                  intro y. cut ( ~ In _ la y \/ ~ ( R x y \/ R y x)). tauto. 
                  cut ( ~ (In U la y /\ (R x y \/ R y x))). tauto.  auto.  }
                assert (Ha3: forall y: U, In _ la y -> ~ (R y x \/ R x y )).
                { intros. intro. assert ( R x y \/ R y x). tauto. generalize H6.
                  apply H3. auto.  }
                assert (H4: ~ In _ la x).
                { intro. apply H2. exists x. split. auto. left.  apply PO_cond2. } 

                pose (la':= Add _ la x).
                assert (H5: cardinal _ la' (S n)).
                { eapply card_add; tauto.  }
           
                assert (H6: Is_an_antichain_in P la').
                { unfold Is_an_antichain_in.
                  split.
                  { split.  unfold Included. intros.
                    unfold la' in H6. destruct H6. unfold Is_an_antichain_in in H.
                    apply H. auto. destruct H6. apply H1.
                    eapply Inhabited_intro with (x:=x). unfold la'. unfold In.
                    unfold Add. apply Union_intror. Print Singleton.
                    auto with sets.  }
                  { intros x0 y0. intros. unfold Included in H6.
                    assert (H8: In _ la' x0).
                    { apply H6. auto with sets.  }
                    assert (H9: In _ la' y0).
                    { apply H6. auto with sets.  }
                    unfold la' in H8.  unfold la' in H9.
                    unfold In in H8. unfold In in H9. unfold Add in H8. unfold Add in H9.
                    destruct H8; destruct H9.
                    { apply H. unfold Included. intros.
                      destruct H10; auto with sets. tauto. }
                    { destruct H9. absurd (Rel_of U P x0 x \/ Rel_of U P x x0).
                 
                      unfold R in Ha3. eapply Ha3. auto. tauto.  }
                    { destruct H8. absurd (Rel_of U P x x1 \/ Rel_of U P x1 x).
                      apply H3. auto. auto. }
                    { destruct H8; destruct H9. reflexivity. }     } }  

           assert (H7: S n <= n).
           { eapply H0 with (e1:= la');tauto.  }
           assert (H8: n <= S n).
           { auto with arith. }
           assert (H9: S n = n ). auto with arith.
           assert (S n <> n).
           { auto with arith. } 
           absurd ( S n = n);tauto. }   } 
            unfold C in H0. unfold R in H0. exact H0.  } Qed. 


Lemma P_Above_or_P_Below:
  forall (P: FPO U) (la: Ensemble U), Is_largest_antichain_in P la ->
               (Carrier_of _ P) =  Union _ (PO_Above_Carrier P la ) (PO_Below_Carrier P la).
Proof. { intros. apply Extensionality_Ensembles.  unfold Same_set.
       pose (C:= Carrier_of _ P).
       pose (R:= Rel_of _ P).
       assert (T: exists n:nat, cardinal _ la n).
       { apply finite_cardinal. eapply Finite_downward_closed with (A:= C).
         apply FPO_cond. apply H.  } destruct T as [n T].
       
       assert (forall x:U, In _ C x -> (exists y: U, In _ la y /\ ( R x y \/ R y x))).
       { unfold C. unfold R. apply Above_or_Below_la.   auto. }  
       
       split. 
       { unfold Included. intros.
         assert (H2:  (exists y: U, In _ la y /\ ( R x y \/ R y x))).
         { apply H0.  auto. } destruct H2 as [y H2]. destruct H2 as [H2 H3].
         elim H3.
         { intro. apply Union_intror. unfold In. unfold PO_Below_Carrier.
           split. 
           { intro. split.  auto. exists y; tauto.  }
           { tauto. } }
         { intro. apply Union_introl. unfold In. unfold PO_Above_Carrier.
           split. 
           { intro. split.  auto. exists y; tauto.  }
           { tauto. } }  }
       { unfold Included. intros. destruct H1. unfold In in H1.
         unfold PO_Above_Carrier in H1. apply H1. unfold In in H1.
         unfold PO_Below_Carrier in H1. apply H1. }    }  Qed. 
       


Lemma No_smaller_element_Above : forall (P: FPO U) (la: Ensemble U) (x a: U),
                                     Is_largest_antichain_in P la ->
                                     In _ (Carrier_of _ (PO_Above P la)) x ->
                                     (In _ la a /\  Rel_of _ P x a ) -> x=a .
Proof. { intros. unfold In in H0. simpl in H0.  unfold PO_Above_Carrier in H0.
        destruct H0. 
        assert  (In U (Carrier_of U P) x /\ (exists y : U, In U la y /\ Rel_of U P y x)).
        apply H0. split. apply H. apply H. destruct H3. destruct H4 as [y H4].
        assert (Order _ (Rel_of _ P)).
        { apply PO_cond2. } destruct H5. 
        assert (Rel_of _ P y a).
        { Print Transitive. eapply H6 with (y:=x);tauto.   }
        destruct H. unfold Is_an_antichain_in in H. destruct H.
        assert (y=a).
        { apply H10. unfold Included. intros. destruct H11;tauto. left. auto.  }
        assert (Rel_of _ P a x /\ Rel_of _ P x a).
        { rewrite H11 in H4. tauto. }
        apply H7;tauto. } Qed. 

Lemma No_bigger_element_Below : forall (P: FPO U)(la: Ensemble U) (x a: U),
                                     Is_largest_antichain_in P la ->
                                     In _ (Carrier_of _ (PO_Below P la)) x ->
                                     (In _ la a /\  Rel_of _ P a x ) -> x=a .
Proof.  { intros. unfold In in H0. simpl in H0.  unfold PO_Below_Carrier in H0.
        destruct H0. 
        assert  (In U (Carrier_of U P) x /\ (exists y : U, In U la y /\ Rel_of U P x y)).
        apply H0. split. apply H. apply H. destruct H3. destruct H4 as [y H4].
        assert (Order _ (Rel_of _ P)).
        { apply PO_cond2. } destruct H5. 
        assert (Rel_of _ P a y).
        { Print Transitive. eapply H6 with (y:=x);tauto.   }
        destruct H. unfold Is_an_antichain_in in H. destruct H.
        assert (y=a).
        { apply H10. unfold Included. intros. destruct H11;tauto. right. auto.  }
        assert (Rel_of _ P a x /\ Rel_of _ P x a).
        { rewrite H11 in H4. tauto. }
        apply H7;tauto. } Qed.     




Lemma PO_Below_inside_P: forall (P: FPO U) (la: Ensemble U ),
                             Is_an_antichain_in  P la -> (la <> (Maximal_elements_of  P))->
                             Inside _ (PO_Below P la) P.
Proof. {
    intros P la H. intro CASE1b.
    assert(H0: True). auto.
    assert(AlwaysTrue: Inhabited U la /\ Included U la (Carrier_of U P)).
    split. destruct H. apply H. destruct H. apply H.

    
elim exists_above with (P:=P) (e :=la). (* We wish to say let P_Above:= (PO_Above P la)*)
intros P_Above. intro H1.
elim exists_below with (P:=P) (e :=la).
intros P_Below. intro H2. (* at this point we have P_Above and P_Below with  desired property *)

unfold Inside.
split.
Focus 2.
* simpl. reflexivity.
  unfold Strict_Included. split.
  unfold Included.  intros. destruct H3. assumption. 

(* WE need to prove that there is some x in P which is not present in P_Below *)
(* For this we use the fact that la <> Maximal_elements_of. *)
apply Not_equal_sets in CASE1b.

elim CASE1b.
  - intro. (* 1st_HalfCASE: when there is a y in la and not present in Maximal *)
  destruct H3 as [y H3]. (* we have a y from la but not in maximal *)
  destruct H3 as [H3a H3b].
  unfold In in H3b. unfold Maximal_elements_of in H3b.

assert(H4: In U (Carrier_of _ P) y). destruct H. destruct H.
unfold Included in H. apply H. assumption. 

(* We wish to  prove the positive of following fact *)
(* Infact if following doesnot happen then y must be a maximal element which contradicts*)
(* Following claim says that there is some x greater than  y and not equal to y *)
assert (H3: exists x: U, In _ (Carrier_of _ P) x /\ y<>x /\ (Rel_of _ P)  y x ). 
{ elim (EM ( exists x: U, In _ (Carrier_of _ P) x /\ y<>x /\ (Rel_of _ P)  y x )).
Focus 2.
intro. absurd (Is_a_maximal_element  P y). assumption.
unfold Is_a_maximal_element. (* apply maximal_element_cond. *) split.  assumption.
intro. elim H3. destruct H5 as [x H5]. exists x. assumption.
trivial. }
(* at this point we have H3 as a crucial fact *)
(* this helps us get a point x0 strictly above y *)
(* we can have a point x0 above y and not equal to y 
   using this we proceed to prove that it (i.e, x0) doesnot belong to P_Below *)
(* we prove this using contradiction *)
destruct H3 as [x0 H3]. (* *)
assert (H5: ~ In _ (PO_Below_Carrier P la) x0 ).
intro. unfold In in H5. destruct H5. destruct H5. clear H6.
apply AlwaysTrue. clear H6. destruct H7 as [y0 H6].
destruct H3 as [H3c H3]. destruct H3 as [H3d H3].
destruct H6 as [H6a H6].
assert ( H7: Rel_of U P  y y0).  (* we prove that y R y0 using transitivity *)
assert (H8: Order U (Rel_of U P)).
apply PO_cond2. destruct H8. apply H8 with (y:= x0).
assumption. assumption.
(* now using antichain condition H we prove that y0= y *)
destruct H. 
assert (H9: y0 = y). apply H8. unfold Included. intros.
destruct H9. assumption. assumption. right. assumption.
(* now we prove R  x0 y by rewriting *)
assert (H10: Rel_of U P x0 y ). rewrite <- H9. assumption.
(*using antisymmetricity we prove that y= x0 because y R x0 and x0 R y are true *)
assert (H11: Order U (Rel_of U P )).
apply PO_cond2. destruct H11. assert (H14: y= x0).
apply H13. assumption. assumption. (*now we have contradiction as x0<>y and x0=y *)
absurd (y=x0). assumption. assumption.
(* here we already proved that x0 is not in P_Below *)
(* Moreover we know that x0 is in P *)
(* hence we can prove that P_Below is not same as P using Lemma Sets_not_equal *)

(* Which proves that P_Below is strictly included in P *)
apply (Sets_not_equal). right. exists x0. split. 
 assumption. destruct H3 as [H3c H3]. assumption.

           (* the 1st_halfCASE is OVER HERE *)
  - intro.  (* 2nd HalfCASE when y belongs to Maximal but not to la *)
    destruct H3 as [y H3]. destruct H3 as [H3a H3b].
    assert (H4: ~ In _ (PO_Below_Carrier P la) y). intro.
    (* assuming y belongs to P_Below we produce contradiction *)
    destruct H3. destruct H3. clear H4. apply AlwaysTrue. clear H4. destruct H5 as [x H4].
    destruct H4 as [H4a H4b]. 
    { elim (EM (x=y)). (* we produce contradiction in both cases *)
    Focus 2.
    intro. (*CASE x<>y   in this case we prove y is not maximal *)
    destruct H3a.
    assert (H6a: (exists y0 : U, In U (Carrier_of U P) y0 /\ y <> y0 /\ Rel_of U P y y0)).
    exists x.
    split. destruct H. destruct H.  unfold Included in H. apply H. assumption.
    split. intro. symmetry in H7. elim H4.  assumption. assumption.
    (* In this case H6 and H6a are contradictory *)
    elim H6. assumption.
    intro. (*CASE x=y in this case since x belongs la hence y belongs la which contradicts H3b*)
    rewrite H4 in H4a. elim H3b. assumption.  }
    (* here we could prove that y is not in P_Above, hence it is strictIncluded in P  *)
    apply (Sets_not_equal). right. exists y.
    split.  simpl. assumption.
    destruct H3a. assumption.   } Qed.

  
Lemma PO_Above_inside_P: forall (P: FPO U) (la: Ensemble U),
                           Is_an_antichain_in  P la -> (la <> (Minimal_elements_of  P))->
                           Inside  _ (PO_Above P la) P.
Proof. {
    intros P la H. intro CASE1b.
         assert(H0: True). auto.
         assert(AlwaysTrue: Inhabited U la /\ Included U la (Carrier_of U P)).
         split. destruct H. apply H. destruct H. apply H.

        
elim exists_above with (P:=P) (e :=la). (* We wish to say let P_Above:= (PO_Above P la)*)
intros P_Above. intro H1.
elim exists_below with (P:=P) (e :=la).
intros P_Below. intro H2. (* at this point we have P_Above and P_Below with  desired property *)
unfold Inside. split.
 Focus 2.   simpl. reflexivity.
unfold Strict_Included. split.
unfold Included.  intros. destruct H3. assumption. 

(* WE need to prove that there is some x in P which is not present in P_Above *)
(* For this we use the fact that la <> Minimal_elements_of. *)
apply Not_equal_sets in CASE1b.

elim CASE1b. intro. (* 1st_HalfCASE: when there is a y in la and not present in Minimal *)
destruct H3 as [y H3]. (* we have a y from la but not in minimal *)
destruct H3 as [H3a H3b].
unfold In in H3b. unfold Minimal_elements_of in H3b.

assert(H4: In U (Carrier_of _ P) y). destruct H. destruct H.
unfold Included in H. apply H. assumption. 

(* We wish to  prove the positive of following fact *)
(* Infact if following doesnot happen then y must be a minimal element which contradicts*)
(* Following claim says that there is some x less than y and not equal to y *)
assert (H3: exists x: U, In _ (Carrier_of _ P) x /\ y<>x /\ (Rel_of _ P) x y ).
{ elim (EM ( exists x: U, In _ (Carrier_of _ P) x /\ y<>x /\ (Rel_of _ P) x y)).
  Focus 2. 
intro. absurd (Is_a_minimal_element  P y). assumption.
unfold Is_a_minimal_element. split. (* apply minimal_element_cond. *) assumption.
intro. elim H3. destruct H5 as [x H5]. exists x. assumption.
trivial. }
(* at this point we have H3 as a crucial fact *)
(* this helps us get a point x0 strictly below y *)
(* we can have a point x0 below y and not equal to y 
   using this we proceed to prove that it (i.e, x0) doesnot belong to P_Above *)
(* we prove this using contradiction *)
destruct H3 as [x0 H3]. (* *)
assert (H5: ~ In _ (PO_Above_Carrier P la) x0 ).
intro. unfold In in H5. destruct H5. destruct H5. clear H6.
assumption. clear H6. destruct H7 as [y0 H6].
destruct H3 as [H3c H3]. destruct H3 as [H3d H3].
destruct H6 as [H6a H6].
assert ( H7: Rel_of U P y0 y).  (* we prove that y0 R y using transitivity *)
assert (H8: Order U (Rel_of U P)).
apply PO_cond2. destruct H8. apply H8 with (y:= x0).
assumption. assumption.
(* now using antichain condition H we prove that y0= y *)
destruct H. 
assert (H9: y0 = y). apply H8. unfold Included. intros.
destruct H9. assumption. assumption. left. assumption.
(* now we prove R y x0 by rewriting *)
assert (H10: Rel_of U P y x0 ). rewrite <- H9. assumption.
(*using antisymmetricity we prove that y= x0 because y R x0 and x0 R y are true *)
assert (H11: Order U (Rel_of U P )).
apply PO_cond2. destruct H11. assert (H14: y= x0).
apply H13. assumption. assumption. (*now we have contradiction as x0<>y and x0=y *)
absurd (y=x0). assumption. assumption.
(* here we already proved that x0 is not in P_Above *)
(* Moreover we know that x0 is in P *)
(* hence we can prove that P_Above is not same as P using Lemma Sets_not_equal *)


(* Which proves that P_Above is strictly included in P *)
apply (Sets_not_equal). right. exists x0. split. 
 assumption. destruct H3 as [H3c H3]. assumption.

 (* the 1st_halfCASE is OVER HERE *)
 intro.  (* 2nd HalfCASE when y belongs to Minimal but not to la *)
destruct H3 as [y H3]. destruct H3 as [H3a H3b].
assert (H4: ~ In _ (PO_Above_Carrier P la) y). intro.
(* assuming y belongs to P_Above we produce contradiction *)
destruct H3. destruct H3. assumption. clear H4. destruct H5 as [x H4]. destruct H4 as [H4a H4b].
{ elim (EM (x=y)). (* we produce contradiction in both cases *)
  Focus 2.
  intro. (*CASE x<>y   in this case we prove y is not minimal *)
destruct H3a.
assert (H6a: (exists y0 : U, In U (Carrier_of U P) y0 /\ y <> y0 /\ Rel_of U P y0 y)).
exists x.
split. destruct H. destruct H.  unfold Included in H. apply H. assumption.
split. intro. symmetry in H7. elim H4.  assumption. assumption.
(* In this case H6 and H6a are contradictory *)
elim H6. assumption.
intro. (*CASE x=y in this case since x belongs la hence y belongs la which contradicts H3b*)
rewrite H4 in H4a. elim H3b. assumption.  }
(* here we could prove that y is not in P_Above, hence it is strictIncluded in P  *)
apply (Sets_not_equal). right. exists y.
split.  simpl. assumption.
destruct H3a. assumption.  } Qed.         




  Inductive Chain_Joined (c1 c2 : Ensemble (Ensemble U))(la: Ensemble U)(e: Ensemble U):Prop:=
  Entry_cond: (exists (e1 e2: Ensemble U)(a: U), In _ la a /\ In _ c1 e1 /\ In _ c2 e2 /\
              In _ e1 a /\ In _ e2 a /\ e = Union _ e1 e2) -> Chain_Joined c1 c2 la e.



  Definition P_remains_A (P: FPO U)(A: Ensemble U)(proof1: Inhabited _ A)(proof2: Finite _ A):
       FPO U :=  {| PO_of:= {| Carrier_of :=  A;
               Rel_of := Rel_of _ P;
               PO_cond1 := proof1;
               PO_cond2 := PO_cond2 _ P |};
               FPO_cond := proof2
            |}.
  Lemma exists_P_small:
       forall (P: FPO U)(A: Ensemble U)(proof1: Inhabited _ A)(proof2: Finite _ A),
       exists (P_small: FPO U), P_small = P_remains_A P A proof1 proof2.
  Proof. {
      intros. exists (P_remains_A P A proof1 proof2).
            reflexivity. } Qed.
 
      
           

  

 Definition DilworthB_statement:= fun (P: FPO U)=> forall (m: nat),
                 (exists (a: Ensemble U ), Is_largest_antichain_in  P a /\ cardinal _  a m) ->
                 (exists (cv: Ensemble (Ensemble U)), Is_a_chain_cover P cv /\
                      cardinal _ cv m).



 Theorem DilworthB: forall (P: FPO U), DilworthB_statement P.
 Proof. { 
   
    (* We will prove the result by well founded induction on the set of all partial order. 
       To use the well founded induction we first need to prove that the Inside relation is
       well founded on PO U.  This is claimed by Lemma Inside_is_WF *)
    Check well_founded_ind.
    apply well_founded_ind with (R:= Inside U ). 
         apply Inside_is_WF.
         intros P IH.
         unfold DilworthB_statement.
         intros m . intros.
         
         assert(H98: Order _ (Rel_of _ P)).
         Print FPO. apply PO_cond2.

      (* We will break the proof in two cases. First one is when Minimal_Elements and 
     Maximal_Elements are not the carrier of the largest anntichain la. 
     Second case is when either Minimal_elements_of or Maximal_elements_of is the
      carrier of largest antichain la. *)

         elim( EM (forall (la: Ensemble U),
                     (Is_largest_antichain_in P la)->
                     (la = Maximal_elements_of  P \/ la = Minimal_elements_of  P))).
         Focus 2.

 -   intro CASE1Before.

         assert (CASE1: exists la: Ensemble U, Is_largest_antichain_in  P la /\
                ~( la = Maximal_elements_of  P \/ la = Minimal_elements_of  P)). 
         { apply Negation3. apply CASE1Before. }

         destruct CASE1 as [la CASE1]. destruct H as [la' H99]. destruct CASE1 as [H CASE1].

         assert(H0: cardinal U la m).
         { Check Largest_card_same.
         apply Largest_card_same with (e1:= la')(FP:=P).
         apply H99. assumption. apply H99. }

         
          


  (* CASE1: ~(la = Maximal_elements_of \/ la = Minimal_elements_of)  *)


  elim exists_above with (P:=P) (e :=la). (* We wish to say let P_Above:= (PO_Above P la)*)
  intros P_Above. intro.
  elim exists_below with (P:=P) (e :=la).
  intros P_Below. intro. (* at this point we have P_Above and P_Below with  desired property *)

  assert (CASE1a: la <> Maximal_elements_of  P /\ la <> Minimal_elements_of  P).
  { split. intro. rewrite H3 in CASE1. elim CASE1. left. reflexivity.
  intro. elim CASE1. right. assumption. }
  destruct CASE1a as [CASE1a CASE1b]. (* we know here that la <> Maximal and la <> Minimal *)

  (* We need to prove that P_Above and P_Below is Inside P *)
   assert(HInside: Inside _ P_Above P /\ Inside _ P_Below P ).
   { destruct H. 

   (* We shall first  prove "Inside P_Above P" *)
   split. rewrite H1. apply PO_Above_inside_P. assumption. assumption.
   (* We now prove that "Inside P_Below P" *)
   rewrite H2.  apply PO_Below_inside_P. assumption.
   assumption. }
   destruct HInside as [HInside1 HInside2].

 (*Since P_Above and P_Below are Inside P we can use IH to obtain chain_cover c1 and c2 for
  P_Above and P_Below . This is done in the following steps. In doing so we claim that la is 
  the largest antichain of P_Above and P_Below. This we need to prove seperately.  *)

   unfold DilworthB_statement in IH.

  (* Following steps extracts a chain cover c1 for P_Above *)
    assert(IH1: exists cv : Ensemble (Ensemble U),
              Is_a_chain_cover  P_Above cv /\ cardinal (Ensemble U) cv m).
     { apply IH. assumption. exists la. split.

    (* WE need to prove that la is the largest antichain of P_Above before we can extract c1.*)
      (*GOAL1: Is_largest_antichain_in _ P_Above la *)
      apply  Largest_antichain_remains with (P2:= P).
        (*SubGoal: Inside P_Above P *) assumption.
        (*SubGoal: Included U la (Carrier_of U P_Above )*)
        rewrite H1. simpl. apply la_in_P_Above.                  (* CHAIN COVER :: C1 *)
        destruct H. assumption.  assumption.
        (*GOAL2: cardinal U la m *)
        assumption. }
    destruct IH1 as [c1 IH1]. destruct IH1 as [IH1a IH1b].
  (* c1 exracted at this point *)   


  (*Following steps extracts a chain cover c2 for P_Below *)
    assert(IH2: exists cv : Ensemble (Ensemble U),
         Is_a_chain_cover  P_Below cv /\ cardinal (Ensemble U) cv m).
     { apply IH. assumption. exists la. split.

    (*GOAL1: Is_largest_antichain_in _ P_Below la *)
     apply  Largest_antichain_remains with (P2:= P).
     (*SubGoal: Inside P_Below P *) assumption.
     (*SubGoal: Included U la (Carrier_of U P_Below )*)
     rewrite H2. simpl. apply la_in_P_Below.                     (* CHAIN COVER :: C2 *)
     destruct H. assumption.  assumption.
     (*GOAL2: cardinal U la m *)  assumption. }
    destruct IH2 as [c2 IH2]. destruct IH2 as [IH2a IH2b].
  (*c2 extracted at this point *)

     (* SHORTHAND "cover" for Chain_joined c1 c2 la *)
     pose (cover:= Chain_Joined c1 c2 la). assert (H3: True). auto. 
(*  elim exists_cover with (c1:=c1)(c2:=c2)(la:=la).              (* COVER == Chain_joined  *)
  intro cover. intro H3. *)

 (* importent facts about c1, c2 and la *)
  (* every chain in c1 passes through some element of la *)  
   assert (Hc1: forall (e: Ensemble U), In _ c1 e -> (exists a:U, In _ la a /\ In _ e a) ).
     { apply Bijection_Relation with (n:=m).
     destruct IH1a.
     intros.
     assert(H7:In U (Carrier_of U P_Above) x ).
          Check la_in_P_Above.
          assert(H8: Included U la (PO_Above_Carrier P la)).
                 apply la_in_P_Above. apply H.
                 rewrite H1. apply H8. assumption.
     apply H5. assumption. (* bijection property *)
     intros.   (*This will be true. Otherwise two antichain element will lie on same chain *)
     apply NoTwoCommon with (P:=P)(X:=b)(Y:=la).
     repeat (destruct  H4). destruct H5. destruct H6. destruct H7.
     assert(H9: Is_a_chain_in  P_Above b). Print Is_a_chain_cover. 
           destruct IH1a as [IH1aA IH1a]. apply IH1aA. assumption.
     apply Chain_remains with (P1:= P_Above). rewrite H1.
     apply PO_Above_inside_P. apply H. assumption. assumption. apply H.
     unfold Included. intros. destruct H5. apply H4. apply H4.
     unfold Included. intros. destruct H5. apply H4. apply H4. assumption.
     assumption. } 
  (* Hc1 prooved *)

  (* every chain in c2 passes through some element of la *)
  assert (Hc2: forall (e: Ensemble U), In _ c2 e -> (exists a:U, In _ la a /\ In _ e a) ).
     { apply Bijection_Relation with (n:=m).
     destruct IH2a.
     intros.
     assert(H7:In U (Carrier_of U P_Below) x ).
           Check la_in_P_Below.
           assert(H8: Included U la (PO_Below_Carrier P la)).
                  apply la_in_P_Below. apply H.
                  rewrite H2. apply H8. assumption.
     apply H5. assumption. (* bijection property *)
     intros.   (*This will be true. Otherwise two antichain element will lie on same chain *)
     apply NoTwoCommon with (P:=P)(X:=b)(Y:=la).
     repeat (destruct  H4). destruct H5. destruct H6. destruct H7.
     assert(H9: Is_a_chain_in  P_Below b). Print Is_a_chain_cover. 
            destruct IH2a as [IH2aA IH2a]. apply IH2aA. assumption.
     apply Chain_remains with (P1:= P_Below). rewrite H2.
     apply PO_Below_inside_P. apply H. assumption. assumption. apply H.
     unfold Included. intros. destruct H5. (apply H4). apply H4.
     unfold Included. intros. destruct H5. apply H4. apply H4. assumption.
  assumption. }
  (* Hc2 prooved *) 
  

 exists cover.
     
  (* We need to prove that cover is a chain cover for the whole P *)
  (* PROOF IDEA: We need to prove that for every element of P there is a chain in cover. 
                 every chain in cover is made up of e1 a e2 where e1 is a chain from c1,
                 "a" is an element of la and e2 is from c2. Thus for every element of P
                 we extract these three component and proove that it lies in "cover" using 
                 definition of cover  *)
  assert (Above_or_Below:
           (Carrier_of _ P) =  Union _ (PO_Above_Carrier P la ) (PO_Below_Carrier P la)).
      { apply P_Above_or_P_Below. apply H. } 
  
  assert (H3a: Is_a_chain_cover  P cover ). 
      
      { apply cover_cond.
        
    - (* Goal1: every e in cover is a chain carrier *)
      destruct IH1a as [IH1aA IH1a].
      destruct IH2a as [IH2aA IH2a].
      intros e He. unfold cover in He. (* rewrite H3 in He. *) destruct He.
      destruct H4 as [e1 H4]. destruct H4 as [e2 H4]. destruct H4 as [a H4].
      destruct H4 as [H4a H4]. destruct H4 as [H4b H4]. destruct H4 as [H4c H4].
      assert(H5: e = Union U e1 e2). apply H4. 
      assert(T1A: Is_a_chain_in  P_Above e1 ). apply IH1aA. assumption.
      assert(T1B: Is_a_chain_in  P e1 ).
             apply Chain_remains with (P1:= P_Above). assumption. assumption.
      assert(T2A: Is_a_chain_in  P_Below e2). apply IH2aA. assumption.
      assert(T2B: Is_a_chain_in  P e2).       
             apply Chain_remains with (P1:= P_Below). assumption. assumption.
      assert(T1: Included _ e1 (Carrier_of _ P_Above)). apply T1A.
      assert(T2: Included _ e2 (Carrier_of _ P_Below)). apply T2A.
      
      unfold Is_a_chain_in. split. 
      + (*SubgoalA: Included U e (Carrier_of U P) /\ Inhabited U e *)
      
      split. (* Subgoal1: e is included in P *)
             assert(H6a: Included _ e1 (Carrier_of U P)).  apply T1B.
             assert(H6b: Included _ e2 (Carrier_of U P)). apply T2B.
             rewrite H5.  unfold Included.  intros. destruct H6.
             apply H6a. assumption. apply H6b. assumption.

             (* Subgoal2: Inhabited e *)
             apply Inhabited_intro with (x:=a). rewrite H5. apply Union_introl.
             apply H4.

       + (* SubgoalB: every e in cover is a chain *)
                     
         intros.
         assert(H7: In _ e x ). apply H6. apply Couple_l.
         assert(H8: In _ e y ). apply H6. apply Couple_r.
         rewrite H5 in H7. rewrite H5 in H8.
         destruct H7. destruct H8.
         (* Case1: when both x and x0 belong to e1 *)
            { assert(H9: Is_a_chain_in  P_Above e1). apply T1A.
             destruct H9. rewrite H1 in H10. simpl in H10. apply H10.
             unfold Included. intros. destruct H11. assumption. assumption. }
         (* Case2: when x in e1 and x0 in e2 *)
         
            { assert(H9: Rel_of U P a x).  
               assert(H10: Rel_of U P a x \/ Rel_of U P x a).
               assert(H11:  Is_a_chain_in P e1). apply T1B.
                     destruct H11 as [H11 H11a]. apply H11a. unfold Included.
                     intros. destruct H9. apply H4. assumption.
               elim H10.
               trivial.
               intro H11. 
               assert(H11a: x= a). 
                  apply No_smaller_element_Above with (P:=P) (la:=la).
                  assumption. rewrite <- H1. apply T1. assumption.
                  repeat (try split ; assumption).
               rewrite H11a. apply H98.       

            assert(H10: Rel_of U P x0 a).
               assert(H10: Rel_of U P a x0 \/ Rel_of U P x0 a).
               assert(H11: Is_a_chain_in  P e2). apply T2B.
                     destruct H11 as [H11 H11a]. apply H11a. unfold Included.
                     intros. destruct H10. apply H4. assumption.
               elim H10. 
               intro H11. 
               assert(H11a: x0 = a). 
                  apply No_bigger_element_Below with (P:=P) (la:=la).
                  assumption. rewrite <- H2. apply T2. assumption.
                  repeat (try split ; assumption).
               rewrite H11a. apply H98.
               trivial.

             right. destruct H98. unfold Transitive in H12. apply H12 with (y:=a).
             assumption. assumption. }
             destruct H8.
         (* Case3: when x in e2 and x0 in e1 *)
             { assert(H9: Rel_of U P a x0).
                 assert(H10: Rel_of U P a x0 \/ Rel_of U P x0 a).
                 assert(H11: Is_a_chain_in   P e1). apply T1B.
                     destruct H11 as [H11 H11a]. apply H11a. unfold Included.
                     intros. destruct H9. apply H4. assumption.
                 elim H10.
                 trivial.
                 intro H11. 
                 assert(H11a: x0= a). 
                     apply No_smaller_element_Above with (P:=P) (la:=la).
                     assumption. rewrite <- H1. apply T1. assumption.
                     repeat (try split ; assumption).
                 rewrite H11a. apply H98.

            
             assert(H10: Rel_of U P x a).
                  assert(H10: Rel_of U P a x \/ Rel_of U P x a).
                  assert(H11: Is_a_chain_in   P e2). apply T2B.
                     destruct H11 as [H11 H11a]. apply H11a. unfold Included.
                     intros. destruct H10. apply H4. assumption.
                  elim H10. 
                  intro H11. 
                  assert(H11a: x = a). 
                      apply No_bigger_element_Below with (P:=P) (la:=la).
                      assumption. rewrite <- H2. apply T2. assumption.
                      repeat (try split ; assumption).
                  rewrite H11a. apply H98.
                  trivial.

            left. destruct H98. unfold Transitive in H12. apply H12 with (y:=a).
            assumption. assumption. }
             
         (* Case4: when both x and x0 belongs to  e2  *)
             { assert(H9: Is_a_chain_in  P_Below e2). apply IH2aA. assumption. 
             destruct H9. rewrite H2 in H10. simpl in H10. apply H10.
             unfold Included. intros. destruct H11. assumption. assumption. }
      (* Goal1 completed here *)      
                   
                         
     - (* Goal2: every x in P lies on some e in cover *)
        intros x Hx.  rewrite Above_or_Below in Hx.
         destruct Hx.
         (* CaseA: H4 : When x lies in P_Above  *)
         assert(T1: exists (e1: Ensemble U), In _ c1 e1 /\ In _ e1 x).
              apply IH1a. rewrite H1. simpl. assumption.
         destruct T1 as [e1 T1].
         assert(T2: exists a:U, In _ la a /\ In _ e1 a ).
              apply Hc1. apply T1. 
         destruct T2 as [a T2].
         assert(T3: exists  (e2:Ensemble U), In _ c2 e2 /\ In _ e2 a).
              apply IH2a. rewrite H2. simpl.
              assert(Temp: Included _ la (PO_Below_Carrier P la) ).
                    apply la_in_P_Below. apply H.
              apply Temp. apply T2.
         destruct T3 as [e2 T3].
         exists (Union _ e1 e2).
         split. (* Subgoal : e1 U e2 is in cover *)
              unfold cover. (* rewrite H3. *) unfold In. apply Entry_cond.
              exists e1. exists e2. exists a. split.
              apply T2. split. apply T1. split. apply T3. split.
              apply T2. split. apply T3. reflexivity.
               (*Subgoal: x belongs to e1 U e2 *)
              apply Union_introl. apply T1.
              
         (* CaseB: H4: When x lies in P_Below  *)
         assert(T1: exists (e2: Ensemble U), In _ c2 e2 /\ In _ e2 x).
              apply IH2a. rewrite H2. simpl. assumption.     
         destruct T1 as [e2 T1].     
         assert( T2: exists a:U, In _ la a /\ In _ e2 a).
              apply Hc2. apply T1.
         destruct T2 as [a T2].
         assert(T3: exists (e1: Ensemble U), In _ c1 e1 /\ In _ e1 a).     
              apply IH1a. rewrite H1. simpl.
              assert(Temp: Included _ la (PO_Above_Carrier P la)).
                    apply la_in_P_Above. apply H.
                    apply Temp. apply T2.
         destruct T3 as [e1 T3].           
         exists (Union _ e1 e2).
         split. (* Subgoal: e1 U e2 is in cover *)
              unfold cover (* rewrite H3. *). unfold In. apply Entry_cond.  
              exists e1. exists e2. exists a.
              repeat (split ; try (apply T2); try (apply T1); try (apply T3)).
              (* Subgoal: x belongs to e1 U e2 *)
              apply Union_intror. apply T1.
       (* Goal2 completed here *)
       }        
              
  split.  
   apply H3a. 

  
    (* We need to prove that cardinality of cover is m *)
   (* We prove this by contradiction. we will assume that cardinality of cover is n .
      and assuming m<>n we will produce a contradiction. But before we can say that let 
      cardinality    of cover be n we need to prove that cover is finite. *)
    assert (HF: Finite _ cover).
     { (*we can prove this by proving that cover is included in the power set of P and P is 
     finite hence any subset of its power set is also finite *)
     (* For now we assume it *) 
      assert (CoverIncluded: Included _ cover (Power_set _ (Carrier_of _ P))).
      { unfold Included.
      destruct IH1a as [IH1aA IH1a].
      destruct IH2a as [IH2aA IH2a].
      intros e He. unfold cover in He. destruct He.
      destruct H4 as [e1 H4]. destruct H4 as [e2 H4]. destruct H4 as [a H4].
      destruct H4 as [H4a H4]. destruct H4 as [H4b H4]. destruct H4 as [H4c H4].
         assert(H5: e = Union U e1 e2). apply H4. 
         assert(T1A: Is_a_chain_in   P_Above e1 ). apply IH1aA. assumption.
         assert(T1B: Is_a_chain_in   P e1 ).
             apply Chain_remains with (P1:= P_Above). assumption. assumption.
         assert(T2A: Is_a_chain_in   P_Below e2). apply IH2aA. assumption.
         assert(T2B: Is_a_chain_in   P e2).       
             apply Chain_remains with (P1:= P_Below). assumption. assumption.
         assert(T1: Included _ e1 (Carrier_of  _ P_Above)). apply T1A.
         assert(T2: Included _ e2 (Carrier_of  _ P_Below)). apply T2A.
       
      assert(H88: Included U e (Carrier_of U P)).
            { assert(H6a: Included _ e1 (Carrier_of U P)).  apply T1B.
             assert(H6b: Included _ e2 (Carrier_of U P)). apply T2B.
             rewrite H5.  unfold Included.  intros. destruct H6.
             apply H6a. assumption. apply H6b. assumption. }

      apply Definition_of_Power_set. apply H88. }

      apply Finite_downward_closed with (A:= Power_set U (Carrier_of U P)).
      apply Power_set_finite. apply FPO_cond.
      assumption. }
          

    elim finite_cardinal with (U:=Ensemble U)(X:= cover).
     intro n. intro H4. (*At this point we have assumed n to be cardinality of cover *)
     
    (* We prove that m<>n is not posiible and hence using EM we have m=n proved *)
     elim (EM (m=n)). 
     Focus 2. 
    intro.
    (*CASE  m<>n:  In this case either m<n or m>n . When m>n  antichain elements are more 
        in number than the number of chains in a chain cover "cover". This contradicts 
        Theorem DilworthA. *) 
      
        assert (H6: m<n \/ m>n).
        apply  (Not_equal_means_lt_or_gt). assumption.

        elim H6.
        (* SubCASE m<n: we need a proof here*)
        intro H7.
        (* Here if chains in cover is more than elements in la then two chains e1 and e2
           will pass through same element a (where a:la ). *)
        assert (H8: exists (e1 e2 : Ensemble U)(a: U), In _ cover e1 /\ In _ cover e2 /\ In _ la a /\
                                                  e1 <> e2 /\ (In _ e1 a /\ In _ e2 a )).
        { apply Pigeon_Relation with (n:=n) (m:=m).
          { intros e He. unfold cover in He. destruct He.
            destruct H8 as [e1 H8]; destruct H8 as [e2 H8]; destruct H8 as [a H8].
            exists a.   split. apply H8. replace e with (Union U e1 e2). apply Union_intror.
            apply H8. symmetry. apply H8. }
          assumption. assumption. assumption.  

        }
        destruct H8 as [e1 H8]. destruct H8 as [e2 H8].
        destruct H8 as [a H8].
        destruct H8 as [H8a H8]. destruct H8 as [H8b H8].
        destruct H8 as [H8c H8]. destruct H8 as [H8d H8].

        unfold cover in H8a, H8b.

        assert (He2: Is_a_chain_in  P e2 ). {
          destruct H3a. apply H9.  unfold cover.  assumption.  }
        assert (He1: Is_a_chain_in   P e1 ). {
          destruct H3a. apply H9.  unfold cover.  assumption.  }

        destruct H8a. destruct H9 as [e1u H9]. destruct H9 as [e1d H9]. destruct H9 as [a1 H9]. 

        destruct H8b. destruct H10 as [e2u H10]. destruct H10 as [e2d H10].
        destruct H10 as [a2 H10].

        assert(Ha_a1: a = a1 ). {
          assert (THe1: In _ e1 a1).
          { replace e1 with ( Union U e1u e1d ). apply Union_intror.  apply H9.
            symmetry. apply H9. }
          apply NoTwoCommon with (P:= P) (X:= e1) (Y:=la).  assumption.
          apply H.
          { unfold Included. intros. destruct H11. apply H8. assumption. }
          { unfold Included. intros. destruct H11. apply H8c. apply H9.  }
           } 


        assert (Ha_a2: a = a2 ). {
           assert (THe1: In _ e2 a2).
          { replace e2 with ( Union U e2u e2d ). apply Union_intror.  apply H10.
            symmetry. apply H10. }
          apply NoTwoCommon with (P:= P) (X:= e2) (Y:=la).  assumption.
          apply H.
          { unfold Included. intros. destruct H11. apply H8. assumption. }
          { unfold Included. intros. destruct H11. apply H8c. apply H10. }
          } 


        assert (H12: True). { tauto. }
        assert (H11: e1u = e2u ).
        { assert
            (TH11: (forall (x y: Ensemble U)(a: U), ( In _ c1 x /\ In _ c1 y /\ In _ la a /\
                                                 In _ x a /\ In _ y a )-> x= y)).
          { apply Bijection_Relation1 with (n:= m);
            repeat (assumption).
            
            { intros. apply IH1a. rewrite H1. apply la_in_P_Above. apply H. assumption. }
            { intros. apply NoTwoCommon with (X:= b) (Y:= la) (P:= P).
              apply Chain_remains with (P1:= P_Above). assumption.
              destruct IH1a. apply H13. apply H11. apply H.
              unfold Included.  intros. destruct H13. apply H11. apply H11.
              unfold Included.  intros. destruct H13. apply H11. apply H11. } 
            
          }
          symmetry. apply TH11 with (a:=a). rewrite <- Ha_a1 in H9 . rewrite <- Ha_a2 in H10.
          repeat (try(split); try (solve [ apply H9 |apply H10 ])) . } 

        clear H12.
                                                           
        assert (H12: e1d = e2d ). 
        { assert
            (TH12: (forall (x y: Ensemble U)(a: U), ( In _ c2 x /\ In _ c2 y /\ In _ la a /\
                                                 In _ x a /\ In _ y a )-> x= y)).
          { apply Bijection_Relation1 with (n:= m);
            repeat (assumption).
            
            { intros. apply IH2a. rewrite H2. apply la_in_P_Below. apply H. assumption. }
            { intros. apply NoTwoCommon with (X:= b) (Y:= la) (P:= P).
              apply Chain_remains with (P1:= P_Below). assumption.
              destruct IH2a. apply H13. apply H12. apply H.
              unfold Included.  intros. destruct H13. apply H12. apply H12.
              unfold Included.  intros. destruct H13. apply H12. apply H12. } 
            
          }
          symmetry. apply TH12 with (a:=a). rewrite <- Ha_a1 in H9 . rewrite <- Ha_a2 in H10.
          repeat (try (split); try ( solve [apply H9 | apply H10])). 
        } 

         assert (H13: e1 = e2 ).
         { replace e1 with (Union U e1u e1d) .
          replace e2 with (Union U e2u e2d) .
          rewrite H11. rewrite H12.  reflexivity.
          symmetry. apply H10 . symmetry. apply H9.  } 


        absurd ( e1 = e2). { assumption. } { assumption. }                         

        

        intro.
        (* SubCASE m>n: this is not possible due to DilworthA. We prove that ~(m>n). *)
        assert(H7b: ~(m>n)).
        { Check DilworthA.
        apply DilworthA with (P:=P)(m:=m)(n:=n)(cv:=cover)(a:=la).
        assumption. destruct H. assumption. assumption. assumption. }
        absurd(m>n). assumption.  assumption.     

     intro.
    (*CASE m=n: A simple rewrite will do *)
    { rewrite H5. assumption. }

    (* Goal: Finite _ cover. *) assumption. (* Already prooved as HF *) 




   (* ====================================================================================== *)
                                (* CASE 2 BEGINS HERE *)
   (* ====================================================================================== *)
 -  intro CASE2Before.
     destruct H as [la H].
     destruct H as [H H0].


     
(* CASE2: when la= Maximal_elements_of \/ Minimal_elements_of *)     
     assert (CASE2: la = Maximal_elements_of  P \/ la= Minimal_elements_of  P ).
     { apply CASE2Before. assumption. }
     
     elim Exists_pair_xy with (U:=U)(FP:=P).
     intro x0. intros.
     destruct H1 as [y0 H1].


     elim (EM (Inhabited _ (Setminus _ (Carrier_of _ P) (Couple _ x0 y0)))).
     Focus 2.

    (* trivial case ::  In this case {x0 y0} is the only chain in chain cover and chain 
        cover has size 1. we need to show that size of la is also 1  *)
     intro TrivialCase.
     exists (Singleton _ (Couple _ x0 y0) ).
     
     assert(H2: Carrier_of U P = Couple U x0 y0).
        {  apply Extensionality_Ensembles. split. {
             elim (EM(Included U (Carrier_of U P) (Couple U x0 y0))).
             Focus 2. intro T1.
         absurd(Inhabited U (Setminus U (Carrier_of U P) (Couple U x0 y0))).
         assumption. unfold Included in T1.
         assert(T2: exists x : U, In U (Carrier_of U P) x /\ ~ In U (Couple U x0 y0) x).
               apply Negation3. assumption.
         destruct T2. apply Inhabited_intro with (x:=x).
         unfold Setminus. unfold In. simpl. apply H2.
         trivial. }
         unfold Included. intros. destruct H2. apply H1. apply H1. }
         (* Prooved H2 ----- *)      

     split.
    * (* Goal {{x0, y0}} is a chain cover *)
      { Print Is_a_chain_cover.
        apply cover_cond. intros. destruct H3.
      - (*Subgoal {x0, y0} is a chain carrier *)
       unfold Is_a_chain_in . split.  split.
        { rewrite H2. unfold Included. trivial. }
        { apply Inhabited_intro with (x:=x0). apply Couple_l. }
        (* every element in cover is a chain *)
        { intros x y H3. unfold Included in H3.
          assert (H4: In U (Couple U x0 y0) x /\ In U (Couple U x0 y0) y).
           { split. apply H3. apply Couple_l. apply H3. apply Couple_r. }
          destruct H4. destruct H4. destruct H5.
          destruct H98 as [H98a H98b H98c].
          left. apply H98a. left. apply H1. destruct H5.
          right. apply H1. left. apply H98. }

       - (* Subgoal: for every element in there is a chain in {{ x0, y0}} *)
         { intros. rewrite H2 in H3.
         destruct H3. exists (Couple U x0 y0).
         split. apply In_singleton. apply Couple_l.
         exists (Couple U x0 y0). split. apply In_singleton.
         apply Couple_r. }
       } 

      (* Prooved Goal: {{x0, y0}} is a chain cover *) 
     
     * (* Goal : m=1, and hence cardinality of {{x0, y0}} is one and *)
       assert(H3: m=1). {
       assert(T1: Included _ la (Couple U x0 y0)).
            rewrite <- H2. apply H.

       assert(TF2: m < 2). {
       elim (EM (x0 = y0)). Focus 2. 
       
           intro T2a. (* Case: when x0<>y0 *)
           assert(T3: cardinal _ (Couple U x0 y0) (S 1)).
           apply Couple_card_2. assumption.
            
           assert(T4: Strict_Included _ la (Couple U x0 y0)). {
              split.  assumption.
              elim (EM ( In _ la x0)). Focus 2. 
              intro T4. apply Sets_not_equal. right. exists x0. split.
              assumption. apply Couple_l.
              intro t4. apply Sets_not_equal. right. exists y0. split.
              intro. destruct H. destruct H. absurd (x0=y0).
              assumption. apply H5. unfold Included.
              intros. destruct H6. assumption. assumption. left. apply H1.
              apply Couple_r. }

           apply incl_st_card_lt with (U:=U)(X:= la)(Y:= (Couple U x0 y0)).
           assumption. apply T3. apply T4.
              
           intro T2b. (* Case : when x0= y0 *)
           assert(T3: cardinal _ (Couple U x0 y0) 1). {
              apply Couple_card_1. assumption. }
           assert(T4: m <=1). {
                   apply incl_card_le with (U:=U)(X:= la)(Y:= (Couple U x0 y0)).
                   assumption. assumption. assumption. }
           apply le_lt_n_Sm.
           assumption.  }

       assert(TF3: m>0). {
              apply inh_card_gt_O with (U:=U) (X:= la).
              apply H. assumption. }

       apply Middle_num. split. unfold gt in TF3. apply TF3. apply TF2. } 

       rewrite H3.
       Check Singleton_card. apply (Singleton_card). 

     (* Non trivial case: *)
       intro Nontrivial.

       assert(H80: Strict_Included _ (Setminus U (Carrier_of U P) (Couple U x0 y0))
                                   (Carrier_of U P)). {
       unfold Strict_Included.
       split. unfold Included. unfold Setminus. unfold In. intros. apply H2.
       apply Sets_not_equal. right. exists x0. split. unfold In. unfold Setminus.
       apply or_not_and. right.
       assert(Temp: In U (Couple U x0 y0) x0). apply Couple_l.
       intro. absurd(In U (Couple U x0 y0) x0). assumption. assumption.
       (*Subgoal: In U (Carrier_of U P) x0 *)
       destruct H1. destruct H1. apply H1. }


       assert (Finite_small: Finite _ (Setminus U (Carrier_of U P) (Couple U x0 y0))). {
       apply Finite_downward_closed with (A:= Carrier_of U P).
       Print FPO. apply FPO_cond. apply H80. }

       
       (* P_small represents P minus {x0, y0} *)
       elim exists_P_small with (P:=P)(A:= (Setminus U (Carrier_of U P) (Couple U x0 y0)))
                                      (proof1:= Nontrivial)(proof2:= Finite_small).
       intro P_small. intro H2.

       assert(H80a: Inside _ P_small P). {
       unfold Inside.
       split. rewrite H2. simpl. apply H80. rewrite H2. simpl.
       reflexivity. }


    (* At this point we have proof of the fact that P_small is finite and inhabited. *)

    (* We wish to extract a chain cover for P_small using induction hypothesis *)
       assert(IH1: DilworthB_statement P_small). {
       apply IH.
       (* Goal: Inside P_small P *)
       apply H80a. }

       
       unfold DilworthB_statement in IH1.

       (* NOTE: We need a lemma that says every FPO has a largest antichain *)
       (* Lemma exists_largest_antichain confirms this *)
       assert(H81: exists (m0:nat) (a: Ensemble U), Is_largest_antichain_in  P_small a /\
                                                    cardinal U a m0). {
       apply  exists_largest_antichain. } 
      
       destruct H81 as [m0 H81].
       assert(H82:  exists cv : Ensemble (Ensemble U),Is_a_chain_cover  P_small cv /\
                                                      cardinal (Ensemble U) cv m0). {
       apply IH1. assumption. }
       destruct H82 as [cv_small H82].
       
     (* chain cover for P_small extracted at this point as cv_small *)
       destruct H81 as [la0 H81].

   (* PROOF IDEA AHEAD: At this point we have a chain cover cv_small of size m0 for P_small. 
      We will  show that that cv_small added with {x0 y0} will cover the whole P. Moreover
      we show that cardinality of the (cv_small+ {x0, y0}) is m. We know that card of  
      (cv_small+ {x0, y0}) is m0+1. So we need to prove that m0+1= m. For this we prove
      two things (FACT2: m0 <> m) and (FACT1: m0<= m). Then this implies m0 < m (FACT3).
      which in turn implies m0+1 <= m (FACT4). At this point we also prove that
      (FACT5: ~(m0+1 < m)), because size of chain cover cannot be less than largest antichain
      size using DilworthA. Hence FACT4 and FACT5 gives us (FACT6: m0+1= m) *)     

       exists (Add _ cv_small (Couple _ x0 y0) ).
       assert(H83: Is_a_chain_cover  P (Add (Ensemble U) cv_small (Couple U x0 y0))). { 
       apply cover_cond.
           (*Subgoal: every e in (cv_small + {x0, y0}) is a chain *)
            intros. destruct H3. apply Chain_remains with (P1:= P_small).
            assumption. destruct H82 as [H82a H82b]. destruct H82a as [H82a1 H82a2].
            apply H82a1. apply H3.
            destruct H3.
            (* SubSubGoal: Couple U x0 y0 is a chain carrier *)
            unfold Is_a_chain_in . split.
             split. unfold Included. intros. destruct H3.
            apply H1. apply H1. apply Inhabited_intro with x0. apply Couple_l.
            intros. assert(H3a: In _ (Couple U x0 y0) x /\ In _ (Couple U x0 y0) y).
            split. apply H3. apply Couple_l. apply H3. apply Couple_r.
            destruct H3a.  destruct H4. destruct H5.
            left. apply H98. left. apply H1.
            destruct H5. right. apply H1. left. apply H98.

            intros.
            (* Subgoal: For every element x in P there is a chain in chain cover that contain x 
                 We prove this by assuming two cases. Whether or not  x belongs to {x0 y0}   *)
            elim (EM(In _ (Couple U x0 y0) x)). Focus 2.  intro CaseA.
            (* CaseA: ~ In U (Couple U x0 y0) x*)
             (* In this case x is in P_small hence there is a chain e in in cv_small that contain
                x. this chain is also present in (cv_small + {x0, y0})*)
                assert( CaseA1: In U (Carrier_of U P_small) x). rewrite H2.
                simpl. unfold In. unfold Setminus. split. assumption. assumption.

                assert(ExistE: exists e: Ensemble U, In _ cv_small  e
                                                     /\ In U e x ).
                      destruct H82 as [H82a H82b]. apply H82a. assumption.

                destruct ExistE as [e ExistE]. exists e. split.
                unfold Add. apply Union_introl. apply ExistE. apply ExistE.
            (* CaseB: In U (Couple U x0 y0) x *)
                (* In this case {x0, y0} is the chain that is in P and contains x *)
                intro CaseB.
                exists (Couple U x0 y0).
                split. unfold Add. apply Union_intror. apply In_singleton. apply CaseB. }

              (* Proof of assertion H83 completes here. This will be useful in many places *)   
       split.
       
      * (* Goal1: cv_small + {x0,y0} is a chain cover. *)
        apply H83. 

      * (*Goal2: cardinal of (cv_small + {x0,y0} ) is m *)

       assert(Fact0: cardinal _ (Add (Ensemble U) cv_small (Couple U x0 y0)) (S m0) ). {
       apply card_add. apply H82. 
          (* Subgoal:  ~ In (Ensemble U) cv_small (Couple U x0 y0) *)
          (* We prove this by contradiction . if {x0, y0} is in cv_small then it must be
             included in P_small . However this contradicts with definition of P_small *)
             intro Temp1. destruct H82 as [H82a H82b]. destruct H82a as [H82a1 H28a2].
             assert(Temp2: Is_a_chain_in  P_small (Couple U x0 y0)). apply H82a1.
                assumption. destruct Temp2. destruct H3. rewrite H2 in H3. simpl in H3.
                unfold Included in H3.
                absurd (In _ (Couple U x0 y0) x0).
                apply H3. apply Couple_l. apply Couple_l. }

       assert(Fact1: m0<= m ). {
       (* This should be true because m is the size of largest antichain of P and m0 is size
          of an antichain of P_small which is also an antichain of P. *)
           assert(H81a: Is_an_antichain_in  P la0 ).
           apply Antichain_not_changed2 with (P1:= P_small).
           apply H80a. apply H81. apply H81.
           Print Is_largest_antichain_in . destruct H.
           apply H3 with (e1:= la0). assumption. assumption. apply H81. }

       
       assert(Fact2: m0<> m ). {
       (* This should be true. Because if m0=m then la0 also becomes a largest antichain
          of P. Moreover, la0 is not Maximal or minimal because of the abscence of x0 and
          y0. thus there is a largest antichain la0 in P other than Maximal or Minimal. This 
          contradicts the hypothesis CASE2Before.  *)
          intro.
       
          assert(Ha: Is_largest_antichain_in  P la0).
          apply Card_same_largest with (e1:=la)(n:=m).
          assumption. apply Antichain_not_changed2 with (P1:= P_small).
          apply H80a. apply H81. apply H81. assumption. rewrite <- H3. apply H81.

          assert(NotCase2: ~(la0 = Maximal_elements_of  P) /\ ~(la0 = Minimal_elements_of  P)).
          split.

          (* SubGoal: la0 <> Maximal_elements_of *)
          apply Sets_not_equal.
          right. exists y0.
             split. destruct H81 as [H81a H81b].
             destruct H81a. destruct H4.
             (* SubSubGoal1: ~ In U la0 y0 *)
             intro.
                assert(H8: In U (Carrier_of U P_small) y0).
                destruct H4. apply H4. assumption.
                absurd (In U (Carrier_of U P_small) y0). rewrite H2. simpl.
                unfold Setminus. unfold In. apply or_not_and.
                right. assert(H8a: (Couple U x0 y0) y0). apply Couple_r.
                intro H8b. absurd (Couple U x0 y0 y0). assumption. assumption.
                assumption.
              (*SubSubGoal2: In U (Maximal_elements_of U P) y0 *)
              apply H1.  

          (* SubGoal: la0 <> Minimal_elements_of *)
          apply Sets_not_equal.
          right. exists x0.
             split. destruct H81 as [H81a H81b].
             destruct H81a. destruct H4.
             (* SubSubGoal1: ~ In U la0 x0 *)
             intro.
                assert(H8: In U (Carrier_of U P_small) x0).
                destruct H4. apply H4. assumption.
                absurd (In U (Carrier_of U P_small) x0). rewrite H2. simpl.
                unfold Setminus. unfold In. apply or_not_and.
                right. assert(H8a: (Couple U x0 y0) x0). apply Couple_l.
                intro H8b. absurd (Couple U x0 y0 x0). assumption. assumption.
                assumption.
              (*SubSubGoal2: In U (Maximal_elements_of U P) x0 *)
              apply H1.     
          

          absurd (la0 = Maximal_elements_of  P \/ la0 = Minimal_elements_of  P).
          apply and_not_or. assumption. apply CASE2Before. assumption. }
         
       
       assert(Fact3: m0 < m ). {
          assert(Fact1a: m0< m \/ m0 =m ).
          apply le_lt_or_eq. assumption.
          elim Fact1a. trivial.
          intro. absurd(m0=m). assumption. assumption. }
       
       assert(Fact4: S m0 <= m).
       apply Fact3.   
          
       assert(Fact5: ~(S m0 < m)). {
       Check DilworthA.
       Print DilworthA_statement.
       assert(H84: DilworthA_statement _ P).
       apply DilworthA. unfold DilworthA_statement in H84.
       apply H84 with (cv:=(Add (Ensemble U) cv_small (Couple U x0 y0)))(a:=la).
       assumption. apply H. apply Fact0. assumption. }
       
       assert(Fact6: S m0 = m). {
          assert(Fact4a: S m0 < m \/ S m0 = m).
          apply le_lt_or_eq. assumption.
          elim Fact4a. intro. absurd( S m0 < m). assumption. assumption. trivial. }



    rewrite <- Fact6. assumption.

 (* CASE2: Over Here *) }

Qed. 

       
End DilworthB.

       




     
     
     

    
     



  
  