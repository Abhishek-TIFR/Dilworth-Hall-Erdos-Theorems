(* In this file some more useful facts about finite posets are proved as lemmas. 
   Following is a partial list of some of them  -------------------------------
     
DEFINITIONS: ------------------------------------------------------------------
1. Inside P1 P2: it is a binary relation which becomes true when the carrier set of 
                 poset P1 is strictly included in the carrier set of poset P2.   
2. Included_in P2 P1: it is a binary relation which becomes true when the carrier set
                      of poset P1 is included in carrier set of poset P2. 
3. Is_largest_set E e: e is the largest set among all the sets present in E.

4. Is_smallest_set E e: e is the smallest set among all the sets present in E.

SOME IMP RESULTS: -------------------------------------------------------------
1. Lemma Inside_is_WF: Inside relation on finite posets is well founded.

2. Lemma Largest_Chain_remains: If P1 is included in P2 and e is a largest chain in P2
                                then e is also a largest chain in P1 provided e is con-
                                -tained in P1.

3. Lemma Largest_Antichain_remains: If P1 is included in P2 and e is a largest antichain 
                                 in P2 then e is also a largest antichain in P1 provided e
                                 is contained in P1.

4. Lemma MaxExists: Every Finite non-empty subset of natural numbers has a maximum.

5. Lemma MinExists: Every Finite non-empty subset of natural numbers has a minimum.

6. Lemma Largest_set_exists: Let E be a non-empty finite collection of finite sets.
                             Then, there exists a largest cardinality set e in E.

7. Lemma Smallest_set_exists: Let E be a non-empty finite collection of finite sets.
                             Then, there exists a smallest cardinality set e in E.

8. Lemma exists_largest_antichain: There exists a largest antichain in every finite poset.

9. Lemma exists_largest_chain: There exists a largest chain in every finite poset.

10.Lemma exists_disjoint_cover: If cv is a smallest chain cover of poset P of size m,
                                then there also exists a disjoint chain cover of P of
                                size m.  *)
    


Require Export PigeonHole.
Require Export BasicFacts.

Require Export FPO_Facts.
Require Export omega.Omega.



    (* ----------------------INSIDE RELATION AND SOME PROPERTIES OF IT ----------------------- *)
    (* --------------------------------------------------------------------------------------- *)

Section Inside_Property.

  Variable U: Type.

Definition Inside (P1: FPO U)(P2: FPO U):Prop:=
  Strict_Included _ (Carrier_of _ P1) (Carrier_of _ P2) /\  Rel_of U P1 = Rel_of U P2 .

Definition Included_in (P2: FPO U)(P1: FPO U): Prop:=
  Included _ (Carrier_of _ P1) (Carrier_of _ P2) /\ Rel_of U P1 = Rel_of U P2 .


Lemma Inside_is_WF: well_founded Inside.
Proof. {
        - unfold well_founded. intro P'. 
       
          assert(H: exists n:nat, cardinal _ (Carrier_of _ P') n ).  
            { apply finite_cardinal;
              apply Finite_PO. }
            
          destruct H as [n0 H]. (*let n0 be cardinality of P' *)
          generalize H. generalize P'. generalize n0 as n.
          induction n using strong_induction.
          intros P2 H1.  (* cardinality of P2 is n *)
          apply Acc_intro.
          intros P1 H2. (*let P1 be Included in P2 *)
          
          assert(H3: exists m:nat, cardinal _ (Carrier_of _ P1) m).
            { apply finite_cardinal. apply Finite_PO. }
          
          destruct H3 as [m H3]. (*let m be the cardinality of P1 *)
          apply H0 with (k:= m).
        (* GOAL: to prove that m <n . i,e Carrier of P1 is strict_included in P2  *)
          assert(H4: Strict_Included _ (Carrier_of _ P1) (Carrier_of _ P2)).
           { unfold Inside in H2. destruct H2 as [H2a H2]. assumption. }

          + { apply strict_included_card_less with
              (U:=U) (e1:= Carrier_of _ P1)(e2:= Carrier_of _ P2).
            
            * assumption.
            * assumption.
            * assumption. }

          + assumption.  } Qed.

 

  Lemma Chain_remains: forall (P1 P2: FPO U)(e: Ensemble U),
                       Inside P1 P2 -> Is_a_chain_in P1 e -> Is_a_chain_in P2 e.
  Proof. { intros. unfold Is_a_chain_in. unfold Is_a_chain_in in H0.
           unfold Inside in H. destruct H0 as [H0 H1]. destruct H0 as [H0 H2].
           destruct H as [T1 T2]. unfold Strict_Included in T1.
           destruct T1 as [T0 T1]. 
           split.
           { split.
             {  auto with sets.  }
             { auto. }  }

           rewrite <- T2. apply H1.  }  Qed.

  Lemma Chain_remains1: forall (P1 P2: FPO U)(e: Ensemble U),
                       Included_in P2 P1 -> Is_a_chain_in P1 e -> Is_a_chain_in P2 e.
  Proof.  { intros. unfold Is_a_chain_in. unfold Is_a_chain_in in H0.
           unfold Included_in in H. destruct H0 as [H0 H1]. destruct H0 as [H0 H2].
           destruct H as [T1 T2].  
           split.
           { split.
             {  auto with sets.  }
             { auto. }  }

           rewrite <- T2. apply H1.  }  Qed. 

  Lemma Chain_remains2:  forall (P1 P2: FPO U)(e: Ensemble U),
      Included_in P2 P1 -> Included _ e (Carrier_of _ P1) -> Is_a_chain_in P2 e ->
      Is_a_chain_in P1 e.
    Proof.  { intros. unfold Is_a_chain_in. unfold Is_a_chain_in in H1.
           unfold Included_in in H. destruct H as [F0 F1]. destruct H1 as [H1 H2].
           destruct H1 as [T1 T2].  
           split.
           { split.
             {  auto with sets.  }
             { auto. }  }

           rewrite  F1. apply H2.  }  Qed.

  Lemma Largest_Chain_remains:  forall (P1 P2: FPO U)(e: Ensemble U),
    Included_in P2 P1 -> Included _ e (Carrier_of _ P1) ->
    Is_largest_chain_in  P2 e -> Is_largest_chain_in  P1 e.
  Proof. { intros. apply_fpo_def.
           { eapply Chain_remains2 with (P2:=P2);(tauto || apply H1). }
           { intros. destruct H1. apply H5 with (e1:=e1).
             eapply Chain_remains1 with (P1:=P1); tauto. tauto. tauto. }  } Qed. 




 Lemma  Antichain_not_changed:
         forall (P1 P2: FPO U)(e: Ensemble U),
           Inside  P1 P2 -> Included _ e (Carrier_of _ P1) ->
           (Is_an_antichain_in  P2 e <-> Is_an_antichain_in P1 e ).
 Proof. {
   intros. unfold iff. split.
  * (* CASE1: Is_an_antichain_in U P2 e -> Is_an_antichain_in U P1 e *)
   intro. destruct H1.
   destruct H1 as [H1a H1]. 
   unfold Is_an_antichain_in. split.
   
   + { split.  - assumption. - assumption. }
   + { unfold Inside in H. destruct H as [Ha Hb].
       rewrite Hb. assumption. }
  * (* CASE2:  Is_an_antichain_in U P1 e -> Is_an_antichain_in U P2 e *)
       intro. destruct H1. destruct H1 as [H1a H1].
       unfold Is_an_antichain_in. split.
    +  split.
       -  destruct H. destruct H.
          apply Included_transitive with (e2:= (Carrier_of U P1)).
          assumption. assumption.
       -  assumption.
     + unfold Inside in H.
          destruct H as [Ha H]. rewrite H in H2.
          assumption.  } Qed.

 Lemma Antichain_not_changed1:  forall (P1 P2: FPO U)(e: Ensemble U),
           Inside  P1 P2 -> Included _ e (Carrier_of _ P1) ->
           Is_an_antichain_in  P2 e -> Is_an_antichain_in  P1 e .
 Proof. { apply Antichain_not_changed. } Qed.


 
 Lemma Antichain_not_changed2: forall (P1 P2: FPO U)(e: Ensemble U),
           Inside  P1 P2 -> Included _ e (Carrier_of _ P1) ->
           Is_an_antichain_in  P1 e ->  Is_an_antichain_in  P2 e .
 Proof.  apply Antichain_not_changed. Qed.

 Lemma Antichain_remains1:  forall (P1 P2: FPO U)(e: Ensemble U),
           Included_in  P2 P1 -> Included _ e (Carrier_of _ P1) ->
           Is_an_antichain_in  P2 e -> Is_an_antichain_in  P1 e.
 Proof.  { intros. destruct H1.
           destruct H1 as [H1a H1]. 
           unfold Is_an_antichain_in. split.
   
          { split.  - assumption. - assumption. }
          { unfold Included_in in H. destruct H as [Ha Hb].
            rewrite Hb. assumption. }   } Qed.

  Lemma Antichain_remains2:  forall (P1 P2: FPO U)(e: Ensemble U),
           Included_in  P2 P1 -> Included _ e (Carrier_of _ P1) ->
           Is_an_antichain_in  P1 e ->  Is_an_antichain_in  P2 e.
  Proof. { intros.  destruct H1. destruct H1 as [H1a H1].
          unfold Is_an_antichain_in. split.
          +  split.
          -  destruct H. 
             apply Included_transitive with (e2:= (Carrier_of U P1)).
             assumption. assumption.
          -  assumption.
             + unfold Included_in in H.
               destruct H as [Ha H]. rewrite H in H2.
               assumption.  } Qed.

  Lemma Largest_Antichain_remains:  forall (P1 P2: FPO U)(e: Ensemble U),
    Included_in P2 P1 -> Included _ e (Carrier_of _ P1) ->
    Is_largest_antichain_in  P2 e -> Is_largest_antichain_in  P1 e.
  Proof. {  intros P1 P2 la.  intros.
 (* We will prove it by contradiction. we assume that la is not a largest antichain in P1
  and therefore there is some chain la' larger than la and an antichain in P1. This must
  also be an antichain in P2. Hence la is also not the largest antichain of P2. This 
  contradicts the assumption H1 that la is largest antichain of P2. *)
  elim (EM (Is_largest_antichain_in  P1 la)).
  Focus 2.
- intro.
  absurd(Is_largest_antichain_in  P2 la).
  
    + assert(H3: ~ forall (la' : Ensemble U),
               forall (n n':nat),  Is_an_antichain_in  P1 la' ->
                                   cardinal _ la n -> cardinal _ la' n' -> n'<= n).
      { intro. absurd (Is_largest_antichain_in  P1 la).
       assumption.
       apply largest_antichain_cond.

       destruct H1. apply Antichain_remains1 with (P2:=P2).
       assumption. assumption. assumption. assumption. } 
     
      (* assertion H3 proved *)
      
     intro.
     destruct H4.
      
     assert(H3a: exists (la': Ensemble U), ~ forall (n n':nat),
         Is_an_antichain_in  P1 la' ->
        cardinal U la n -> cardinal U la' n' -> n' <= n).
        { apply Negation6. assumption. } 
     assert(H4a: exists e1: Ensemble U, ~ (forall n n1:nat, Is_an_antichain_in  P2 e1 ->
                                         cardinal U la n -> cardinal U e1 n1 -> n1 <= n ) ).
        { destruct H3a as [la' H3a]. exists la'.
          intro. elim H3a.
          intros n n1 H7. apply H6. generalize H7. apply Antichain_remains2.
          assumption. destruct H7. apply H7. } 
     absurd (forall (e1 : Ensemble U) (n n1 : nat),
       Is_an_antichain_in  P2 e1 ->
       cardinal U la n -> cardinal U e1 n1 -> n1 <= n).
       { apply Negation7. assumption. } { assumption. }

   + assumption.
- trivial.  } Qed.   
 


Lemma Largest_antichain_remains:
  forall (P1 P2: FPO U)(e: Ensemble U),
    Inside P1 P2 -> Included _ e (Carrier_of _ P1) ->
    Is_largest_antichain_in  P2 e -> Is_largest_antichain_in  P1 e.
Proof. {
  intros P1 P2 la.  intros.
  (* We will prove it by contradiction. we assume that la is not a largest antichain in P1
  and therefore there is some chain la' larger than la and an antichain in P1. This must
  also be an antichain in P2. Hence la is also not the largest antichain of P2. This 
  contradicts the assumption H1 that la is largest antichain of P2. *)
  elim (EM (Is_largest_antichain_in  P1 la)).
  Focus 2.
- intro.
  absurd(Is_largest_antichain_in  P2 la).
  
    + assert(H3: ~ forall (la' : Ensemble U),
               forall (n n':nat),  Is_an_antichain_in  P1 la' ->
                                   cardinal _ la n -> cardinal _ la' n' -> n'<= n).
      { intro. absurd (Is_largest_antichain_in  P1 la).
       assumption.
       apply largest_antichain_cond.

       destruct H1. apply Antichain_not_changed1 with (P2:=P2).
       assumption. assumption. assumption. assumption. }
     
      (* assertion H3 proved *)
      
     intro.
     destruct H4.
      
     assert(H3a: exists (la': Ensemble U), ~ forall (n n':nat),
         Is_an_antichain_in  P1 la' ->
        cardinal U la n -> cardinal U la' n' -> n' <= n).
        { apply Negation6. assumption. } 
     assert(H4a: exists e1: Ensemble U, ~ (forall n n1:nat, Is_an_antichain_in  P2 e1 ->
                                         cardinal U la n -> cardinal U e1 n1 -> n1 <= n ) ).
        { destruct H3a as [la' H3a]. exists la'.
          intro. elim H3a.
          intros n n1 H7. apply H6. generalize H7. apply Antichain_not_changed2.
          assumption. destruct H7. apply H7. }
     absurd (forall (e1 : Ensemble U) (n n1 : nat),
       Is_an_antichain_in  P2 e1 ->
       cardinal U la n -> cardinal U e1 n1 -> n1 <= n).
       { apply Negation7. assumption. } { assumption. }

   + assumption.
- trivial.  } Qed.

End Inside_Property.    

Hint Resolve Chain_remains1 Chain_remains2 Largest_Chain_remains : fpo_facts.
Hint Resolve Antichain_remains1 Antichain_remains2 Largest_Antichain_remains: fpo_facts.

(* ----------------------------- EXISTENCE OF LARGEST ELEMENTS-----------------------------  *)


Section Largest_members.

  Variable U: Type.


Hint Resolve Singleton_is_finite: sets_card.
Lemma MaxExists: forall e: Ensemble nat,
    Finite _ e -> Inhabited _ e -> (exists max: nat, In _ e max /\ (forall x: nat, In _ e x -> x<= max)).
Proof. { intros.
       
       assert (Order _ le).
       { Print Order. apply Definition_of_order.
         {  unfold Reflexive. auto with arith. }
         { unfold Transitive. apply le_trans. }
         {unfold Antisymmetric. auto with arith. } }
       Print PO.

       pose (P:= {|Carrier_of:= e ; Rel_of:= le ; PO_cond1:= H0 ; PO_cond2:= H1 |}).

       pose (FP:= {|PO_of := P; FPO_cond:= H |}).
       pose (C:= Carrier_of _ FP).
       pose (R:= Rel_of _ FP).

       assert (Totally_ordered _ FP C ).
       { Print Totally_ordered. apply Totally_ordered_definition.
         intros. simpl. omega.   }

       elim Largest_element_exists with (FP:=FP).
       intro max. intros.

       exists max. unfold Is_the_largest_element_in in H3. simpl in H3. tauto.
       simpl. apply H2.  } Qed.

Lemma MinExists:  forall e: Ensemble nat,
    Finite _ e -> Inhabited _ e -> (exists min: nat, In _ e min /\ (forall x: nat, In _ e x -> min <= x)).
Proof.  { intros.
       
       assert (Order _ le).
       { Print Order. apply Definition_of_order.
         {  unfold Reflexive. auto with arith. }
         { unfold Transitive. apply le_trans. }
         {unfold Antisymmetric. auto with arith. } }
       Print PO.

       pose (P:= {|Carrier_of:= e ; Rel_of:= le ; PO_cond1:= H0 ; PO_cond2:= H1 |}).

       pose (FP:= {|PO_of := P; FPO_cond:= H |}).
       pose (C:= Carrier_of _ FP).
       pose (R:= Rel_of _ FP).

       assert (Totally_ordered _ FP C ).
       { Print Totally_ordered. apply Totally_ordered_definition.
         intros. simpl. omega.  }

       elim Smallest_element_exists with (FP:=FP).
       intro min. intros.

       exists min. unfold Is_the_smallest_element_in in H3. simpl in H3. tauto.
       simpl. apply H2.  } Qed.  

    Definition numbers_lte (n: nat): Ensemble nat := fun (x:nat)=> x<=n.
    Check numbers_lte.

    Notation "[ n ]" := (numbers_lte n).

    Lemma Finite_n: forall n: nat, Finite _ [n]. 
    Proof. { intro. induction n.
           assert ( Included _ [0]  (Singleton _ 0)).
           { unfold Included. intros. unfold In in H.  unfold numbers_lte in H.
            Print Singleton. cut (x=0). intro. rewrite H0.
            auto with sets. auto with arith.  } 
           eapply Finite_downward_closed with (A:= (Singleton _ 0)).
           auto with sets_card. auto with sets_card. 
           assert ( Included _ [S n] (Add _ [n] (S n)) ).
           { unfold Included. intros. unfold In in H.  unfold numbers_lte in H.
             unfold Add.
             assert ( x< S n \/ x= S n). generalize H.
             SearchPattern (?x <=  ?n -> ?x < ?n \/ ?x =  ?n). apply le_lt_or_eq.
             elim H0.
             { intro. apply Union_introl. unfold In. unfold numbers_lte. generalize H1.
               auto with arith.  }
             { intro. apply Union_intror. rewrite H1. auto with sets. }
           }
           eapply Finite_downward_closed with (A:= (Add nat [n] (S n)) ).
           { eapply Union_is_finite with (A:= [n]). auto.
           intro. unfold In in H0. unfold numbers_lte in H0.
           absurd ( S n <= n). auto with arith.  auto. }
           { auto. }  } Qed.  

    Lemma MaxExists1:
      forall n:nat, forall e: Ensemble nat, Inhabited _ e ->
          Included _ e [ n ] -> (exists max:nat, In _ e max /\ (forall x: nat, In _ e x -> x<= max)).
    Proof. { intros n e.   intro T. intros.
           assert(H1: Finite _ e).
           { Check Finite_downward_closed.
             apply Finite_downward_closed with (A:= [n] ).  apply Finite_n. auto. }
           generalize T. generalize H1. apply MaxExists. } Qed.

    Set Implicit Arguments.



 Inductive Is_largest_set (U: Type) (E: Ensemble (Ensemble U)) (e: Ensemble U): Prop:=
  Larg_cond:  In _ E e ->
   (forall (e1 : Ensemble U)(n n1 : nat), (In _ E e1 /\ cardinal _ e1 n1 /\ cardinal _ e n) -> n1 <= n) ->
   Is_largest_set  E e.

 Inductive Is_smallest_set (U: Type) (E: Ensemble (Ensemble U)) (e: Ensemble U): Prop:=
  Small_cond:  In _ E e ->
   (forall (e1 : Ensemble U)(n n1 : nat), (In _ E e1 /\ cardinal _ e1 n1 /\ cardinal _ e n) -> n <= n1) ->
   Is_smallest_set  E e.

 Unset Implicit Arguments. 

 Lemma Largest_set_exists: forall U:Type, forall E: Ensemble (Ensemble U),
         Finite _ E -> Inhabited _ E ->
         (forall e: Ensemble U, In _ E e -> Finite _ e) ->
         exists e_max: Ensemble U, Is_largest_set E e_max.
 Proof. {
 (* Proof Idea: We consider the subset of Natural numbers which has the size
    of each set in E. We call it N. we can prove that N has a maximum number.
    hence the set corresponding to it will be the largest set.  *)
   clear U. intros. Check my_choice.
   assert ( exists f : Ensemble U -> nat, forall x : Ensemble U, In _ E x -> cardinal _ x (f x)).
   { apply my_choice. exists 0. trivial. intros. apply finite_cardinal. auto. }

   destruct H2 as [size H2].
   pose (N:= Im _ _ E size).

   assert (Finite _ N ).
   { apply finite_image. auto. }

   assert (exists max: nat, In _ N max /\ (forall x: nat, In _ N x -> x<= max)).
   { Print MaxExists. apply MaxExists. auto.
     destruct H0. eapply Inhabited_intro with (x:= size x).
     unfold N. eapply Im_def. auto. }

   destruct H4 as [n H4]. destruct H4.
   assert (exists e : Ensemble U, In _ E e /\ size e = n).
   { apply Im_inv . apply H4. } destruct H6 as [e_max H6]. destruct H6. 

   exists e_max.
   { apply Larg_cond.  tauto. intros. destruct H8. destruct H9.
     assert (n= n0).
     { cut (cardinal U e_max (size e_max) ).  rewrite H7. intro.
       eapply cardinal_unicity. exact H11.  auto. auto. }
     rewrite <- H11. apply H5. apply Im_intro with (x:=e1). auto.
     cut ( cardinal _ e1 (size e1)). intro. eapply cardinal_unicity. exact H9. auto.
     apply H2. auto.  }   } Qed.

 Lemma Smallest_set_exists:  forall U:Type, forall E: Ensemble (Ensemble U),
         Finite _ E -> Inhabited _ E ->
         (forall e: Ensemble U, In _ E e -> Finite _ e) ->
         exists e_min: Ensemble U, Is_smallest_set E e_min.
 Proof. {
 (* Proof Idea: We consider the subset of Natural numbers which has the size
    of each set in E. We call it N. we can prove that N has a minimum number.
    hence the set corresponding to it will be the smallest set.  *) 
   clear U. intros. Check my_choice.
   assert ( exists f : Ensemble U -> nat, forall x : Ensemble U, In _ E x -> cardinal _ x (f x)).
   { apply my_choice. exists 0. trivial. intros. apply finite_cardinal. auto. }

   destruct H2 as [size H2].
   pose (N:= Im _ _ E size).

   assert (Finite _ N ).
   { apply finite_image. auto. }

   assert (exists min: nat, In _ N min /\ (forall x: nat, In _ N x -> min <= x)).
   { Print  MinExists. apply MinExists. auto.
     destruct H0. eapply Inhabited_intro with (x:= size x).
     unfold N. eapply Im_def. auto. }

   destruct H4 as [n H4]. destruct H4.
   assert (exists e : Ensemble U, In _ E e /\ size e = n).
   { apply Im_inv . apply H4. } destruct H6 as [e_min H6]. destruct H6. 

   exists e_min.
   { apply Small_cond.  tauto. intros. destruct H8. destruct H9.
     assert (n= n0).
     { cut (cardinal U e_min (size e_min) ).  rewrite H7. intro.
       eapply cardinal_unicity. exact H11.  auto. auto. }
     rewrite <- H11. apply H5. apply Im_intro with (x:=e1). auto.
     cut ( cardinal _ e1 (size e1)). intro. eapply cardinal_unicity. exact H9. auto.
     apply H2. auto.  }   } Qed. 


Lemma exists_largest_antichain: forall (P: FPO U), exists (m: nat)(la: Ensemble U),
      (Is_largest_antichain_in P la) /\ (cardinal _ la m).
Proof. { intros.
         pose (C:= Carrier_of _ P).
         pose (E:= fun (e: Ensemble U)=> Is_an_antichain_in  P e).
       assert (H_Finite: Finite _ E).
       { assert (H: Included _ E (Power_set _ C) ).
         { unfold E. unfold Included.  unfold In.
           intros la H.  destruct H.  unfold C.
           apply Definition_of_Power_set. tauto. }
         apply Finite_downward_closed with (A:= Power_set U C).
         apply Power_set_finite. unfold C. apply FPO_cond. tauto. } 
       
       assert (All_Finite: forall e: Ensemble U, In _ E e -> Finite _ e).
       { intros la H.
         assert (H0: Included _ la C).
         { unfold E in H. unfold In in H. apply H. }
         apply Finite_downward_closed with (A:= C). apply FPO_cond.
         auto. }

       assert (Inhabited_E: Inhabited _ E).
       { elim Antichain_exists with (FP:=P). intro a. intro.
         eapply Inhabited_intro with (x:= a).
         unfold In. unfold E. auto.  }
       
       assert (H: exists e_max: Ensemble U, Is_largest_set E e_max).
       { apply Largest_set_exists.  auto. auto. auto. }

       destruct H as [e_max H]. destruct H.
       assert (H1: exists m: nat, cardinal _ e_max m).
       { apply finite_cardinal. auto. }
       destruct H1  as [m H1].
       exists m. exists e_max.
       split.
       { apply largest_antichain_cond. auto.  unfold E in H0. unfold In in H0.
         intros e1 n n1. intros.
         apply H0 with (e1:= e1). tauto. } 
       tauto. } Qed.


Lemma exists_largest_chain: forall (P: FPO U), exists (m: nat)(lc: Ensemble U),
      (Is_largest_chain_in P lc) /\ (cardinal _ lc m).
Proof. { intros.
         pose (C:= Carrier_of _ P).
         pose (E:= fun (e: Ensemble U)=> Is_a_chain_in P e).

       assert (H_Finite: Finite _ E).
       { assert (H: Included _ E (Power_set _ C) ).
         { unfold E. unfold Included.  unfold In.
           intros la H.  destruct H.  unfold C.
           apply Definition_of_Power_set. tauto. }
         apply Finite_downward_closed with (A:= Power_set U C).
         apply Power_set_finite. unfold C. apply FPO_cond. tauto. }
       
       assert (All_Finite: forall e: Ensemble U, In _ E e -> Finite _ e).
       { intros la H.
         assert (H0: Included _ la C).
         { unfold E in H. unfold In in H. apply H. }
         apply Finite_downward_closed with (A:= C). apply FPO_cond.
         auto. }

       assert (Inhabited_E: Inhabited _ E).
       { elim Chain_exists with (FP:=P). intro a. intro.
         eapply Inhabited_intro with (x:= a).
         unfold In. unfold E. auto.  }
       
       assert (H: exists e_max: Ensemble U, Is_largest_set E e_max).
       { apply Largest_set_exists.  auto. auto.  auto. }

       destruct H as [e_max H]. destruct H.
       assert (H1: exists m: nat, cardinal _ e_max m).
       { apply finite_cardinal. auto. }
       destruct H1  as [m H1].
       exists m. exists e_max.
       split.
       { apply largest_chain_cond. auto.  unfold E in H0. unfold In in H0.
         intros e1 n n1. intros.
         apply H0 with (e1:= e1). tauto. }
       tauto. } Qed. 



End Largest_members.


Section More_FPO.
   Variable U: Type.

   Ltac apply_equal:= (apply Extensionality_Ensembles; unfold Same_set; split).
   Set Implicit Arguments. 
  
   Inductive Is_a_smallest_chain_cover (P: FPO U) (scover: Ensemble (Ensemble U)): Prop:=
    smallest_cover_cond: (Is_a_chain_cover P scover) ->  
                        ( forall (cover: Ensemble (Ensemble U))(sn n: nat),
                           (Is_a_chain_cover P cover /\ cardinal _ scover sn /\
                           cardinal _ cover n) -> (sn <=n) ) ->
                        Is_a_smallest_chain_cover P scover.
   Lemma Chain_cover_included_in_PC: forall (P: FPO U) (cv: Ensemble (Ensemble U)),
       Is_a_chain_cover P cv -> Included _ cv (Power_set _ (Carrier_of _ P)).
   Proof. { intros. unfold Included. intros. Print Power_set.
          apply  Definition_of_Power_set. apply H. auto. } Qed. 

   
   Lemma Exists_smallest_chain_cover: forall (P: FPO U), exists cover: Ensemble (Ensemble U),
         Is_a_smallest_chain_cover P cover.
   Proof.  { intros.
         pose (C:= Carrier_of _ P).
         pose (E:= fun (e : Ensemble( Ensemble U)) => Is_a_chain_cover P e).
         pose (PC:= Power_set _ C). 
       assert (H_Finite: Finite _ E).
       { assert (H: Included _ E (Power_set _ PC) ).
         { unfold E. unfold Included.  unfold In.
           intros cv H.  (* destruct H. *)  unfold PC.
           apply Definition_of_Power_set. unfold C.  apply Chain_cover_included_in_PC. tauto. } 
         apply Finite_downward_closed with (A:= Power_set _ PC).
         apply Power_set_finite.  unfold PC. apply Power_set_finite.
         unfold C. apply FPO_cond. tauto. } 
       
       assert (All_Finite: forall e: Ensemble (Ensemble U), In _ E e -> Finite _ e).
       { intros cv H.
         assert (H0: Included _ cv PC).
         { unfold E in H. unfold In in H. unfold PC. unfold C.
           apply Chain_cover_included_in_PC. apply H. } 
         apply Finite_downward_closed with (A:= PC). unfold PC.
         apply Power_set_finite. apply FPO_cond. auto. }

       assert (Inhabited_E: Inhabited _ E).
       { elim Chain_cover_exists with (FP:=P). intro cv. intro.
         eapply Inhabited_intro with (x:= cv).
         unfold In. unfold E. auto.  }
       
       assert (H: exists cv_min: Ensemble (Ensemble U), Is_smallest_set E cv_min).
       { apply Smallest_set_exists.  auto. auto.  auto. }

       destruct H as [cv_min H]. destruct H.
       assert (H1: exists m: nat, cardinal _ cv_min m).
       { apply finite_cardinal. auto. }
       destruct H1  as [m H1].
       exists cv_min. apply smallest_cover_cond.
       { unfold In in H. unfold E in H. auto. }
       { intros e1 n n1. intros. apply H0 with (e1:=e1) (n1:= n1). tauto. }  } Qed.

    Lemma Union_over_cv_is_C: forall (P: FPO U) (cv: Ensemble (Ensemble U)),
       Is_a_chain_cover P cv -> ( (Carrier_of _ P) = (Union_over cv)).
    Proof. { intros. apply_equal.
           { unfold Included. intros. unfold In. unfold Union_over. apply H. auto. }
           { unfold Included. intros.  unfold In in H0. unfold Union_over in H0.
             destruct H. destruct H0 as [e H0].
             assert (Is_a_chain_in P e). apply H. tauto. apply H2. tauto.  } } Qed.

    
   Lemma Inhabited_chain_cover: forall (P: FPO U)(cv: Ensemble (Ensemble U)),
       Is_a_chain_cover P cv -> Inhabited _ cv.
   Proof. { intros. elim (classic (Inhabited _ cv)). tauto. 
          { intro.
            assert (cv = Empty_set _ ). eapply Not_Inh_Empty. auto. 
            absurd (Inhabited _ (Carrier_of _ P)).
            replace (Carrier_of _ P) with (Union_over cv).
            replace (Union_over cv) with (Empty_set U ). intro. inversion H2.
            inversion H3.
            rewrite H1. symmetry. apply Union_over_empty. symmetry.
            apply Union_over_cv_is_C. auto. Print PO. apply PO_cond1.  }  } Qed. 

   
   Lemma exists_disjoint_cover: forall (P: FPO U) (m:nat),
     (exists cv: Ensemble (Ensemble U), Is_a_smallest_chain_cover P cv /\ cardinal _ cv m )->
    (exists cv': Ensemble (Ensemble U), Is_a_disjoint_cover P cv' /\ cardinal _ cv' m).
   Proof. {  intros P0 m. generalize P0 as P. clear P0.
           induction m.
           (* Base case when cv is empty . It is not possible. *)
           { intros. destruct H as [cv H]. destruct H.
             assert (0>0). eapply inh_card_gt_O with (X:=cv).
             eapply Inhabited_chain_cover. apply H. auto. inversion H1. } 
           
           (* Induction Step *) 
           intros. destruct H as [cv H].   destruct H.
           assert (H1: Is_a_chain_cover P cv). apply H.
           apply cardinal_invert with (p:= (S m)) in H0  as H2. 
          
           destruct H2 as [cv0 H2]. destruct H2 as [c H2].
           assert (H_cv:  cv = Add (Ensemble U) cv0 c ). tauto.
           assert (T0: In _ cv c).
           { rewrite H_cv.  auto with sets. } 
           assert (T1: Is_a_chain_in P c ).
           { apply H1. auto. }  
           assert (T2: Included _ c (Carrier_of _ P)).
           { apply T1. } 
          
           destruct H2. destruct H3. 
           pose (C:= Carrier_of _ P).
           assert (H5: C = Union_over cv).
           { unfold C. apply Union_over_cv_is_C. auto. }
           pose (C0:= Union_over cv0).
           assert (H6: C = Union _ C0 c).
           { rewrite H5. unfold C0. rewrite H2. eapply Union_over_P1. } 

           (* We break the proof in two cases *)
           elim (classic (cv0= Empty_set _)).
           (* CASE1: when C0 is empty. In this case chain cover cv has only one chain 
                     and hence it is minimal as well as disjoint *)
           { intro.
           
           assert (H8: cv= Singleton _ c).
           { rewrite H2. rewrite H7. auto with sets. }
           exists cv. split.
           { unfold Is_a_disjoint_cover.  split. auto.
             intros.  rewrite H8 in H9. destruct H9. destruct H9;destruct H10.
             left. reflexivity. }
           { auto. } } 
           
           (* CASE2: when C0 is not empty. Then cv0 is the smallest chain cover. 
                    Then it must have a disjoint chain cover of same size as cv0 by IHn. 
                     we consider the chain c':= Setminus c C0. then Union {c'} cv0' will be the 
                     disjoint chain cover for the whole poset. *)
           { intro. Print PO.
             pose (R:= Rel_of _ P).
             assert (Inh_cv0: Inhabited _ cv0).
             { apply Not_Empty_Inh. auto. }
             destruct Inh_cv0 as [e0 Inh_cv0].
             
             assert (H8: Inhabited _ C0).
             { assert (T4: In _ cv e0).
               { rewrite H2. unfold Add. apply Union_introl. auto. }
               assert (T5: Inhabited _ e0).
               { cut (Is_a_chain_in P e0 ).  intro. apply H8. apply H1. auto. }
               destruct T5 as [x0 T5].
               apply Inhabited_intro with (x:=x0). unfold C0.   unfold In.
               unfold Union_over. exists e0;tauto. } 
             
             pose (PO_P0:= {| Carrier_of := C0; Rel_of :=R; PO_cond1 := H8;
                              PO_cond2 := PO_cond2 _ P |}). Print FPO.
             
             assert (H9:Finite _ C0).
             { cut (Included _ C0 C). apply Finite_downward_closed.  apply FPO_cond.
               rewrite H6. auto with sets. } 
             pose (P0:= {| PO_of:= PO_P0; FPO_cond:= H9 |} ).

             assert (Fact: Included_in _ P P0).
             { unfold Included_in. split.
               simpl. replace (Carrier_of U P) with C.  rewrite H6.  auto with sets.
               unfold C. reflexivity. simpl. unfold R. reflexivity. }

             assert ( H10: Is_a_smallest_chain_cover P0 cv0).
             (* otherwise cv cannot be Smallest Chain Cover of P *)
             { Print Is_a_smallest_chain_cover.
               assert (H11: Is_a_chain_cover P0 cv0). 
               { apply cover_cond.
                 
                 { intros. 
                   assert (T3: In _ cv e).
                   { rewrite H_cv. unfold In. unfold Add. apply Union_introl. auto. }
                   assert (T4: Is_a_chain_in P e).
                   { destruct H. destruct H. apply H. auto. }
                   apply Chain_remains2 with (P2:= P).
                   auto.
                   { simpl. unfold C0. apply Union_over1. auto. }
                   auto. }
                 { simpl. unfold C0. intros. destruct H10. exists x0; tauto. } }  
                
             assert (H12: (forall (cover : Ensemble (Ensemble U)) (sn n : nat),
                           Is_a_chain_cover P0 cover /\
                           cardinal (Ensemble U) cv0 sn /\ cardinal (Ensemble U) cover n ->
                           sn <= n)).
               { intros.
                 assert (sn= m).
                 { eapply cardinal_unicity with (X:= cv0);tauto. }
                 rewrite H12 in H10. rewrite H12.
                 elim (classic ( m<= n)).
                 { tauto. }
                 { intro.
                   assert ( H14: ~ S m <= S n).
                   { intro. apply H13. auto with arith. }
                   destruct H10. destruct H15.
                   destruct H.
                   elim (classic (In _ cover c)).
                   { intro.
                     assert (H19: Is_a_chain_cover P cover).
                     { apply cover_cond.
                       { intros.
                         assert (H20: Is_a_chain_in P0 e).
                         { apply H10. auto. }
                         unfold Is_a_chain_in. apply Chain_remains1 with (P1:= P0).
                         auto.  auto. }
                       { replace (Carrier_of U P) with C.  intros.
                         rewrite H6 in H19. destruct H19. destruct H10.
                         apply H20. simpl. auto.
                         exists c. tauto. unfold C. reflexivity.  }  } 
                     assert (H20: S m <= n).
                     { eapply H17 with (cover:= cover). tauto.  }
                       auto with arith.   } 
                   { intro. pose (cover' := Add _ cover c).
                     assert (H19: cardinal _ cover' (S n)).
                     { apply card_add. auto. auto. }
                     assert (H20: Is_a_chain_cover P cover').
                     { apply cover_cond.
                       { intros. unfold cover' in H20. destruct H20.
                         { assert (Is_a_chain_in P0 x). apply H10. auto.
                         apply Chain_remains1 with (P1:= P0).
                         auto. auto. }
                         { destruct H20. auto. }  }
                       { replace (Carrier_of U P) with C.  intros. rewrite H6 in H20.
                         destruct H20. destruct H10.
                         assert ( exists e : Ensemble U, In (Ensemble U) cover e /\ In U e x).
                         { apply H21. simpl. auto. } destruct H22.
                         exists x0. split. unfold cover'. unfold Add. apply Union_introl.
                         apply H22. apply H22.  exists c. unfold cover'.
                         unfold Add. split. apply Union_intror. auto with sets. tauto.
                         unfold C. reflexivity.  }  } 
                     assert (H21: S m <= S n).
                     { eapply H17 with (cover:= cover'). tauto. }
                     contradiction.  }    }   } 
               
                 apply smallest_cover_cond. auto. auto. 
             } 

             assert ( H11: exists cv0' : Ensemble (Ensemble U), Is_a_disjoint_cover P0 cv0' /\
                                                      cardinal (Ensemble U) cv0' m).
             { apply IHm. exists cv0. tauto. }

             destruct H11 as [cv0' H11]. destruct H11. 

             assert (H13: C0= Union_over cv0').
             { replace C0 with (Carrier_of _ P0). eapply Union_over_cv_is_C. apply H11.
               simpl. reflexivity. }
             (* Lemma: Union_over_cv_is_C *)

             pose (c' := Setminus _ c C0).
             assert (Fact1:  c = Union _ c' (Intersection _ c C0) ).
             { apply_equal.
               { unfold c'. unfold Included.  intros.
                 elim (classic (In _ C0 x)).
                 { intro. apply Union_intror. auto with sets. }
                 { intro. apply Union_introl. auto with sets. }  }
               { unfold Included. intros. destruct H14. apply H14.
                 destruct H14. apply H14. } } 
             assert (F0: Included _ c' c).
             { unfold c'. apply Included_setminus. } 
             assert (H14:  ~ In (Ensemble U) cv0' c'). 
             { intro.
               assert (H15: Included _ c' C0). (* since c' belongs to cv0' due to H14. *)
               { rewrite H13. apply Union_over1. auto. }
               assert (H16: Inhabited _ c'). (* since it is a chain in cv0' *)
               { cut (Is_a_chain_in P0 c').  intro. apply H16. apply H11. auto. }
               destruct H16 as [x' H16].
               absurd (Disjoint _ c' C0).
               { intro. destruct H17.
                 assert ( In _ C0 x'). apply H15. auto. 
                 assert (In U (Intersection U c' C0) x'). auto with sets.
                 absurd (In U (Intersection U c' C0) x'). apply H17. tauto.  }
               { unfold c'. apply Disj_Setminus. }  }  
              
             assert (H15: forall x: Ensemble U, In _ cv0' x -> Disjoint _ x c').
             { intro e. intro.
               assert ( Included _ e C0).
               { rewrite H13.  apply Union_over1. auto. } 
               apply Disj_comm. eapply Disj_set_inc_disj with (B:= C0).
               unfold c'. apply Disj_Setminus. auto. } 

             assert (H16: Inhabited _ c').
             (* otherwise cv0 will be smallest chain cover of P *)
             {  elim (classic (Inhabited _ c')).
                { tauto. }
                { intro.
                  assert (H17: Included _ c C0).
                  {  rewrite Fact1. unfold Included.
                     intros. destruct H17.
                     { absurd (Inhabited U c'). auto. eapply Inhabited_intro. apply H17. }
                     { Print Intersection. destruct H17. auto.  }  } 
                  assert (H18: Is_a_chain_cover P cv0).
                  { apply cover_cond.
                    { intros. apply Chain_remains1 with (P1:= P0). auto.  destruct H10.
                      apply H10. auto. }
                    { replace (Carrier_of U P) with C. replace C with C0. unfold C0.
                      intros. unfold In in H18. unfold Union_over in H18. apply H18.
                      rewrite H6. symmetry. apply Union_absorbs. auto. unfold C.
                      reflexivity.  }  } 
                  assert (H19: S m <= m).
                  { destruct H. apply H19 with (cover:= cv0) . tauto. }
                  absurd(S m <= m). auto with arith. auto. } }  
                  

             

             pose (cv' := Add _ cv0' c' ).
             destruct H10 as [F1 H10]. destruct F1 as [F1 F2].
             destruct H11 as [F3 H11]. destruct F3 as [F3 F4].

             exists cv'. split. 
             { unfold Is_a_disjoint_cover.  split.
               { apply cover_cond.
                 { intros. unfold cv' in H17.  destruct H17.
                  { assert (H18: Is_a_chain_in P0 x).
                  { apply F3.  auto. }
                  unfold Is_a_chain_in in H18.
                  assert (H19: Is_a_chain_in P x ). 
                  { unfold Is_a_chain_in.
                  split.
                  { split.
                    { cut (Included _ (Carrier_of U P0) (Carrier_of U P)).
                  apply Inclusion_is_transitive.  tauto.  simpl.
                  cut (Included U C0 C). unfold C. tauto. rewrite H6. auto with sets. } 
                    { tauto. }  }
                  { simpl in H18. unfold R in H18. tauto. } }
                  tauto. }
                  { destruct H17.  cut (Is_a_chain_in P c).
                    { intro.
                    unfold Is_a_chain_in. split.   split.
                    cut (Included _ c (Carrier_of U P)). apply Inclusion_is_transitive. auto.
                    apply H17. auto. intros.
                    assert (H19: Included _ (Couple _ x y) c).
                    generalize F0. apply Inclusion_is_transitive. auto. apply H17. auto. }
                    auto. } }
                 { intros. replace (Carrier_of U P) with C in H17.
                   { assert (H18: C= Union _ C0 c').
                     { rewrite H6. unfold c'. apply Union_setminus.  }
                     rewrite H18 in H17. destruct H17.
                     { unfold cv'.
                       assert (H19:  exists e : Ensemble U, In (Ensemble U) cv0' e /\ In U e x).
                       apply F4. apply H17. destruct H19 as [e H19]. exists e.
                       split. unfold Add. apply Union_introl; tauto. tauto.  }
                     { unfold cv'.  exists c'.  split. auto with sets. auto. } }  
                   { unfold C. reflexivity. }   }   } 
               
               { intros.  unfold cv' in H16. destruct H17.
                 destruct H17; destruct H18.
                 apply H11;tauto.
                 destruct H18.  right. auto.
                 destruct H17. right. cut (Disjoint _ x0 c').
                 { intro.  destruct H17. Print Disjoint. apply  Disjoint_intro.
                  cut (Intersection _ x0 c' = Intersection _ c' x0). intro.
                  rewrite <- H19. apply H17. apply Intersection_commutative. }
                 apply H15. auto. left. destruct H17; destruct H18. reflexivity. } } 
             unfold cv'. eapply card_add. auto. auto.     }            }   Qed. 






    
  End More_FPO.
  
 