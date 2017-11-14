(* This File contains some trivial results on sets and natural numbers. ----------------*
  
   Note that this file uses the Classical and Classicalchoice modules of the Standard Library 

   New Definitions:
   1. Union_over (S: Ensemble (Ensemble U)): Let S be a collection of sets whose elements 
                                             are of type U. Then (Union_over S) represents the 
                                             Union of all the sets in S. 

   Description of some New  Results:
             1. We prove a Theorem called my_choice to extract a function from a given relation.
                Proof of this theorem uses Choice axiom from the Classicalchoice module. 
             2. We also prove a theorem strong_induction which is actually  the principle of stro                ng induction on natural numbers. 
             3. Some elementary results on natural number and sets that appear in this file might                already be present in other modules of Standard Library.  They are listed here 
                and renamed only because they are used more often in the proofs of other 
                important results.
             4. Lemma Disjoint_card: It claims that size of the set A U B equals 
                |A|+|B| whenever A and B are mutually disjoint.
             5. Lemma Power_set_finite: It claims that Powerset of a finite set is finite.
             6. Lemma Finite_Union_of_Finite_Sets: It says that (Union_over S) is finite if 
                i) S is finite and ii) every element of S is also finite.       *)


Require Export Ensembles.
Require Export Relations_1.
Require Export Finite_sets.
Require Export Constructive_sets.
Require Export Powerset.
Require Export Powerset_facts.
Require Export Powerset_Classical_facts.
Require Export Gt.
Require Export Lt.
Require Export Le.
Require Export Finite_sets_facts.
Require Export Image.
Require Export Classical.
Require Export Arith.
Require Export ClassicalChoice.

Section BasicFacts.

 


Definition Union_over {U:Type} (S: Ensemble (Ensemble U)): Ensemble U :=
  fun (x:U)=>  exists s: Ensemble U, In _ S s /\ In _ s x .


Theorem strong_induction: forall P : nat -> Prop,
                    (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
                    forall n : nat, P n.
Proof.    {
  intros P Strong_IH n. pose (Q:= fun (n: nat)=> forall k:nat, k<= n -> P k). 
  assert (H: Q n).
  { induction n.
    { unfold Q. intros. apply Strong_IH. intros. cut (S k0 <= 0).  intro. inversion H1.
      unfold lt in H0. generalize H. generalize H0. apply le_trans. } 
    { unfold Q in IHn. unfold Q. intros k H0.
      assert (H1: k < (S n) \/ k = (S n) ).  apply le_lt_or_eq.  auto.
      elim H1. unfold lt. intro. apply IHn. auto with arith.
      intro. rewrite H. apply Strong_IH. intros. apply IHn. unfold lt in H2.
      generalize H2. auto with arith. }   }
  unfold Q in H. apply H. auto with arith.   }   Qed.

Check strong_induction.


Lemma  maps_to_same: forall (U V: Type) (x y: U) (f: U-> V),
                             f x = f y ->  exists c:V, f x = c /\ f y = c.
  Proof. {
    intros A B x y f H. exists (f x). split. reflexivity. symmetry. assumption. }
  Qed.

  Check choice.

  (* The following theorem claims that we can get a function from U to V which maps 
     every element x of A to an element f(x)  in B such that R x f(x) .  Provided
     we are supplied with a relation R which relates every element in A to some element
     in B : One extra condition we need is B should be non empty *)

Theorem S_choice : forall (U V : Type) (R : U->V->Prop) (A: Ensemble U) (B: Ensemble V),
   (Inhabited _ B) -> (forall x : U, In _ A x ->  (exists y : V, In _ B y /\  R x y) )  ->
   exists f : U->V, (forall x : U, In _ A x -> ( R x (f x) /\ In _ B (f x))) .

Proof.  { intros.
       
       destruct H as [y0 F1].
       pose (R1(x: U) (y:V) := R x y /\ ( In _ A x -> In _ B y) ).
       pose (R' (x:U)(y:V):= R1 x y \/ ~ In _ A x ).
       Check choice.
       assert (F2: exists f : U -> V, forall x : U, R' x (f x)).
       {  apply choice. unfold R'. intro x.
          elim (classic (In _ A x)). {
          intros.
          assert (H2: exists y : V, In V B y /\ R x y).
          { auto. } destruct H2 as [y H2].  exists y.
          left. unfold R1. tauto.  }
          { intros. exists y0.  tauto. } }
       destruct F2 as [f F2].
       exists f.
       intros x F3. unfold R' in F2.
       assert(F4: R1 x (f x) \/ ~ In U A x).
       { auto.  }
       elim F4.
       { intro. unfold R1 in H.
         tauto.  }
       { intro. contradiction. }   }    Qed.

Theorem my_choice:  forall (U V : Type) (R : U->V->Prop) (A: Ensemble U),
   (exists y0:V, True )-> (forall x : U, In _ A x ->  (exists y : V, R x y) )  ->
   exists f : U->V, (forall x : U, In _ A x ->  R x (f x) ) .
  Proof.   { intros U V R A.  intros. 
       
       destruct H as [y0 F1]. 
       pose (R1(x: U) (y:V) := R x y  ).
       pose (R' (x:U)(y:V):= R1 x y \/ ~ In _ A x ).
       Check choice.
       assert (F2: exists f : U -> V, forall x : U, R' x (f x)).
       {  apply choice. unfold R'. intro x.
          elim (classic (In _ A x)). {
          intros.
          assert (H2: exists y : V,  R x y).
          { auto. } destruct H2 as [y H2].  exists y.
          left. unfold R1. tauto.  }
          { intros. exists y0.  tauto. } }
       destruct F2 as [f F2].
       exists f.
       intros x F3. unfold R' in F2.
       assert(F4: R1 x (f x) \/ ~ In U A x).
       { auto.  }
       elim F4.
       { intro. unfold R1 in H.
         tauto.  }
       { intro. contradiction. }   }    Qed. 

  
      
       
  (* -----------------  NATURAL NUMBER FACTS -------------------------------------------- *)


Open Scope nat_scope.
 
 Lemma Middle_num: forall (m n: nat), (m <= n /\ n <  (S m)) ->  n =  m.
 Proof. {  unfold lt. intros.
         assert (H1: n<= m). { destruct H. generalize H0. auto with arith. }
         generalize H1. destruct H. generalize H. auto with arith. }
 Qed. 

 
 Lemma nat_P0: forall n:nat, S n = n+1.
   Proof. intros. rewrite plus_comm. unfold plus. reflexivity. Qed.  

 Lemma nat_P1: forall n m: nat, n<=m <-> ~(n>m).
  Proof. {  intros.
         unfold iff.
         split. { auto with arith. }
                { unfold gt. unfold lt.
                  apply or_to_imply.
                  assert (H1: S m <= n \/ n <= m).
                  { induction n.  right. auto with arith.
                    elim IHn.
                    {intro. left.  auto. }
                    { intro.  destruct H. left. auto. right. auto with arith. } }
                  elim H1.
                  {intro. left. intro. contradiction. }
                  {intro. right.   auto. }  }      }  Qed.


   
 Lemma nat_P2:  forall n: nat, n>0 -> S (pred n) = n .
  Proof. { intros. destruct n.  inversion H.  auto with arith. } Qed.
 

 Lemma nat_P3: forall n: nat, pred n = n-1.
  Proof. apply pred_of_minus. Qed. 
  
 Lemma Not_equal_means_lt_or_gt: forall (m n :nat), m<>n-> (m<n)\/ (m>n).
 Proof.  apply nat_total_order. Qed. 

 Lemma nat_P4: forall n m p: nat, n<=m -> (n + p <= m + p).
 Proof. intros. auto with arith.  Qed.

 Lemma nat_P5: forall n m:nat, ~(n<= m) <-> n>m.
 Proof. { intros.  unfold iff. split.
        { unfold gt. unfold lt.
          apply or_to_imply.
          assert (H1: S m <= n \/ n <= m).
           { induction n.  right. auto with arith.
                    elim IHn.
                    {intro. left.  auto. }
                    { intro.  destruct H. left. auto. right. auto with arith. } }
           elim H1.
           { intro. right. auto. }
           { intro. left. intro. contradiction. }   }
        { auto with arith. } } Qed. 
 
 Lemma nat_P6: forall n m: nat, n<=m \/ m<= n.
 Proof. { intros.  assert (n<=m \/ ~n <= m). apply classic.
         elim H.
         { tauto. }
         { intro. right.
           assert (n>m).
           { apply nat_P5. auto. }
           unfold gt in H1. unfold lt in H1. eapply le_trans with (m:= S m).
           auto with arith. auto. } } Qed. 




  (* ------------------------------------------------------------------------------------ *)
  (* --------------NEGATION FACTS ON PROPOSITION AND PREDICATES-------------------------- *)
  
 Lemma Negation1: forall (A B: Prop), ~(A \/ B) -> ( ~A /\ ~B).
 Proof.  apply not_or_and.  Qed.
 
 Lemma Negation2: forall (A B: Prop), ~(A /\ B) -> (~A \/ ~B).
 Proof. apply not_and_or.  Qed.

 
 Lemma Negation4: forall (P Q: Prop), ~ (P -> Q)-> (P /\ ~Q).
 Proof. apply imply_to_and. Qed. 

 Lemma Negation5: forall (P Q R: Prop), ~(P-> Q-> R) -> (P /\ Q /\ ~R).
 Proof. { intros. assert(H1: P/\~(Q-> R)). apply Negation4. assumption.
         destruct H1.
         assert (H2: Q/\ ~R). apply Negation4. assumption.
         split. assumption. assumption. }
 Qed.

 Lemma Negation3: forall (U: Type)(P Q : U-> Prop),
                    ~(forall x:U, P x -> Q x)-> (exists x:U, P x /\ ~ Q x).
 Proof. { intros. assert (H1: exists x:U, ~( P x -> Q x)).
          apply not_all_ex_not. assumption.
        destruct H1 as [a H1]. exists a.
        generalize H1. apply imply_to_and. }   Qed.


 Ltac apply_negation:=
   match goal with
         | _:_ |-  ~ (forall n : ?U, ~ ?P n) -> exists n : ?U, ?P n => (apply not_all_not_ex)
         | _:_ |-  ~ (forall n : ?U, ?P n) -> exists n : ?U, ~ ?P n=> (apply not_all_ex_not)
         | _:_ |-  ~ (exists n : ?U, ?P n) -> forall n: ?U, ~ ?P n => (apply not_ex_all_not)
         |_:_ |-  ~ (exists n : ?U, ~ ?P n) -> forall n: ?U, ?P n => (apply not_ex_not_all)
         |_:_ |-  (exists n : ?U, ~ ?P n) -> ~ (forall n: ?U, ?P n) => (apply ex_not_not_all) 
         |_:_ |-   (forall n: ?U, ~ ?P n) -> ~ (exists n : ?U, ?P n) => (apply all_not_not_ex)
   end.
 
 
 Lemma Negation6: forall (U: Type) (P:U->Prop ), ~(forall x:U, P x)-> (exists x:U, ~ P x).
 Proof. intro. intro. apply_negation.  Qed.

 Lemma Negation7: forall (U:Type) (P:U-> Prop), (exists x:U, ~ P x)-> ~(forall x: U, P x).
 Proof. intros. generalize H. apply_negation.  Qed.

 Lemma Negation8: forall (U:Type) (P:U-> Prop), ~ (exists x:U,  P x)-> (forall x: U, ~ P x).
 Proof. intro.  intro. apply_negation. Qed. 

 Lemma Negation9:  forall (U:Type) (P:U-> Prop), (forall x: U, ~ P x) -> ~ (exists x:U,  P x).

 Proof. intro. intro. apply_negation. Qed. 
 
 

(* --------------------------------------------------------------------------------------- *)
(* ------------------ SET FACTS ---------------------------------------------------------- *) 




Lemma strict_included_card_less:
     forall (U: Type)(e1 e2: Ensemble U)(m n:nat),
       cardinal _ e1 m -> cardinal _ e2 n -> Strict_Included _ e1 e2 -> m < n.
 Proof. {
   intro U1. intros.
   apply incl_st_card_lt with (U:=U1)(X:=e1)(Y:=e2).
   assumption. assumption. assumption. }  Qed.

Lemma Included_transitive: forall(U:Type)(e1 e2 e3: Ensemble U),
                             Included _ e1 e2 -> Included _ e2 e3 -> Included _ e1 e3.
Proof. { intros. unfold Included. intro x.
       assert (H1: In _ e1 x -> In _ e2 x).
       apply H. assert (H2: In _ e2 x -> In _ e3 x).
       apply H0. intro. apply H2. apply H1. assumption. } Qed.

Lemma Not_equal_sets: forall(U:Type) (A B: Ensemble U),
        A<>B -> (exists a:U, In _ A a /\ ~ In _ B a )\/ (exists b:U, In _ B b /\ ~ In _ A b).
  Proof. { intros. assert (Ha: ~ Same_set _ A B). intro. elim H.
         apply Extensionality_Ensembles. assumption.

         unfold Same_set in Ha. assert (Hb: ~ Included U A B \/  ~ Included U B A).
         apply not_and_or. assumption.
         elim Hb.
         intro. left. unfold Included in H0. generalize H0.
         apply Negation3.
         intro. right. unfold Included in H0. generalize H0.
         apply Negation3. }  Qed.

Lemma Sets_not_equal: forall(U: Type) (A B: Ensemble U),
        ( (exists x:U, In _ A x /\ ~ In _ B x) \/(exists x:U, ~In _ A x /\ In _ B x)) -> A<>B.
Proof.  { intros. elim H.
          { intro;  intro; destruct H0 as [x H0]; rewrite H1 in H0; destruct H0; contradiction. }
          { intro;  intro; destruct H0 as [x H0]; rewrite H1 in H0; destruct H0; contradiction. }
           } Qed. 




Lemma Singleton_card: forall (U:Type) (x: U), cardinal _ (Singleton _ x) 1.
Proof. { intros. 
       assert (H: Singleton U x = Add _ (Empty_set U) x).
       auto with sets. rewrite H. eapply card_add. auto with sets. auto with sets. }  Qed. 

Lemma Couple_card_1: forall (U:Type) (x y: U), x=y -> cardinal _ (Couple _ x y) 1.
Proof. { intros. rewrite <- H.
       assert ( Union U (Singleton U x) (Singleton U x) = Couple U x x).
       apply Couple_as_union.
       assert ( Union U (Singleton U x) (Singleton U x) = Singleton U x).
       apply Union_idempotent. rewrite <- H0. rewrite H1. apply Singleton_card. } Qed. 

Lemma Couple_card_2: forall (U:Type) (x y: U), x<>y -> cardinal _ (Couple _ x y) 2.
Proof. { intros.
       assert (H1: Couple U x y = Add _ (Singleton _ x) y).
       unfold Add. symmetry.   apply Couple_as_union. rewrite H1.
       eapply card_add. apply Singleton_card. intro.  destruct H0.
       apply H. reflexivity.  } Qed.


Lemma Couple_comm: forall (U: Type) (x y: U), Couple _ x y = Couple _ y x.
Proof. { intros.
       assert (H: Union U (Singleton U x) (Singleton U y) = Couple U x y).
       apply Couple_as_union.
       assert (H1: Union U (Singleton U y) (Singleton U x) = Couple U y x ).
       apply Couple_as_union. rewrite <- H. rewrite <- H1. apply Union_commutative. } Qed. 

Lemma Disjoint_card: forall (U: Type) (A B: Ensemble U)(m n: nat),
    (Disjoint _ A B)/\ (cardinal _ A m) /\ (cardinal _ B n) -> (cardinal _ (Union _ A B) (m+n) ).
Proof. { intro. intros A0 B0 m.  generalize B0 as B. generalize A0 as A.
       induction m.
       (* trivial case here A is empty set. *)
       { intros. destruct H. destruct H0.
        assert (H2: A = Empty_set U).
        { Print cardinal_elim. eapply cardinal_elim with (X:= A) (p:= 0).  auto. }
        rewrite H2. simpl.
        assert (Union U (Empty_set U) B = B). auto with sets. rewrite H3. auto. }
       (* Induction Step *)
       { intros. destruct H. destruct H0.
         apply cardinal_invert in H0. clear A0 B0. destruct H0 as [A0 H0].
         destruct H0 as [a H0].
         assert (H2: ~ In _ B a).
         { destruct H. intro.
           assert ( In _ (Intersection _ A B) a).
           { Print Intersection. apply Intersection_intro. destruct H0.  rewrite H0.
             auto with sets. auto. }
           absurd (In _ (Intersection _ A B) a). auto. auto.  }

         assert (H3: ~ In _ (Union _ A0 B) a).
         { intro. destruct H0. destruct H4.  destruct H3; contradiction. }

         assert (H4: (Union _ A B) = Add _ ( Union _ A0 B) a).
         { destruct H0. rewrite H0. unfold Add.
           cut (Union U (Union U A0 (Singleton U a)) B = Union U B (Union U A0 (Singleton U a))).
           { intro. rewrite H5.
           cut (Union U B (Union U A0 (Singleton U a))= Union _ (Union _ B A0) (Singleton _ a)).
           { intros. rewrite H6. cut (Union _ B A0 = Union _ A0 B).
             { intro. rewrite H7. reflexivity.  }
             auto with sets. } auto with sets.  } auto with sets. }

         assert (H5: cardinal _ (Union _ A B) (S (m +n)) ).
         { rewrite H4. apply card_add. auto.  apply IHm.
           split.
           { Print Disjoint.  apply Disjoint_intro. intros. intro.
             destruct H.
             absurd ( In _ (Intersection _ A B) x ).
             { apply H. }
             { destruct H0. rewrite H0.   apply Intersection_intro.  unfold Add.
               apply Union_introl. destruct H5; auto. destruct H5; auto. }  } 
           tauto. auto.  }

         apply H5.  }    }  Qed.


  Lemma Singleton_P1:  forall (U:Type) (x y: U), In _ (Singleton _ x) y -> x=y.
  Proof.  intros. auto with sets. Qed.

  Lemma Set_Add_Sub: forall (U:Type) (X: Ensemble U)(x: U), In _ X x -> X = Add _ (Subtract _ X x) x.
  Proof. { intros. auto with sets. } Qed.

  Lemma Set_Sub_card: forall (U:Type) (X: Ensemble U)(x: U)(n:nat), In _ X x -> cardinal _ X (S n) ->
                                                             cardinal _ (Subtract _ X x) n.
  Proof. { intros.
          assert (H1: X = Add _ (Subtract _ X x) x). auto with sets.
          assert (H2: exists n':nat, cardinal _ (Subtract _ X x) n').
          { eapply finite_cardinal.
            eapply Finite_downward_closed with (A:= X).
            {  eapply cardinal_finite. exact H0. } { auto with sets. } }
          
          destruct H2 as [n' H2].
          rewrite H1 in H0.
          assert (H3: cardinal _ (Add _ (Subtract U X x) x) (S n') ).
          { eauto with sets. eapply card_add. tauto.
            intro. unfold Subtract in H3. unfold Setminus in H3.
            unfold In in H3. destruct H3 as [H3 H4].
            apply H4. apply In_singleton.  }

          assert (H4: S n = S n' ).
          { eapply cardinal_unicity. exact H0. exact H3. }
          assert (H5: n=n'). injection  H4. tauto. rewrite H5. auto. }  Qed.  



    
Hint Resolve Singleton_card Couple_card_1 Couple_card_2 Disjoint_card : sets_card.
Ltac apply_set_equal:= (apply Extensionality_Ensembles; unfold Same_set; split).


(*   ------------------------Some Non- Trivial Facts-----------------------------------------   *)




  

Lemma Power_set_finite: forall (U: Type)(A: Ensemble U),
                               Finite _ A -> Finite _ (Power_set _ A).
Proof. { intros U A0 H0. apply finite_cardinal in H0 as H1. destruct H1 as [n0 H1].
       generalize H1. generalize A0 as A. generalize n0 as n. clear H1 n0 H0 A0. intro n.
       induction n.
       (* trivial case when A is empty set *)
       { intro. intro. 
         pose (Phi:= Empty_set U). 
         assert (H2: A = Phi).
         { unfold Phi.  apply cardinal_invert with (p:=0) in H1. auto. }
         assert (H3: Power_set _ A = Singleton _ Phi ).
         { apply Extensionality_Ensembles. unfold Same_set.
           split.
           { rewrite H2.
           unfold Included. intros. destruct H.
           assert (X = Phi).
           { unfold Phi. unfold Phi in H. auto with sets. } 
           Print Singleton. rewrite H0. auto with sets.  } 
           { unfold Included.  intros. destruct H. rewrite H2.
             assert (H3: Included _ Phi Phi).
             { auto with sets. } generalize H3. apply Definition_of_Power_set. }  } 
         assert (H4: cardinal _ (Power_set _ A) 1).
         { rewrite H3. auto with sets_card.  } 
         eapply cardinal_finite with (n:=1). auto. }

       (* Induction step *)
       { intro. intro.
         assert (H0: True). trivial. 
         eapply cardinal_invert with (p:= S n) in H1 as H2.
         destruct H2 as [A0 H2]. destruct H2 as [a H2].  destruct H2 .
         destruct H2 .
         pose (PA:= Power_set _ A).
         pose (PA0 (e: Ensemble U):= In _ PA e /\ ~ In _ e a).
         pose (PA0' (e: Ensemble U):= In _ PA e /\  In _ e a).
         assert (T0: A0 = Subtract _ A a ).
         { rewrite H. auto with sets. }
         assert (H4: PA = Union _ PA0 PA0' ).
         { apply_set_equal.
           { unfold Included. intros. elim (classic ( In _ x a)).
             intro.  apply Union_intror. unfold In.  unfold PA0'. tauto.
             intro. apply Union_introl. unfold In. unfold PA0. tauto. }
           { unfold Included. intros. destruct H4.
             unfold PA0 in H4.  apply H4.  unfold PA0' in H4. apply H4. }  } 
         
         assert (H5: PA0 = Power_set _ A0).
         { apply_set_equal. 
           { unfold Included. intros. unfold In in H5. unfold PA0 in H5.
           apply Definition_of_Power_set.  destruct H5. unfold PA in H5. rewrite H in H5.
           destruct H5. unfold Add in H5.  unfold Included. intros.
           unfold Included in H5. apply H5 in H7 as H8. destruct H8. auto.
           destruct H8. contradiction. }
           { unfold Included. intros.  unfold In. unfold PA0.
             destruct H5. unfold PA.  split. rewrite H. unfold Add.
             apply Definition_of_Power_set.  auto with sets.  intro. apply H2.
             auto with sets.   } } 
         assert (H6: Finite _ PA0). (* Using the IHn. *)
         { rewrite H5. apply IHn.  auto. }

         pose (f (e: Ensemble U):= Add _ e a).
         assert (H7: PA0' = Im _ _ PA0 f).
         { apply_set_equal.
           { unfold Included. intro y. intros.  unfold In in H7. unfold PA0' in H7.
             pose (X0:= Subtract _ y a).
             apply Im_intro with (x:=X0).
             { rewrite H5.  apply Definition_of_Power_set.  destruct H7. unfold PA in H7.
              destruct H7.  unfold Included. intros. unfold X0 in H9.
              destruct H9.  rewrite T0. unfold Subtract. unfold In. unfold Setminus.
              split. auto with sets. auto. }
             unfold f. unfold X0. destruct H7.  auto with sets. }
           { unfold Included. intro y. intros.  destruct H7. unfold f in H8.
             unfold In. unfold PA0'.
             split.
             { rewrite H8. unfold PA.
             apply Definition_of_Power_set. unfold Add.  unfold Included. intros.
             destruct H9.
             { unfold In in H7. unfold PA0 in H7.
             destruct H7. unfold PA in H7. destruct H7. auto with sets. } 
             { destruct H9. rewrite H. auto with sets. } } 
             { rewrite H8. auto with sets. }    }  }  

         assert (H8: PA = Power_set _ A).
         { unfold PA. reflexivity. }

         rewrite <- H8. rewrite H4.
         apply Union_preserves_Finite. auto.
         rewrite H7. apply finite_image. auto.   }     }  Qed.  


Variable U: Type. 


   Lemma Union_over_empty: (Union_over  (Empty_set _ )) = (Empty_set U).
   Proof. { apply Extensionality_Ensembles. unfold Same_set.
          split.
          { unfold Included. intros. destruct H. destruct H as [Ha Hb].
            unfold In in Ha. inversion Ha.  }
          { unfold Included. intros. destruct H.  }  } Qed.

   Lemma Union_over_P1: forall (L: Ensemble (Ensemble U)) (S: Ensemble U),
       Union_over ( Add _ L S) = Union _ (Union_over L) S .
   Proof. { intros.
            apply Extensionality_Ensembles. unfold Same_set.
            split.
            {  unfold Included. intros. unfold In in H.  unfold Union_over in H.
               unfold Add in H. destruct H as [S1 H].  destruct H as [Ha Hb].
               destruct Ha.
               { apply Union_introl. unfold In. unfold Union_over. exists x0;tauto. }
               { apply Singleton_P1 in H. rewrite H. apply Union_intror. tauto. } }
            {  unfold Included. intros. unfold In in H. destruct H.
               { destruct H.  unfold In. unfold Union_over.  exists x0.
                 unfold In. unfold Add. split. apply Union_introl. tauto. tauto. }

               {  unfold In. unfold Union_over. exists S. split. auto with sets.  tauto. } 
            } 
            
          } Qed.  
  
         

   Lemma Finite_Union_of_Finite_Sets: forall L: Ensemble (Ensemble U),
       (Finite _ L /\ (forall S: Ensemble U, In _ L S -> Finite _ S))-> Finite _ (Union_over L).
   Proof. { intros.
          assert (H1: exists n: nat, cardinal _ L n).
          { apply finite_cardinal. tauto. } destruct H1 as [n0 H1 ].

          generalize H.  generalize H1. generalize L. generalize n0 as n. clear L H n0 H1.
          induction n.

          (* Base case : when |L|= 0, ie L is empty set  *)
          intros.
          { assert ( H3: L = Empty_set _ ).  auto with sets.
            eapply cardinal_elim with (X:= L) (p:= 0) . tauto.
            rewrite H3. rewrite Union_over_empty. auto with sets. }

          (* Induction Step *)
          intros L. intros. destruct H as [H2 H3].
          assert (H4: Inhabited _ L).
          { eapply cardinal_elim with (X:= L)(p:= (S n)). auto.  }
          destruct H4 as [S H4].

          pose ( L0:= Subtract _ L S).
          assert ( L = Add _ L0 S ). unfold L0. auto with sets.

          rewrite H. rewrite Union_over_P1.

          apply Union_preserves_Finite .
          { eapply IHn. apply Set_Sub_card.  auto. auto.
            split. eapply Finite_downward_closed with (A:= L). auto.
            unfold L0. auto with sets. intros. cut (In _ L S0). auto.
            rewrite H.  auto with sets.  }
          auto.  } Qed. 



             

End BasicFacts.




Section Some_more_facts.

  Ltac apply_equal:= (apply Extensionality_Ensembles; unfold Same_set; split).

  Variable U:Type.

Lemma Not_Inh_Empty: forall (U:Type) (A: Ensemble U), ~ Inhabited _ A -> A = Empty_set U.
    Proof. { intros. Print Inhabited.
           apply_equal.
           { unfold Included. intros. absurd (Inhabited _ A). auto.
             apply Inhabited_intro with (x:=x). auto. }
           { unfold Included. intros. unfold In in H0. inversion H0. } } Qed. 


    Lemma Not_Empty_Inh:  forall (U:Type) (A: Ensemble U),  A <> Empty_set U  -> Inhabited _ A .
    Proof. { intros. elim (classic (Inhabited _ A)). tauto. intro.
             absurd (A = Empty_set U0). auto. apply Not_Inh_Empty. auto.  } Qed.

   Lemma Union_setminus: forall A B : Ensemble U, Union _ A B = Union _ A (Setminus _ B A).
   Proof. { intros.  apply_equal.
          { unfold Included. intros. destruct H. apply Union_introl. auto.
            elim (classic (In _ A x)).
            { intro. apply Union_introl. auto. }
            { intro. apply Union_intror. unfold In. unfold Setminus. tauto. } }
          { unfold Included. intros. destruct H. apply Union_introl.  auto.
            destruct H. apply Union_intror. auto. } } Qed.
   
   Lemma Included_setminus: forall A B: Ensemble U, Included _ (Setminus _ A B) A.
   Proof. intros. unfold Included. intros. destruct H. auto.  Qed.

   Lemma Disj_comm: forall A B: Ensemble U, Disjoint _ A B -> Disjoint _ B A.
   Proof. { intros. Print Disjoint. destruct H. apply Disjoint_intro. intro.
          cut ( ~ In U (Intersection U A B) x).
          intros. intro. apply H0. destruct H1. auto with sets. apply H. } Qed. 
   

   Lemma Disj_Setminus: forall A B: Ensemble U, Disjoint _ (Setminus _ A B) B.
   Proof. { intros. apply Disjoint_intro.  intro. intro. destruct H. destruct H.
          contradiction. } Qed. 

   Lemma Disj_set_inc_disj: forall A B C: Ensemble U, Disjoint _ A B -> Included _ C B ->
                                                 Disjoint _ A C.
   Proof. { intros. destruct H. apply Disjoint_intro.  intro. intro. destruct H1.
          assert (In _ B x).
          { apply H0. auto. }
          absurd (In U (Intersection U A B) x).
          auto. auto with sets. } Qed. 

   Lemma Union_over1: forall (E: Ensemble (Ensemble U))(e: Ensemble U), In _ E e ->
                                                                   Included _ e (Union_over E).
   Proof. { intros. unfold Included.  intros. unfold In. unfold Union_over.
            exists e. tauto. } Qed.

   

  
End Some_more_facts.
                                                                                                                                                                        
                                                                                                                               
                                 