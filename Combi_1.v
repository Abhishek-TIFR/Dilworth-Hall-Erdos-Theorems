(* In this file some new tactics are defined to automate the proofs of some 
   trivial facts on numbers, logic, sets and finite partial orders.
1. auto_with_sets0: to prove some common facts on sets without reffering to the 
                    names of the theorems.
2. auto_with_arith0: to prove some trivial facts on natural numbers.

3. auto_with_card0: to prove some trivial facts about set cardinalities.

 Let R be a relation between set A and B. We say that:
             A. R represents a function from A to B iff
                                    i) every element of A is related to some element of B.

             B. R represents a a one-one function from A to B (or R is a bijective relation
                                   from A to B) iff  
                                    i) every element of A is related to some element of B, and
                                   ii) no two diff elements of A is related to same element of B.

4. Lemma Bijection_Relation3: If R is a bijective relation from A to B as well as from B to A. 
                              Then the size of sets A and B are equal.
5. Lemma Bijection_Relation5: If R is a bijective relation from A to B then |A|<= |B|.  *)


Require Export PigeonHole.
Require Export BasicFacts.
Require Export FPO_Facts.
Require Export FPO_Facts2.
Require Export omega.Omega.



 Ltac auto_with_logic1 :=
   match goal with
         | _:_ |-  ~ (forall n : ?U, ~ ?P n) -> exists n : ?U, ?P n => (apply not_all_not_ex)
         | _:_ |-  ~ (forall n : ?U, ?P n) -> exists n : ?U, ~ ?P n=> (apply not_all_ex_not)
         | _:_ |-  ~ (exists n : ?U, ?P n) -> forall n: ?U, ~ ?P n => (apply not_ex_all_not)
         |_:_ |-  ~ (exists n : ?U, ~ ?P n) -> forall n: ?U, ?P n => (apply not_ex_not_all)
         |_:_ |-  (exists n : ?U, ~ ?P n) -> ~ (forall n: ?U, ?P n) => (apply ex_not_not_all) 
         |_:_ |-   (forall n: ?U, ~ ?P n) -> ~ (exists n : ?U, ?P n) => (apply all_not_not_ex)
   end.

  Ltac auto_with_logic0 :=
   match goal with
         | _:_ |-  exists n : ?U, ?P n => (apply not_all_not_ex)
         | _:_ |-  exists n : ?U, ~ ?P n=> (apply not_all_ex_not)
         | _:_ |-  forall n: ?U, ~ ?P n => (apply not_ex_all_not)
         |_:_ |-   forall n: ?U, ?P n => (apply not_ex_not_all)
         |_:_ |-   ~ (forall n: ?U, ?P n) => (apply ex_not_not_all) 
         |_:_ |-   ~ (exists n : ?U, ?P n) => (apply all_not_not_ex)
   end.


 Ltac unfold_equal:= (apply Extensionality_Ensembles; unfold Same_set; split).

 Check le_trans.
 Check le_lt_trans.
 Check lt_le_trans.

 
 
 Ltac eapply_trans0 :=
   match goal with
   |_:_ |- Included ?U ?x ?B => (eapply Inclusion_is_transitive)
   |_:_ |- ?n <= ?p => (eapply le_trans)
   | _:_ |- ?n < ?p => (eapply lt_trans)
   |_:_ |- ?n <= ?m -> ?m < ?p -> ?n < ?p => (eapply le_lt_trans)
   |_:_ |- ?n < ?m -> ?m <= ?p -> ?n < ?p => (eapply lt_le_trans)
   end.
 


 Lemma Subtract1: forall (U:Type) (x:U) (X: Ensemble U), ~ In _ (Subtract _ X x) x.
 Proof. { intros. unfold Subtract. unfold In. unfold Setminus. intro. destruct H.
        auto with sets. } Qed. 
 
  Ltac auto_with_sets0:=
    match goal with
  | _:_ |- Union ?U ?A ?B = Union ?U ?B ?A => (apply Union_commutative)
  | _:_ |- Union ?U ?A ?A = ?A => (apply Union_idempotent)
  |_:_|- Union ?U ?A ?B = ?A => (apply Union_absorbs)
  |_:_ |- Intersection ?U ?A ?B = Intersection ?U ?B ?A => (apply Intersection_commutative )
  |_:_ |- Intersection ?U ?A (Union ?U ?B ?C) =
         Union ?U (Intersection ?U ?A ?B) (Intersection ?U ?A ?C) => (apply Distributivity)
  |_:_|- Union ?U ?A (Intersection ?U ?B ?C) =
        Intersection ?U (Union ?U ?A ?B) (Union ?U ?A ?C) => (apply Distributivity')
                                                              
  |_:_|- ~ Inhabited ?U ?A -> ?A = Empty_set ?U => (apply Not_Inh_Empty)
  |_:_|- ?A <> Empty_set ?U -> Inhabited ?U ?A => (apply Not_Empty_Inh)
  |_:_ |- Included ?U ?X (Empty_set ?U) -> ?X = Empty_set ?U => (apply less_than_empty)
                                                               
  |_:_|- Union ?U ?A ?B = Union ?U ?A (Setminus ?U ?B ?A) => (apply Union_setminus)
  |_:_|- Included ?U (Setminus ?U ?A ?B) ?A => (apply Included_setminus)
  |_:_|- Disjoint ?U ?A ?B -> Disjoint ?U ?B ?A => (apply Disj_comm)
  |_:_|- Disjoint ?U (Setminus ?U ?A ?B) ?B => (apply Disj_Setminus)
  |_:_|-  ~ In ?U (Subtract ?U ?X ?x) ?x => (apply Subtract1)
                                            
  |_:_|- Disjoint ?U ?A ?B -> Included ?U ?C ?B -> Disjoint ?U ?A ?C => (apply Disj_set_inc_disj)
  |_:_|- In _ ?E ?e -> Included _ ?e (Union_over ?E) => (apply Union_over1)
  |_:_|- Union_over (Add _ ?L ?S) = Union _ (Union_over ?L) ?S => (apply Union_over_P1)
  |_:_|- (Union_over (Empty_set (Ensemble ?U)) = Empty_set ?U) => (apply Union_over_empty)
  |_:_ |- Couple ?U ?x ?y = Couple ?U ?y ?x => (apply Couple_comm)
  |_:_ |- Included ?U ?X ?A -> Finite ?U ?X => (eapply Finite_downward_closed)
  |_:_|- Finite ?U (Union_over ?L) => (apply Finite_Union_of_Finite_Sets)
  |_:_|- Finite _ (Power_set ?U ?A) => (apply Power_set_finite)
  |_:_|- Finite _ ?A => (eapply cardinal_finite)
  
                                     
                                                                             
    end.

  
  Hint Resolve Power_set_finite Finite_Union_of_Finite_Sets finite_cardinal: sets0.
  Hint Resolve Couple_comm Union_over_empty Union_over_P1 Union_over1: sets0.
  Hint Resolve Disj_Setminus Included_setminus Union_setminus : sets0.
  Hint Resolve Not_Inh_Empty Not_Empty_Inh cardinalO_empty : sets0.
  Hint Resolve Distributivity Distributivity' : sets0.
  Hint Resolve Union_absorbs Union_commutative Intersection_commutative : sets0. 
  

  Ltac auto_with_arith0 :=
    match goal with
    |_:_|- ?n <= ?m -> ~ ?n > ?m => (apply nat_P1)
    |_:_|- (~ ?n > ?m) -> ?n <= ?m => (apply nat_P1)
    |_:_|- (~ ?n <= ?m)  -> ?n > ?m => (apply nat_P5)
    |_:_|- ?n > ?m -> ~ ?n <= ?m => (apply nat_P5)
    |_:_|- (S ?n ) = ?n + 1 => (apply nat_P0)
    |_:_|- (pred ?n ) = ?n -1 => (apply nat_P3)
    |_:_|- ?n > 0 -> S (pred ?n) = ?n => ( apply nat_P2)
    |_:_|- ?m <> ?n -> ( ?m < ?n \/ ?m > ?n ) => (apply nat_total_order)
    |_:_|- (?n <= ?m) \/ (?m <= ?n) => (apply nat_P6)
    end.

  Hint Resolve nat_P0 nat_P3 nat_P2 nat_P6 nat_total_order : arith0.
  

  Ltac auto_with_card0 :=
    match goal with
    |_:_|- cardinal ?U (Singleton ?U ?x) 1 => (apply Singleton_card)
    |_:_|- cardinal ?U (Couple ?U ?x ?y) 1 => (apply Couple_card_1)
    |_:_|- cardinal ?U (Couple ?U ?x ?y) 2 => (apply Couple_card_2)
    |_:_|- cardinal ?U (Union ?U ?A ?B) (?m + ?n) => (eapply Disjoint_card)
    |_:_|- cardinal ?U (Subtract ?U ?X ?x) ?n => (apply Set_Sub_card)
    |_:_|- ?m < ?n => (eapply incl_st_card_lt)
    |_:_|- ?m <= ?n => (eapply incl_card_le)
    |_:_|- ?n <= S ?m => (eapply card_Add_gen)
    |_:_|- ?m = ?n => (eapply cardinal_unicity)
    |_:_|- ?m > 0 => (eapply inh_card_gt_O)
    |_:_|- ?X = Empty_set ?U => (apply cardinalO_empty)
    |_:_|- exists p : nat, cardinal _ ?A p => (eapply finite_cardinal)
    |_:_|- Finite _ ?A => (eapply cardinal_finite)
    end.
  
                                          
  Hint Resolve Singleton_card Couple_card_1 Couple_card_2 Disjoint_card: card0.
  Hint Resolve Set_Sub_card incl_st_card_lt incl_card_le card_Add_gen : card0.
  Hint Resolve cardinal_unicity inh_card_gt_O cardinalO_empty : card0.



 
Section Bijection_Properties1.
Variable U V: Type.

 Lemma Bijection_Relation2:  forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n : nat),
        cardinal U A n -> cardinal V B n ->
        (forall y:V, In _ B y -> (exists x:U, In _ A x /\ R x y)) ->
        (forall (x y: V)(a: U), ( In _ B x /\ In _ B y /\ In _ A a /\ R a x /\ R a y)-> x= y)->
        (forall (x y: U)(b: V), (In _ A x /\ In _ A y /\ In _ B b /\ R x b /\ R y b)-> x=y).
 Proof. intros A B R' n Card_A Card_B.  apply Bijection_Relation1 with (U:=V)(V:=U) (A:=B) (B:=A) (n:= n).  auto. auto. Qed.

 Lemma Bijection_Relation3: forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n : nat),
     (forall x:U, In _ A x -> (exists y:V, In _ B y /\ R x y)) ->
     (forall b:V, In _ B b -> (exists a: U, In _ A a /\ R a b)) ->
     (forall (x y: U)(b: V), (In _ A x /\ In _ A y /\ In _ B b /\ R x b /\ R y b)-> x=y)->
     (forall (x y: V)(a: U), ( In _ B x /\ In _ B y /\ In _ A a /\ R a x /\ R a y)-> x= y)->
     cardinal U A n -> cardinal V B n.
 Proof. { intros A0 B0 R0 n. generalize A0 as A, B0 as B, R0 as R. clear A0 B0 R0.
        induction n.
        { intros. cut (B= Empty_set V). intro. rewrite H4. auto with sets.
          cut (A= Empty_set U ).
          { intro. cut (~ Inhabited _ B). auto with sets0. intro. destruct H5 as [b H5].
            assert (exists a : U, In U A a /\ R a b). auto. repeat (destruct H6).
            rewrite H4 in H6. inversion H6. }
          auto with sets0. }
        { intros.
          eapply cardinal_invert in H3 as H4.
          destruct H4 as [A0 H4];destruct H4 as [a H4]; destruct H4; destruct H5.
          assert (H7: In _ A a). rewrite H4;auto with sets.
          assert (H8: exists b:V , In _ B b /\ R a b). auto. destruct H8 as [b H8].
          pose (B0:= Subtract _ B b).
          assert ( H9: ~ In _ B0 b). unfold B0.  auto_with_sets0.
          assert (H10: B = Add _ B0 b). unfold B0; destruct H8; auto with sets.
          rewrite H10. apply card_add.
          { eapply IHn with (R:=R) (A:= A0).
            { intros. cut (exists y: V, In V B y /\ R x y).
              { intro. destruct H12 as [y H12]. destruct H12. exists y.
                split. unfold B0. unfold Subtract. unfold In. unfold Setminus.
                split. auto. intro. cut (b=y). intro. cut (x=a).
                intro. absurd (In U A0 a).  auto. rewrite <- H16;auto.
                apply H1 with (b:=b). rewrite H4.
                repeat ( try split; try (auto with sets || rewrite H15; auto ||  rewrite <- H15; tauto )).
                
                destruct H14; tauto. tauto.  } 
              { apply H. rewrite H4. auto with sets. } }

            { intro y. intros.  cut (exists x: U, In _ A x /\ R x y).
              { intro. destruct H12 as [x H12]. destruct H12. exists x.
                split.
                assert (A0= Subtract _ A a). rewrite H4. auto with sets.
                rewrite H14. unfold Subtract. unfold In. unfold Setminus.
                split. auto. intro. cut (a=x). intro. cut (b=y).
                intro. absurd (In _ B0 b).  auto. rewrite  H17;auto.
                apply H2 with (a:=a). rewrite H10.
                repeat ( try split; try (auto with sets || rewrite H16; tauto ||  rewrite <- H16; tauto )).
                
                destruct H15; tauto. tauto.  } 
              { apply H0. rewrite H10. auto with sets. } }

            { intros. apply H1 with (b:= b0). rewrite H4; rewrite H10.
              destruct H11.  destruct H12.  destruct H13.
              repeat (try split; try (auto with sets;tauto) ). }

             { intros. apply H2 with (a:= a0). rewrite H4; rewrite H10.
              destruct H11;destruct H12;  destruct H13.
              repeat (try split; try (auto with sets;tauto) ). }
             auto with sets.  }  auto.  }  } Qed.
End Bijection_Properties1.




Section Bijection_Properties2.
  Variable U V: Type. 

 Lemma Bijection_Relation4:  forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n : nat),
     (forall x:U, In _ A x -> (exists y:V, In _ B y /\ R x y)) ->
     (forall b:V, In _ B b -> (exists a: U, In _ A a /\ R a b)) ->
     (forall (x y: U)(b: V), (In _ A x /\ In _ A y /\ In _ B b /\ R x b /\ R y b)-> x=y)->
     (forall (x y: V)(a: U), ( In _ B x /\ In _ B y /\ In _ A a /\ R a x /\ R a y)-> x= y)->
     cardinal V B n -> cardinal U A n .
 Proof. { intros. eapply Bijection_Relation3 with (A:=B) (B:= A)(n:=n).
          apply H0. apply H. apply H2. apply H1. auto. } Qed.
 

 Lemma Bijection_Relation5:  forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n m : nat),
        (forall x:U, In _ A x -> (exists y:V, In _ B y /\ R x y)) ->
        (forall (x y: U)(b: V), (In _ A x /\ In _ A y /\ In _ B b /\ R x b /\ R y b)-> x=y)->
        cardinal U A n -> cardinal V B m -> n<= m.
 Proof. { intros. cut (~ n>m). auto_with_arith0. intro.
        assert (m<n). auto with arith.
        assert (exists (x y: U) (z:V) , In _ A x /\ In _ A y /\ In _ B z /\ x<>y /\ (R x z /\ R y z)).
        eapply Pigeon_Relation with (n:=n)(m:=m). apply H. tauto. tauto. tauto.
        repeat (destruct H5).
        absurd (x=x0). tauto. apply H0 with (b:= x1). tauto. } Qed.

 Lemma Bijection_Relation5':  forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n m : nat),
        (forall b:V, In _ B b -> (exists a: U, In _ A a /\ R a b))->
        (forall (x y: V)(a: U), ( In _ B x /\ In _ B y /\ In _ A a /\ R a x /\ R a y)-> x= y)->
        cardinal U A n -> cardinal V B m -> m<= n.
 Proof.  { intros. cut (~ m>n). auto_with_arith0. intro.
          assert (n<m). auto with arith.
          pose (R' (y: V) (x:U):= R x y).
        assert (exists (x y: V) (z:U) , In _ B x /\ In _ B y /\ In _ A z /\ x<>y /\ (R' x z /\ R' y z)).
        eapply Pigeon_Relation with (n:=m)(m:=n). unfold R'. apply H. tauto. tauto. tauto.
        repeat (destruct H5).
        absurd (x=x0). tauto. apply H0 with (a:= x1). tauto. } Qed.

 Lemma Bijection_Relation3':  forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n m: nat),
     (forall x:U, In _ A x -> (exists y:V, In _ B y /\ R x y)) ->
     (forall b:V, In _ B b -> (exists a: U, In _ A a /\ R a b)) ->
     (forall (x y: U)(b: V), (In _ A x /\ In _ A y /\ In _ B b /\ R x b /\ R y b)-> x=y)->
     (forall (x y: V)(a: U), ( In _ B x /\ In _ B y /\ In _ A a /\ R a x /\ R a y)-> x= y)->
     cardinal U A n -> cardinal V B m -> n=m.
 Proof. { intros. cut (n<=m /\ n>=m). omega. split.
        eapply Bijection_Relation5 with (A:=A)(B:=B)(R:=R);tauto.
        eapply Bijection_Relation5' with (A:=A)(B:=B)(R:=R);tauto. } Qed. 
           
        
 
End Bijection_Properties2. 



(*----------- Some FPO properties have been grouped in fpo and fpo_facts-------------- *)
  

Hint Resolve NoTwoCommon Singleton_is_chain Singleton_is_antichain :fpo.
Hint Resolve Antichain_exists Chain_exists Chain_cover_exists Antichain_cover_exists: fpo.
Hint Resolve Minimal_element_exists Maximal_element_exists: fpo.
Hint Resolve Minimal_is_antichain Maximal_is_antichain: fpo.
Hint Resolve Minimal_for_every_y Maximal_for_every_x: fpo.
Hint Resolve Largest_card_same Card_same_largest Largest_element_exists: fpo.
Hint Resolve Maximal_is_largest Minimal_is_smallest Smallest_element_exists: fpo.
Hint Resolve exists_largest_antichain exists_largest_chain :fpo.
Hint Resolve Union_over_cv_is_C: fpo.

Hint Resolve Chain_remains1 Chain_remains2 Largest_Chain_remains : fpo_facts.
Hint Resolve Antichain_remains1 Antichain_remains2 Largest_Antichain_remains: fpo_facts.