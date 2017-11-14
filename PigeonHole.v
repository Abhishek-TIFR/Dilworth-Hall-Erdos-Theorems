(* ----- This file contains different variants of Pigeon Hole Principles --------- )

   Most of the lemmas are concerned with the relational version of PHP. They become useful if we
   have relations but not neccessarily functions between two sets A and B.
   The important results and their descriptions are as follows:

   Notations: Let R be a relation between set A and B. Then,
              Dom(R): { x:A| R x y for some y:B}
              Ran(R): { y:B| R x y for some x:A}   

        Let R be a relation between set A and B. We say that R represents:
             A. R represents a function from A to B iff
                                    i) every element of A is related to some element of B.

             B. R represents a a one-one function from A to B 
                                 iff  
                                    i) every element of A is related to some element of B, and
                                   ii) no two diff elements of A is related to same element of B

   1) Lemma Pigeon_Relation0:  Let R be a relation between set A and B such that 
                               every element of A is related to some element of B 
                               and Ran(R) is included in B. Also assume that the 
                               size of set A is strictly more than the size of B. Then
                               this Lemma assures that there exists two different 
                               elements x, y  in A such that both are related to the
                               same element z in B.  

   2) Lemma Pigeon_Relation:  Let R be a relation between set A and B such that 
                               every element of A is related to some element of B and the 
                               size of set A is strictly more than the size of B. Then
                               this Lemma assures that there exists two different 
                               elements x, y  in A such that both are related to the
                               same element z in B. 
   3) Lemma Pigeon_Function:  Let f be a function from U to V. Assume A is a subset of U
                              and f(A) represents the image of f restricted to A. If  
                               size of set A is strictly more than the size of f(A) then
                               this Lemma assures that there exists two different 
                               elements x, y  in A such that both are mapped to the
                               same element z in B.
   4) Lemma Bijection_Relation: Let R represents one one fun from A to B and |A|= |B| then 
                                every element of B has a preimage in A. 

   5) Lemma Bijection_Relation1: If R is a one one relation between A to B and |A|=|B|, then
                                 its inverse is also one one from B to A.  

---------------------------------------------------------------------------------------------*
---------------------------------------------------------------------------------------------*)



(* Require Export Finite_sets. *)
(* Require Import Arith. *)
(* Require Import ZArith. *)
(* Require Export Finite_sets_facts.*)
Require Export Classical.
Require Export Gt.
Require Export Lt.
Require Export Le.

Require Export Image.
Require Export omega.Omega.



Section PHP.

Variable U V :Type.



  Lemma EM: forall P:Prop, P \/ ~P.
  Proof. { intro.  elim classic with (P:=P). intro.
           left. assumption. right. assumption. }  Qed.

  Open Scope nat_scope.

  Lemma negation_of_exist: forall (P Q: U-> Prop),
                             (~ (exists x:U, P x /\ Q x)-> (forall x:U, P x -> ~ Q x)).
  Proof. { intros. intro.  absurd (exists x: U, P x /\ Q x).
    assumption. exists x. split. assumption. assumption. }  Qed.
  
  

  Let Almost_Function := fun (R: U-> V-> Prop)(A: Ensemble U) =>
                           (forall x:U, In _ A x -> (exists y:V,  R x y )).
    Let Image_Included := fun (R: U-> V-> Prop) (A: Ensemble U) (B: Ensemble V)=>
                               (forall (x:U) (y:V), In _ A x -> R x y -> In _ B y ).


 Lemma Pigeon_Relation0: forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n m : nat),
       Almost_Function R A  -> Image_Included R A B->
       cardinal U A n -> cardinal V B m -> (m < n) ->
       (exists (x y: U) (z:V) , In _ A x /\ In _ A y /\ In _ B z /\ x<>y /\ (R x z /\ R y z)).
      

    Proof. { (* rearranging forall variables to get a stronger induction hypothesis *)

      intros A0 B0 R0 n0.
     
      generalize R0 as R; generalize B0 as B; generalize A0 as A. generalize n0 as n.
      clear A0 B0 R0 n0.


      induction n. (* induction on the size of set A *)
      

      (* BASE CASE *)
      intros. {  absurd (m < 0); repeat ( auto with arith  ). }
      (* BASE CASE Over *)        
      

      intros A0 B0 R m.
      intros.

      (* Proving A0 is non empty *)

      assert (H4: exists A: _,(exists x : _, A0 = Add U A x /\ ~ In U A x /\ cardinal U A n)).
      { apply cardinal_invert with (U:=U) (p:=S n) ( X:=A0). assumption. }

      destruct H4 as [A H4]; destruct H4 as [a H4]. (* extracting an a:A0 *)
      destruct H4 as [H4a H4]; destruct H4 as [H4b H4].

      unfold Almost_Function in H; unfold Image_Included in H0.

      

      (* using the Almost_Function property extracting a "b:V" such that R a b *) 

      destruct H with (x:=a) as [ b Hb].  
      rewrite H4a.  assert( In U (Add U A a) a).  unfold Add. apply Union_intror.
      Print Singleton. apply In_singleton. assumption.

      (* using the Image_Included we show that In _ B0 b *)

      assert (H0a: In _ A0 a). { rewrite H4a. unfold Add. apply Union_intror.
      Print Singleton. apply In_singleton. }
      assert (H0b: In _ B0 b). { apply H0 with (x:= a)(y:= b). assumption. assumption. }

      (* proving that cardinality of B0 is greater than 0 since it is inhabited *)
      assert(m_gt_0: m > 0). {
      
      assert(Inh: Inhabited V B0).
      generalize H0b. generalize b. apply Inhabited_intro.

      apply inh_card_gt_O with (U:=V)(X:=B0). assumption. assumption. }


      elim (EM (exists x: U, In _ A x /\ R x b )).

      (* In the following discussion A0 is A U {a} and B0 is B U {b} 
         OR equivalently B := subtract B0 b *)

      (* CASE1: when an element from A is related to b *) {
      intro. destruct H5 as [a' H5]. destruct H5 as [H5a H5b].
      (* a a' and b act as certificates.*)
      exists a. exists a'.  exists b. split.
      rewrite H4a.  assert( In U (Add U A a) a). unfold Add. apply Union_intror.
      Print Singleton. apply In_singleton. assumption.

      split.  rewrite H4a. unfold Add. apply Union_introl. assumption.
      split. assumption.
      split. intro. absurd (In U A a). assumption. rewrite H5. assumption.
      split. assumption. assumption. }

      (* CASE2: when no element from A is related to b *) {
      (* Let B := Subtract V B0 b.*)
      intro.
      assert (H6: forall x:U, In U A x -> ~ R x b). {
      apply negation_of_exist. assumption. }
      
    
      (* extract the certificate using IHn as u u' v H7 *)

      destruct IHn with (A:=A)(B:= Subtract V B0 b)(R:=R)(m:=  pred m) as [u H7].

      (* proving all the precondition of Induction hypothesis IHn *)
      {
      unfold Almost_Function. intro. intro. apply H. rewrite H4a. unfold Add.
      apply Union_introl. assumption. }

      { unfold Image_Included. intros.
      assert (H9: In _ B0 y). apply H0 with (x:=x).
      rewrite H4a. unfold Add. apply Union_introl. assumption.
      assumption. unfold Subtract. unfold Setminus. unfold In.
      split. unfold In in H9. assumption. intro H10. Check H10.
      assert (b=y). inversion  H10. reflexivity.
      absurd ( R x b ).  apply H6. assumption. rewrite H11. assumption. }

      { assumption. }
      { simpl.
      

      apply card_soustr_1 with (X:=B0)(x:=b)(n:= m ).
      assumption. assumption. }

      
      
      { assert (TFact1: n = pred (S n)). omega.  rewrite TFact1.
      omega.  }

      { destruct H7 as [u' H7]. destruct H7 as [v H7].

      exists u. exists u'. exists v.
      destruct H7 as [H7a H7]; destruct H7 as [H7b H7]; destruct H7 as [H7c H7].
      repeat (split;[ (rewrite H4a; unfold Add; apply Union_introl; assumption)| idtac ]).

      
      split. unfold Subtract in H7c. unfold In in H7c.  unfold Setminus in H7c.
      destruct H7c as [H7c H7c']. assumption.

      assumption. }

      }

      }
      Qed.

   

 Lemma Pigeon_Relation: forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n m : nat),
        (forall x:U, In _ A x -> (exists y:V, In _ B y /\ R x y)) ->
       cardinal U A n -> cardinal V B m -> (m < n) ->
       (exists (x y: U) (z:V) , In _ A x /\ In _ A y /\ In _ B z /\ x<>y /\ (R x z /\ R y z)).
 Proof. { intros.
          pose ( R':= (fun (x:U)(y:V)=>  In _ B y /\ R x y) ). 
        assert(H3: exists (x y : U) (z : V), In U A x /\ In U A y /\ In V B z /\ x <> y /\
                                             R' x z /\ R' y z ). 
        apply Pigeon_Relation0 with (n:=n)(m:=m). 
        { unfold Almost_Function. unfold R'. 
        assumption. }
        { unfold Image_Included. unfold R'. 
        intros. apply H4. }
        { assumption. }
        { assumption. }
        { assumption. }
        { unfold R' in H3.  repeat (destruct H3).
        exists x. exists x0. exists x1.
        split. assumption. repeat (try (split); [ apply H4 | idtac] ). apply H4. } 
        }  Qed.


 Lemma Pigeon_Function: forall (A: Ensemble U)(f: U -> V)(n m :nat),
             cardinal U A n -> cardinal _ (Im U V A f) m ->
             m < n -> (exists x y: U, A x /\ A y /\ x<>y /\ f x = f y). 
Proof. {

  (* Rearranging forall variables to bring "n" in the front for using 
   induction on n *)
  
  intro A0; intro f0; intro n0.
  generalize f0 as f; generalize A0 as A. generalize n0 as n.
  clear A0 f0 n0.

  (* reasoning the proof by using induction on the size of set A, i.e "n" *)
  induction n.
                                       (* BASE CASE *)
  intros.
  absurd (m < 0).
  apply lt_n_0. exact H1.              (* BASE CASE OVER *)
  
  intro A0; intro f; intro m0.         
  intro.
  Print cardinal_invert.
                                       (* Proving A0 is non empty *)
  assert (exists A: _,(exists x : _, A0 = Add U A x /\ ~ In U A x /\ cardinal U A n)).
  apply cardinal_invert with (U:=U) (p:=S n) ( X:=A0) .
  exact H.
  destruct  H0 as [A  H1].
  destruct H1 as [a H2].          (* Instantiation of an element from A0 *)


  elim (EM (In V (Im _ _ A f) (f a) )). (* EM on "f a : Im A f "*)

  intro F1.                           (* CASE "f a belongs Im A f" *)
  apply Im_inv in F1.
  destruct F1 as [b F1].
  intro H1.
  intro H0.
  exists a; exists b.                 (* then a and b act as certificate  *)
  destruct H2 as [H2a H2].
  unfold Add in H2a.
  rewrite H2a.
  split. apply Union_intror. apply In_singleton.
  split. apply Union_introl. destruct F1 as [F1a F1b]. exact F1a.
  split. intro.    (* we prove that H2b F1a and H3 are inconsistent *)
  destruct H2 as [H2b H2]. destruct F1 as [F1a F1].
  absurd (In U A b). rewrite <- H3. exact H2b. exact F1a.
  destruct F1 as [F1a F1]. symmetry.  exact F1.

  intro.                           (* case " f a does not belong Im A f" *)
  destruct H2 as [H2a H2]; destruct H2 as [H2b H2].
  intro H3. assert (forall m:nat, cardinal V (Im _ _ A f) m -> cardinal  V (Im _ _ A0 f)  (S m)).
  intro m. intro H4.              (* if m is size of Im A then size of Im A0 will be S m  *)
  rewrite H2a. assert (Im _ _ (Add _ A a) f = Add _ (Im _ _  A f) (f a)).
  apply Im_add with (X:=A)(x:=a)(f:=f). rewrite H1.
  apply card_add . exact H4. exact H0.

  
  intro. assert (exists x y : U, A x /\ A y /\ x <> y /\ f x = f y).
  assert (exists m:nat, cardinal V (Im _ _ A f) m ). (* just to say let size of Im A be m *)
  apply cardinal_Im_intro with n.  exact H2. destruct H5 as [m H5].
  apply IHn with m.   exact H2. exact H5.
                                           (* proof of m<n *)
  assert (cardinal V (Im _ _ A0 f)(S m)).
  assert (H6:cardinal V (Im _ _ A f) m ). assumption.  apply H1 in H5. exact H5.
  assert (m0= S m). apply cardinal_unicity with (X:= Im _ _ A0 f).
  assumption. assumption.   rewrite H7 in H4. generalize H4. apply lt_S_n.
  destruct H5 as [b1 H5]; destruct H5 as [b2 H5].
  exists b1; exists b2. destruct H5 as [H5a H5]. destruct H5 as [H5b H5].
  split. rewrite H2a. apply Union_introl. unfold In. assumption.
  split. rewrite H2a. apply Union_introl. unfold In. assumption.
  exact H5.  }  Qed.


(* If there is an one one fun f from A to B and |A|= |B| then  every element of B has a 
   preimage in A *)
Lemma Bijection_Relation: forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n : nat),
        (forall x:U, In _ A x -> (exists y:V, In _ B y /\ R x y)) ->
        (forall (x y: U)(b: V), (In _ A x /\ In _ A y /\ In _ B b /\ R x b /\ R y b)-> x=y)->
          cardinal U A n -> cardinal V B n ->
          (forall b:V, In _ B b -> (exists a: U, In _ A a /\ R a b)).
 Proof. {
   intros.
   elim (EM (exists a : U, In U A a /\ R a b)). trivial.
   (* Assuming that no element from A is related to b we proceed to show contradiction *)
   intro H4.
   assert (H4a: forall a:U, In U A a ->  ~ R a b). {
     assert ( H4a: forall a: U, ~ In U A a \/ ~ R a b).  {
       assert (H4b:forall a: U, ~ (In U A a /\ R a b )) . { apply not_ex_all_not.  apply H4. }
                                                    intro a. apply not_and_or . auto. }
     intros a H5.  elim H4a with a.  { intro. contradiction. } { trivial. } }
   assert (Ha:  forall x : U, In U A x -> exists y : V, In V (Subtract _ B b) y /\ R x y). {
     intros x H3a.
     assert (H3b: exists y : V, In V B y /\ R x y ). { apply H. auto. }
     destruct H3b as [y H3b].
     exists y. split. unfold Subtract. unfold In. unfold Setminus.
     split. tauto.  intro H5. assert (H6: b=y ). inversion H5. reflexivity.
     absurd ( R x y). { rewrite <- H6. eauto. }  apply H3b. apply H3b. } 
   assert (Card_1: cardinal _ (Subtract _ B b) (pred n) ). { apply card_soustr_1 ; auto. }
   

  assert (C1: (exists (x y: U) (z:V) , In _ A x /\ In _ A y /\ In _ B z /\ x<>y /\ (R x z /\ R y z))).
   {  assert (C2: (exists (x y: U) (z:V) ,
                     In _ A x /\ In _ A y /\ In _ (Subtract _ B b) z /\ x<>y /\ (R x z /\ R y z))).
      { apply Pigeon_Relation with (A:=A)(B:= (Subtract V B b)) (R:=R)(n:= n)(m:= pred n).
       { auto. }
       {auto. }
       { auto. }
       { assert (Card_2: n> 0). {
           apply inh_card_gt_O with (U:= V) (X:= B).
            apply Inhabited_intro with (U:=V) (x:= b). assumption. assumption. }
            auto with arith.   }  }

      destruct C2 as [x C2]. destruct C2 as [y C2]. destruct C2 as [z C2].
      exists x. exists y. exists z. repeat (apply C2 || (split; [apply C2| idtac]) ). }
   
   destruct C1 as [x C1]. destruct C1 as [y C1]. destruct C1 as [z C1].
   
  absurd (x=y). { apply C1. } { apply H0 with (b:=z).
  repeat (try(split); [apply C1 | idtac]). apply C1. }   } Qed. 
                                                                                                  
(* If R is a one one relation between A to B and |A|=|B|, then its inverse is also one one
   from B to A *)
 Lemma Bijection_Relation1:  forall (A: Ensemble U)(B: Ensemble V)(R: U-> V-> Prop)(n : nat),
        cardinal U A n -> cardinal V B n ->
        (forall x:U, In _ A x -> (exists y:V, In _ B y /\ R x y)) ->
        (forall (x y: U)(b: V), (In _ A x /\ In _ A y /\ In _ B b /\ R x b /\ R y b)-> x=y)->
          (forall (x y: V)(a: U), ( In _ B x /\ In _ B y /\ In _ A a /\ R a x /\ R a y)-> x= y).
 Proof. { intros A B R n.  intros H H0 H1 H2. intros b1 b2 a. intro.
         elim (classic (b1=b2)) .   trivial.
         intro.
         (* We produce contradiction by assuming b1 <> b2 *)
         (* Case: b1 <> b2 *)
         assert (H5:  forall x: _, (In _ A x /\ x <> a) -> ~ R x b2 ). 
         { intros. intro.
           absurd (x=a).  tauto. eapply H2 . repeat (split; [tauto| idtac] ).
           split.  Focus 2. split.  apply H6. tauto. tauto. }
         pose (B1 := Subtract _ B b2).
         assert (Card_1: cardinal _ B1 (pred n) ).
         { apply card_soustr_1 ; tauto. } 

       assert (C1: (exists (x y: _) (z:_) , In _ A x /\ In _ A y /\ In _ B z /\ x<>y /\ (R x z /\ R y z))).
         {
  assert (C2: (exists (x y: _) (z:_) , In _ A x /\ In _ A y /\ In _ B1 z /\ x<>y /\ (R x z /\ R y z))).
  {  apply Pigeon_Relation with (A:=A)(B:= B1) (R:=R)(n:= n)(m:= pred n).
     { intros x H6. elim (classic (x=a) ).
       { intro.  exists b1.
         split.
         { unfold In. unfold B1. unfold Subtract. unfold Setminus.
           split. tauto. intro.  inversion H8. symmetry in H9. contradiction. }
         { rewrite H7. apply H3. } }
       { intro.
         assert (H1a : exists y : V, In V B y /\ R x y).
         { apply H1. auto. }
         destruct H1a as [y H1a].
         exists y.
         split.
         { unfold In. unfold B1. unfold Subtract. unfold Setminus.
           split. tauto.
           intro. inversion H8.
           absurd ( R x b2).  eapply H5. split. tauto. tauto.
           rewrite H9. tauto.  }
         { tauto. } }

     }
     { assumption. }
     { assumption. }
     { assert (Card_2: n> 0). {
           apply inh_card_gt_O with (U:= V) (X:= B).
           apply Inhabited_intro with (U:=V) (x:= b1). tauto. assumption. }
       auto with arith. }  }
  
     destruct C2 as [x C2]. destruct C2 as [y C2]. destruct C2 as [z C2].
      exists x. exists y. exists z. repeat (apply C2 || (split; [apply C2| idtac]) ). }

      destruct C1 as [x C1]. destruct C1 as [y C1]. destruct C1 as [z C1].

      absurd (x=y). { apply C1. } { apply H2 with (b:=z).
  repeat (try(split); [apply C1 | idtac]). apply C1.  }    }  Qed.


End PHP.























































