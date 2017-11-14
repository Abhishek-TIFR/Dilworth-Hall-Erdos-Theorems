(* This file contains the proof of Erdős-Szekeres theorem on sequences. 
   The Erdős-Szekeres theorem then states that for any two natural numbers
   m and n, every sequence of m.n+1 distinct integers contains an increasing 
   subsequence of length m+1 or a decreasing subsequence of length n+1. For
   a finite sequence s: Int_seq we prove,
   ------------------------------------------------------------------------------------------
   Theorem Erdos_Szeker: forall m n, cardinal _ (C_of s) (m*n+1) ->
    ( (exists s1: Int_seq, sub_seq s1 s /\ Is_increasing s1 /\ cardinal _ (C_of  s1) (n+1)) \/
      (exists s2: Int_seq, sub_seq s2 s /\ Is_decreasing s2 /\ cardinal _ (C_of  s2) (m+1)) ).
   -------------------------------------------------------------------------------------------

  Here Is_increasing and Is_decreasing capture the notions of increasing and 
  decreasing sequences respectively. That s1 is a subsequence of s2 is represented 
  by predicate sub_seq s1 s2. The exact definitions of these terms are, 

  Definition sub_seq (s1 s2: Int_seq): Prop:= Included _ (C_of s1) (C_of s2)/\
                                          (forall m n, (In _ (C_of s1) m /\
                                                   In _ (C_of s1) n )->
                                                  R_of s1 m n  ->  R_of s2 m n ).

  Definition Is_increasing (s: Int_seq): Prop:=  forall m n, 
         (In _ (C_of s) m /\ In _ (C_of s) n )->  R_of s m n -> m < n.

  Definition Is_decreasing (s: Int_seq): Prop:=  forall m n, 
         (In _ (C_of  s) m /\ In _ (C_of s) n )-> R_of s m n -> m > n.   *)

Require Import Combi_1.
Require Import BasicFacts2.
Require Import FPO_Facts3.
Require Export FiniteDilworth_AB.

Section Pre_ES.
 Variable U: Type.
  Variable FP: FPO U.
  Let C:= Carrier_of _ FP.
  Let R:= Rel_of _ FP. 

  Set Implicit Arguments.

  
 Lemma Pre_ES: forall (m n:nat),
     cardinal _ C (m*n+1) -> ((exists e: Ensemble U, Is_a_chain_in FP e /\ cardinal _ e (n+1))\/
                             (exists e:Ensemble U, Is_an_antichain_in FP e /\ cardinal _ e (m+1))).
 Proof.  { intros.
     elim (classic (exists e : Ensemble U, Is_an_antichain_in FP e /\ cardinal U e (m + 1))).
    (*Case1: When there is an antichain of size m+1 *)
     tauto.
     (*Case2: When there is no antichain on size m+1 *)
     intro. left.
    (* let la be the largest antichain and la_size be its cardinality *)
     assert (exists(la_size:nat)(la:Ensemble U), Is_largest_antichain_in FP la/\ cardinal _ la la_size).
     auto with fpo. destruct H1 as [la_size H1]. destruct H1 as [la H1]. destruct H1.
    (* hence size of largest antichain must be smaller than m+1 *)
     assert (F1: la_size <= m ).
     { elim (classic (la_size <= m)).  tauto.
       intro.
       assert ( m+1 <= la_size ). omega.
       assert (exists la':Ensemble U, Included _ la' la /\ cardinal _ la' (m+1)).
       {eapply Exists_a_subset_m with (n:= la_size); tauto. } destruct H5 as [la' H5].
       destruct H5.
       assert (Inhabited _ la').
       { replace (m+1) with (S m) in H6. 
         eapply cardinal_elim with (X:=la')(p:= S m). auto. omega. }

       absurd (exists e : Ensemble U, Is_an_antichain_in FP e /\ cardinal U e (m + 1)).
       auto. exists la'. split. eapply Antichain_sub; eauto. apply H1. auto. }

     (* according to the Dilworth's theorem there must exist a chain cover of size la_size *)
     assert(exists (cv: Ensemble (Ensemble U)), Is_a_chain_cover FP cv /\
                                           cardinal _ cv la_size).
     {eapply DilworthB. exists la;tauto. } destruct H3 as [cv H3]. destruct H3.

     assert (F2: C= Union_over cv).
     {unfold C. auto with fpo. }

     assert (F3: cardinal _ (Union_over cv) (m*n+1)).
     {rewrite <- F2. auto. }

     assert (exists (e:Ensemble U)(n':nat), In _ cv e /\ cardinal _ e n' /\ n' > n).
     { eapply U_Bound3. split. apply H4. apply F1. auto. }

     destruct H5 as [chain H5]. destruct H5 as [n' H5]. destruct H5. destruct H6.

     assert (F4: n+1 <= n'). omega.
     assert (F5: Is_a_chain_in FP chain). apply H3. auto.

     assert (F6: exists chain':Ensemble U, Included _ chain' chain /\ cardinal _ chain' (n+1)).
     {eapply Exists_a_subset_m with (n:=n');tauto. } destruct F6 as [chain' F6].
     destruct F6.

     assert (F7: Inhabited _ chain').
     { replace (n+1) with (S n) in H9. 
       eapply cardinal_elim with (X:=chain')(p:= S n).  auto. omega. }

     exists chain'. split. eapply Chain_sub; eauto. auto. } Qed. 
     
 Unset Implicit Arguments. 
  
End Pre_ES.
        


Section Erdos.

  Variable U:Type.

  Definition Asymmetric := fun (U : Type) (R : Relation U) => forall x y : U, R x y -> ~ R y x.
  Set Implicit Arguments.
  Print PO.
  Print Totally_ordered.
  Print Order.
  
 
  Definition Strict_Order (U: Type)(R: Relation U): Prop:=  Transitive U R /\  Asymmetric  _ R.
  Definition Total_Order (U:Type )(R: Relation U)(S: Ensemble U): Prop:=
    forall s1 s2, (In _ S s1 /\ In _ S s2)-> ( R s1 s2 \/ R s2 s1).
  
  Record Int_seq:Type:= Def_of_seq
                          { C_of: Ensemble nat;
                            R_of: Relation nat;
                            Seq_cond1: Inhabited _ (C_of);
                            Seq_cond2: Finite _ (C_of);
                            Seq_cond3: Transitive _ R_of;
                            Seq_cond4: Asymmetric _ R_of;
                            Seq_cond5: Total_Order R_of C_of ;
                            }.
                            
  Definition sub_seq (s1 s2: Int_seq): Prop:= Included _ (C_of s1) (C_of s2)/\
                                          (forall m n, (In _ (C_of s1) m /\
                                                   In _ (C_of s1) n )->
                                                  R_of s1 m n  ->  R_of s2 m n ).
  Definition Is_increasing (s: Int_seq): Prop:=  forall m n, (In _ (C_of s) m /\ In _ (C_of s) n )->
                                                     R_of s m n -> m < n.
  Definition Is_decreasing (s: Int_seq): Prop:=  forall m n, (In _ (C_of  s) m /\ In _ (C_of s) n )->
                                                       R_of s m n -> m > n. 
  
  Variable s: Int_seq.
 
  Hint Resolve Seq_cond1 Seq_cond2 Seq_cond3 Seq_cond4 Seq_cond5: seq_def.

  Lemma Total_Order1: forall (U: Type)(S1 S2: Ensemble U)(R: Relation U),
        Total_Order R S2 -> Included _ S1 S2 -> Total_Order R S1.
    Proof. { unfold Total_Order. intros. apply H.  destruct H1. split;auto with sets. } Qed.  

  Theorem Erdos_Szeker: forall m n, cardinal _ (C_of s) (m*n+1) ->
    ( (exists s1: Int_seq, sub_seq s1 s /\ Is_increasing s1 /\ cardinal _ (C_of  s1) (n+1)) \/
      (exists s2: Int_seq, sub_seq s2 s /\ Is_decreasing s2 /\ cardinal _ (C_of  s2) (m+1)) ).

  Proof. { Print FPO. Print PO. intros.
         pose (C:= C_of s).
         pose (R (m n:nat):= m=n \/ (R_of s m n /\ m < n) ).

         assert (F1: Inhabited _ C).
         { unfold C;auto with seq_def. }
         assert (F2: Order _ R).
         { apply Definition_of_order.
            { unfold Reflexive.  unfold R. intro. left. tauto. }
            { unfold Transitive. intros x y z. unfold R.
              intros. elim H0;elim H1.
              { intros; left; omega. }
              { intros; right; rewrite H3; auto. }
              { intros; right; rewrite <- H2; auto. }
              { intros. right. destruct H2. destruct H3. split.
                cut (Transitive _ (R_of s)). eauto. auto with seq_def. omega. } }
            { unfold Antisymmetric. intros x y. intros. destruct H0;destruct H1.
              auto. auto. rewrite H1; reflexivity. destruct H0; destruct H1.
              absurd (x<y).  omega. auto.  } }
         assert (F3: Finite _ C).
         { unfold C;auto with seq_def. }

           assert (HF3: Transitive nat (R_of s)).
           { auto with seq_def. }

           assert (HF4: Asymmetric nat (R_of s)).
           { auto with seq_def. }

         pose (P:= {| Carrier_of := C;
                      Rel_of:= R;
                      PO_cond1:= F1;
                      PO_cond2:= F2|}).
           pose (FP:= {|PO_of:= P; FPO_cond:= F3 |}).

           assert (F4: forall m n, R_of s m n -> m<>n).
           { intros. intro. rewrite H1 in H0.  absurd (R_of s n0 n0). apply HF4. auto. auto. }

           assert (F5: forall m n, R m n -> R_of s m n -> m < n).
           { intros. destruct H0. absurd ( m0=n0). apply F4;auto. auto. apply H0. }
           assert (F6: forall m n, R_of s m n -> ~ R n m ).
           { intros. intro.  destruct H1. cut (m0=n0). apply F4. auto. omega.
             absurd (R_of s m0 n0). apply HF4. apply H1. auto. } 

         (* In the partial order FP there exists either a chain  of size m+1 or an 
            antichain of size n+1 *)
         Check Pre_ES.

         assert (H0: (exists e : Ensemble nat, Is_a_chain_in FP e /\ cardinal _ e (n + 1)) \/
                     (exists e : Ensemble nat, Is_an_antichain_in FP e /\ cardinal _ e (m + 1))).
         { eapply Pre_ES; simpl; unfold C; auto. }

         elim H0.
         (* when there is a chain of length n+1 *)
         (* we can show that it is an increasing subsequence in s *)
         { intro. destruct H1 as [chain H1]. destruct H1.
           assert (HF2: Finite _ chain).
           { cut (Included _ chain C). cut (Finite _ C).
             intro. auto_with_sets0. auto. auto. apply H1. }
           
           assert (HF1: Inhabited _ chain).
           { apply H1. }
           
           assert (HF5: Total_Order (R_of s) (chain)).
           { cut (Included _ chain C).  eapply Total_Order1.
             unfold C. auto with seq_def. apply H1.  }

           Print Int_seq.
           pose (s0:= {|C_of:= chain; R_of:= R_of s;
                        Seq_cond1:= HF1; Seq_cond2:= HF2; Seq_cond3:= HF3;
                        Seq_cond4:= HF4; Seq_cond5:= HF5|}). 
           left. exists s0. split.
           (* need to prove that s0 is a sub_seq of s *)
           { unfold sub_seq. split. simpl. apply H1.
             intros. simpl in H4. auto. } split.
           (* need to prove that s0 is increasing *)
           { unfold Is_increasing. simpl. intros m0 n0. intros.
             cut (R m0 n0 \/ R n0 m0). 
             { destruct 1. auto. absurd(R n0 m0). apply F6. auto. auto.  }
             
             unfold Is_a_chain_in in H1.  apply H1. Print Couple. destruct H3.
             unfold Included. destruct 1;auto. }
           (* need to prove that size of s0 is n+1  *)
           { simpl. auto. }
         }

         (* when there is an antichain of length m+1 *)
         (* we can show that it is a decreasing subsequence in s *)
         { intro. destruct H1 as [A_chain H1]. destruct H1.
           assert (HF2: Finite _ A_chain).
           { cut (Included _ A_chain C). cut (Finite _ C).
             intro. auto_with_sets0. auto. auto. apply H1. }

           assert (HF1: Inhabited _ A_chain).
           { apply H1. }
           
           assert (HF5: Total_Order (R_of s) (A_chain)).
           { cut (Included _ A_chain C).  eapply Total_Order1.
             unfold C. auto with seq_def. apply H1. }

           pose (s0:= {|C_of:= A_chain; R_of:= R_of s;
                        Seq_cond1:= HF1; Seq_cond2:= HF2; Seq_cond3:= HF3;
                        Seq_cond4:= HF4; Seq_cond5:= HF5|}). 
           right. exists s0. split.
           (* need to prove that s0 is a sub_seq of s *)
           { unfold sub_seq. split. simpl. apply H1.
             intros. simpl in H4. auto. } split.
           (* need to prove that s0 is increasing *)
           { unfold Is_decreasing. simpl. intros m0 n0. intros.
             assert (R m0 n0  -> m0 = n0 ).
             { unfold Is_an_antichain_in in H1. intro. destruct H1. apply H6.
               unfold Included; destruct 1; tauto. simpl. tauto. }
             assert (m0<>n0).
             { apply F4. auto.  }
             assert (m0<n0 \/ m0>n0).
             { omega. } elim H7. intro. 
             assert (R m0 n0).
             { unfold R. right;tauto. } absurd (m0=n0);auto. auto. }
           (* we need to prove that size of s0 is m+1 *)
           { simpl; auto. } }  }  Qed.  
  
  
  
End Erdos.