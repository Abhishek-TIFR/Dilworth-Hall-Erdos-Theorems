(* This File contains the proof of Dilworth's Thm. We just combine the 
   Thms DilworthA and DilworthB from the File Finitedilworth_AB.v to prove
   the statement of Dilworth's theorem. 
   Dilworth's decomposition theorem is the central result in our formalization. 
   It states that in any poset, the maximum size of an antichain is equal to 
   the minimum number of chains in any chain cover. In other words, if c(P) 
   represents the size of a smallest chain cover of P, then width(P)=c(P). 
   
   We prove the following formal statement,

  Theorem Dilworth: forall (P: FPO U), Dilworth_statement P.

  where Dilworth_statement is defined as, 

  Definition Dilworth_statement:= fun (P: FPO U)=> forall (m n: nat), 
      (Is_width P m) -> (exists cover: Ensemble (Ensemble U), 
      (Is_a_smallest_chain_cover P cover) /\ (cardinal _ cover n)) -> m=n.

 *)

Require Export PigeonHole.
Require Export BasicFacts.
Require Import FiniteDilworth_AB.



Section Dilworth.
 
  
  Variable U: Type.



Inductive Is_width (P: FPO U) (n: nat) :Prop :=
     W_cond: (exists la: Ensemble U, Is_largest_antichain_in P la /\ cardinal _ la n) -> (Is_width P n).


 Definition Dilworth_statement:=  fun (P: FPO U)=>
     forall (m n: nat), (Is_width P m) ->
    (exists cover: Ensemble (Ensemble U), (Is_a_smallest_chain_cover P cover)/\ (cardinal _ cover n)) ->
    m=n.


 
   Theorem Dilworth: forall (P: FPO U), Dilworth_statement P.

   Proof. { intro P. unfold Dilworth_statement. intros m n. intros.
            destruct H. destruct H as [la H]. destruct H0 as [cover H0].
            
            (* We prove that there is a chain cover of size m using DilworthB *)
            assert (H1:  (exists (cv: Ensemble (Ensemble U)), Is_a_chain_cover P cv /\
                                                      cardinal _ cv m)).
            { apply (DilworthB _ P ).  exists la.  auto. }
            (* Hence n<= m, since n is the size of smallest chain cover *)
            assert (H2: n<= m ).
            { destruct H1 as [cv H1].
             destruct H0 as [H_cover H0].
             destruct H_cover . 
             apply H3 with ( cover0:= cv) ( sn:= n) (n:= m). tauto.
            }
            (* We prove n>=m or ~ (n<m) using DilworthA *)
             assert (H3: n>= m).
              { apply nat_P1. apply ( DilworthA _ P) with (cv:= cover) (a:= la).
                apply H0.  apply H. tauto.  tauto. } 
           (* Hemce combining H2 and H3 we have m=n  *)
           auto with arith.  }
  Qed.
            
 
 
  
End Dilworth.


