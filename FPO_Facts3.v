Require Export Combi_1.
Require Export BasicFacts2.



Section More_on_FPO.
  Variable U: Type.
  Variable FP: FPO U.
  Let C:= Carrier_of _ FP.
  Let R:= Rel_of _ FP. 

  Set Implicit Arguments.

  Inductive Is_a_smallest_antichain_cover (P: FPO U) (scover: Ensemble (Ensemble U)): Prop:=
    smallest_cover_cond_AC: (Is_an_antichain_cover P scover) ->  
                        ( forall (cover: Ensemble (Ensemble U))(sn n: nat),
                           (Is_an_antichain_cover P cover /\ cardinal _ scover sn /\
                           cardinal _ cover n) -> (sn <=n) ) ->
                        Is_a_smallest_antichain_cover P scover.

 Inductive Is_height (P: FPO U) (n: nat) : Prop:=
   H_cond: (exists lc: Ensemble U, Is_largest_chain_in  P lc /\ cardinal _ lc n) -> (Is_height P n).
 


 Lemma Chain_sub: forall (P: FPO U)(e1 e2: Ensemble U), Is_a_chain_in P e2 -> (Included _ e1 e2)->
                                                   Inhabited _ e1-> Is_a_chain_in P e1.
 Proof. { intros. unfold Is_a_chain_in. split. split.
         cut (Included _ e2 (Carrier_of _ P)).  auto with sets. apply H. auto.
         intros. cut (Included _ (Couple _ x y) e2). intro. apply H;auto with sets.
         auto with sets. } Qed. 
 
 Lemma Antichain_sub:  forall (P: FPO U)(e1 e2: Ensemble U),
       Is_an_antichain_in P e2 -> (Included _ e1 e2)-> Inhabited _ e1-> Is_an_antichain_in P e1. 
 Proof.  { intros. unfold Is_an_antichain_in. split. split.
         cut (Included _ e2 (Carrier_of _ P)).  auto with sets. apply H. auto.
         intros. cut (Included _ (Couple _ x y) e2). intro. apply H;auto with sets.
         auto with sets. } Qed.  

                                

 
End More_on_FPO. 