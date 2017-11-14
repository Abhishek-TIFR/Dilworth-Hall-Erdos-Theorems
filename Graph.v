
(* This file contains definitions of different types of graphs.*)

Require Export Ensembles.
Require Export Relations_1.
Require Export Finite_sets.


Section Graph.

  

  Variable U: Type.

  Set Implicit Arguments. 

  Record Graph : Type := Def_of_Graph
                        { Vertices_of : Ensemble U;
                          Edge_Rel_of: Relation U;
                          NonEmpty_cond: Inhabited U Vertices_of }.

  Record Finite_Graph : Type := Def_of_FiniteGraph {
                           Graph_of_FG :> Graph ;
                           F_Graph_cond: Finite U ( Vertices_of Graph_of_FG ) }.

  Record U_Graph: Type:= Def_of_UGraph
                           { Graph_of_UG :> Graph;
                             UG_Rel_Sym: Symmetric _ (Edge_Rel_of Graph_of_UG ) }.

  Record FU_Graph: Type:= Def_of_Finite_UGraph {
                           Graph_of_FUG :> Finite_Graph ;
                           FUG_Rel_Sym: Symmetric _ (Edge_Rel_of Graph_of_FUG ) }.


   Record Biper_Graph: Type :=
    Def_of_BG {
    Graph_of_BG:> Finite_Graph ;
    L_of: Ensemble U;
    R_of: Ensemble U;
    LR_Inhabited: Inhabited _ L_of /\ Inhabited _ R_of;
    LR_Disj: Disjoint _ L_of R_of;
    LR_Union: Vertices_of (Graph_of_BG ) = (Union _ L_of R_of);
    LR_Rel: forall x y: U, (Edge_Rel_of (Graph_of_BG ))  x y  -> (In _ L_of x /\ In _ R_of y)  }.

  Unset Implicit Arguments. 
  
                                 
  
  
End Graph.


