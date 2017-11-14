# Dilworth-Hall-Erdos-Theorems
The Formalisation of Dilworth's, Hall's and the Erdos-Szekeres theorems in Coq Proof Assistant 

This work is done in the Coq Proof General (Version 4.4pre). We have used the Company-Coq extension [#Company-Coq] 
for the Proof General. The proofs are split into the following files: 


1. PigeonHole.v: It contains some variants of the Pigeonhole Principle.

2. BasicFacts.v: Contains some useful properties on numbers and sets. It also contains strong induction and some variants of Choice theorem. 

3. FPO_Facts.v: Most of the definitions and some results on finite partial orders are proved in this file. 

4. FPO_Facts2.v: Contains most of the lemmas that we discussed in this section. 

5. FiniteDilworth_AB.v: Contains the proofs of forward and backward directions of Dilworth's theorem.

6. FiniteDilworth.v: Contains the proof of the main statement of Dilworth's theorem. 

7. Combi_1.v: Some new tactics are defined to automate the proofs of some trivial facts on numbers, logic, sets and finite partial orders. 

8. BasicFacts2.v: Contains some facts about power-sets.

9. FPO_Facts3.v: Contains some more lemmas on finite posets. 

10. Dual_Dilworth.v: Contains the proof of the Dual-Dilworth Theorem. 

11. Graph.v: Contains definitions of different types of graphs.

12. Halls_Thm.v: Contains the proof of Hall's theorem on bipartite graph. 

13. Marriage_Thm.v: Contains the proof of Hall's theorem on collection of finite sets (SDR).

14. Erdos_Szeker.v: Contains the proof of the Erdős-Szekeres theorem on sequences.

 All these files can be safely compiled in the above given order. 
