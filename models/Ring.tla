-------------------------- MODULE Ring ---------------------------
\* This model contains the definitions for the ring structure  

(* The hierarchy of the modules are
 Ring (The basic parameters and operations for ring calculation)
   \subset LS (The leaf set utilities)
      \subset RT (The routing table utilities)
         \subset Msg (The messages definitions)
            \subset InitialStates (The initial state and TypeInvariant)
               \subset Actions (All the actions)
                  \subset MSPastry (The specification of MSPastry including properties)
                     \subset MCMSPastry (The demonstration assignments for MSPastry)
*)
EXTENDS 
   TLC,       \* To enable the pretty print
   FiniteSets,(* To understand IsFiniteSet() *)
   Integers   \* To resolve the operators, e.g. <, divid operation \div under natural numbers,etc.
CONSTANTS  
   I,    (* The route-enabled nodes in the network *)
   A,  \* the initial active nodes
   B,         \* The parameter b in the paper, typical value 4
   M,    \* The maximal allowed exponents of 2, which won't cause an overflow of natural number
   L         \* The parameter l in paper, max. length of half of the leafset
--------------------------------------------------------------

(*Assumptions*)
ASSUME IsFiniteSet(I)
ASSUME I \in SUBSET Nat
ASSUME A \in SUBSET I 
ASSUME B < M /\ M % B = 0
ASSUME L >0  
ASSUME Cardinality(A)>0
\*ASSUME Cardinality(A)> L\*L + 1 is the minimum number of nodes on the ring to keep it running
--------------------------------------------------------------
\*Definitions
Base == 2^B            \* Base of the number: 2 for binary numbers, 10 for digital and 16 for hexal number
MaxDigit == M \div B (* Maximum length of the digits for the valid I, e.g. if MaxDigit = 3, 
                          then the I with 1897 is not valid, but 189, 18, 1 are valid *)
RingCap == 2^M       \* In Pastry, nodes are connected to be a Ring, this is the capacity of the Ring

Distance(x, y) 
(*Result gives two information: positive sign represents 
  clockwise relation, value represents absolute distance*)
== LET 
       diff == (x%RingCap) - (y%RingCap)
       \*diff == x - y \* this is the case if x and y \in I
       minusmax == 0-RingCap
       half == 2^(M-1)
       halfminus == 0-half
   IN  IF diff < halfminus 
       THEN diff + RingCap
       ELSE IF diff > half THEN diff - RingCap
       ELSE diff

\*ToTheRightOf(x,y) ==  Distance(x, y)  < 0 
(* (nodeA, nodeB) returns if the shortest way from A to B is clockwise on the ring 
   The opposite nodes in the ring is always to the left*)

AbsDist(x, i) == 
(* Absolute distance between two nodes in x ring, it takes the shortest bow to calculate *)
LET hd == Distance(x, i)
IN IF hd<0 THEN 0-hd ELSE hd

\*RightDist(x, i) == 
(*The clockwise distance from i to x*)
\*IF ToTheRightOf(x, i) THEN AbsDist(x, i) ELSE RingCap - AbsDist(x, i)

CwDist(x, i) == 
(*The clockwise distance from x to i*)
IF Distance(x, i)  < 0 THEN RingCap - AbsDist(x, i) ELSE AbsDist(x, i) 

==============================================================
