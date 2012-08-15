-------------------------- MODULE LS --------------------------
\* This module extends the data structure with
\* two different implementations of the leaf set. 
\* One is restricted using only sets. 
\* and the other uses Sequence.
\* The reason of using sequence is to provide more readable and 
\* efficient implementation for TLC model checker.

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
EXTENDS Ring,
        Sequences \* For the second approach using sequence
--------------------------------------------------------------
\* Implementation of LSet using set

LSet == {ls \in [node: I, left: SUBSET I, right: SUBSET I]: 
         ls.node \notin ls.left /\ ls.node \notin ls.right
       /\ Cardinality(ls.left) =< L /\ Cardinality(ls.right) =< L}

GetLSetContent(ls) == ls.left \cup ls.right \cup {ls.node}
RemoveFromLSet(delta, ls) ==  
\* By removing nodes from leaf set, there are two ways:
\* 1. Remove them from overall leaf set nodes and rearrange the leafset's left and right
\* 2. simply remove them from left and right set.
\* For the first case, a leaf set will be always complete if there are more than L ready 
\* nodes in the network, which obviously contradict with the algorithm 
\* Hence, we must choose the second one.
   [node |-> ls.node, 
    left |-> ls.left \ delta, 
   right |-> ls.right \ delta]

AddToLSet(delta, set) == \*(SUBSET I, LSet, I), 
\* we ``update'' the leaf set (set) of
\* some node (i) with a set (delta) of new nodes. 
  LET 
    i == set.node
    left == ((set.left) \cup delta) \ {i}
    right == ((set.right) \cup delta) \ {i}
    newleft == 
      IF Cardinality(left) =< L 
      THEN left
      ELSE CHOOSE subsetleft \in SUBSET left:
               /\ Cardinality(subsetleft) = L
               /\ \A out \in (left \ subsetleft), in \in subsetleft:
                  /\ CwDist(in,i) < CwDist(out,i)
    newright == 
      IF Cardinality(right) =< L 
      THEN right
      ELSE CHOOSE subsetright \in SUBSET right:
               /\ Cardinality(subsetright) = L
               /\ \A out \in (right \ subsetright), in \in subsetright:
                  /\ CwDist(i,in) < CwDist(i,out)
  IN [node |-> i, left |-> newleft, right |-> newright]
LeftMost(ls)==(*(lset, I), find the leftmost node in lset wrt. I*)
    IF ls.left = {} 
    THEN ls.node
    ELSE CHOOSE n \in ls.left: \A m \in ls.left: Distance(m, n) < 0 \/ n = m

RightMost(ls)==(*(lset, I), find the rightmost node in lset wrt. I*)
    IF  ls.right = {} 
    THEN ls.node
    ELSE CHOOSE n \in  ls.right: \A m \in  ls.right: Distance(n, m) < 0 \/ n = m
LeftNeighbor(ls) == IF ls.left = {}
                       THEN ls.node
                       ELSE CHOOSE n \in ls.left: \A p\in ls.left: CwDist(p,ls.node)>=CwDist(n,ls.node)
RightNeighbor(ls) == IF ls.right = {}
                        THEN ls.node
                        ELSE CHOOSE n \in ls.right: \A p\in ls.right: CwDist(ls.node, p)>=CwDist(ls.node, n)

IsComplete(ls)==(*(lset, I), if the leafset lset of the I has enough 
                    nodes in left and right parts*)
  /\Cardinality(ls.left) = L 
  /\Cardinality(ls.right) = L
  
\* we don't need this now, because initially there is only one active node
InitLS(i) == AddToLSet(A, [node |-> i, left|-> {}, right|-> {}]) 


EmptyLS(i) == [node |-> i, left|-> {}, right|-> {}]
Overlaps(ls) == ls.left \cap ls.right # {} \* Overlap happens
Lenth(s)== Cardinality(s) 


-------------------------------------------------------------------------------------------

\* Implementation of LSet using Sequence


(*
InSeq(e, s)== \E i \in 1..Len(s): s[i] = e
\* Test if we can find element e in sequence s

SeqToSet(s) == {s[i]: i \in 1..Len(s)} 
\* given sequencce s, return the nodes it contains as set


LSet == {ls \in [node: I, left: Seq(I), right: Seq(I)]:
\*a leaf set (LSet) consists of node, left, right. 
       /\ ~InSeq(ls.node, ls.left) /\ ~InSeq(ls.node, ls.right)
\*the left and right sequence does not contain the node itself 
       /\ Len(ls.right) =< L /\ Len(ls.right) =< L}
\*the size of leafset is less than L

GetLSetContent(ls) == (SeqToSet(ls.left)\cup SeqToSet(ls.right)) \cup {ls.node} 

RemoveFromSeq(s, delta) == LET Test(k) == k \notin delta IN SelectSeq(s, Test)
\* Remove a set (delta) of elements from sequence s



RemoveFromLSet(delta, ls) ==   
\* By removing nodes from leaf set, there are two ways:
\* 1. Remove them from overall leaf set nodes and rearrange the leafset's left and right
\* 2. simply remove them from left and right set.
\* For the first case, a leaf set will be always complete if there are more than L ready 
\* nodes in the network, which obviously contradict with the algorithm 
\* Hence, we must choose the second one.
[node |-> ls.node, 
    left |-> RemoveFromSeq(ls.left, delta), 
   right |-> RemoveFromSeq(ls.right, delta)]

SortSet(set, LEQ(_, _)) ==
\* sort the set s and generate a sequence 
\* w.r.t. the partial order LEQ
\* here we implements the insert sort algorithm 
 LET SetToSeq[S \in SUBSET set] ==
      IF S = {} THEN <<>>
                 ELSE LET s == CHOOSE s \in S: TRUE
                      IN Append(SetToSeq[S\{s}], s) 
 IN SortSeq(SetToSeq[set], LEQ)  

AddToLSet(delta, ls) == 
\*(SUBSET I, LSet, I), 
\* we ``update'' the leaf set (ls) of
\* particular node (i) with a set (delta) of new nodes. 
LET i == ls.node
    d == delta \ {i}
    LEFT(x, y) == CwDist(x, i) =< CwDist(y, i)
    RIGHT(x, y) == CwDist(i, x) =< CwDist(i, y)
    lcan == SortSet(SeqToSet(ls.left) \cup d, LEFT)
    rcan == SortSet(SeqToSet(ls.right) \cup d, RIGHT)
IN IF d = {} 
   THEN ls
   ELSE  
    [node |-> ls.node,
     left |-> IF Len(lcan)>L THEN SubSeq(lcan, 1, L) ELSE lcan, 
     right |-> IF Len(rcan)>L THEN SubSeq(rcan, 1, L) ELSE rcan]

LeftMost(ls)==(*(lset, I), find the leftmost node in lset wrt. I*)
    LET n == Len(ls.left)
    IN IF n = 0 THEN ls.node ELSE ls.left[n]

RightMost(ls)==(*(lset, I), find the rightmost node in lset wrt. I*)
    LET n == Len(ls.right)
    IN IF n = 0 THEN ls.node ELSE ls.right[n]
    
LeftNeighbor(ls) == IF ls.left = <<>> THEN ls.node ELSE (ls.left)[1]
\* the closest node to the left of ls.node in ls
    
RightNeighbor(ls) ==IF ls.right = <<>> THEN ls.node ELSE (ls.right)[1]
\* the closest mode to the right of ls.node in ls 
IsComplete(ls)==(*(lset, I), if the leafset lset of the I has enough 
                   nodes in left and right parts*)
  /\Len(ls.left) = L
  /\Len(ls.right) = L

\* we don't need this now, because initially there is only one active node
InitLS(i) == AddToLSet({A}, [node |-> i, left|-> <<>>, right|-> <<>>])

EmptyLS(i) == [node |-> i, left|-> <<>>, right|-> <<>>]
Overlaps(ls) == SeqToSet(ls.left) \cap SeqToSet(ls.right) # {}
Lenth(s) == Len(s)
*)
----------------------------------------------------------
\* shared definitions
LeftCover(ls) == 
\*(LSet,I), find the left bound of the node i's coveraged (key ownerschip)
\* exclusive the edge node
    IF LeftNeighbor(ls) = ls.node
    THEN ls.node
    ELSE (ls.node + CwDist(LeftNeighbor(ls), ls.node) \div 2) % RingCap 
RightCover(ls) ==
\*(LSet, I), find the right bound of the node i's coveraged (key ownerschip)
\* inclusive the edge node
    IF RightNeighbor(ls) = ls.node
    THEN ls.node + 1
    ELSE (RightNeighbor(ls) + CwDist(ls.node, RightNeighbor(ls)) \div 2 +1) % RingCap
Covers(ls, k) == CwDist(LeftCover(ls), k) 
                 =< CwDist(LeftCover(ls), RightCover(ls))
              
==============================================================
