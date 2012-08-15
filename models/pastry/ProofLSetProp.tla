--------------------------- MODULE ProofLSetProp ---------------------------
(* The hierarchy of the Proofs are
ProofBasic
  \subset ProofRingProp (The basic parameters and operations for ring calculation)
   \subset ProofLSetProp (The leaf set local properties of data structure)
    \subset ProofType (The Proof of TypeInvariant)
     \subset ProofLSetInv (The proof of Invariant of Leaf Set properties)
      \subset ProofProp (The reduction proof from Correctness properties
                         of Pastry to a list of Leaf Set properties)
*)
EXTENDS ProofRingProp

\* Sequence relevant axioms
AXIOM NonEmptySeq == \A S: \A s \in Seq(S): s # <<>> <=> Len(s) >=1
\*LEMMA AbigerThan1 == Cardinality(A)> 1
LEMMA LSetInvProp == \A ls \in LSet: ~ls.node \in (ls.left) 
                                       /\ ~ls.node \in (ls.right)
BY DEF LSet
\*LSet Theorems
THEOREM LeftNeighborType == \A ls \in LSet: LeftNeighbor(ls) \in I
(*
LeftNeighbor(ls) == IF ls.left = {}
                       THEN ls.node
                       ELSE CHOOSE n \in ls.left: \A p\in ls.left: CwDist(p,ls.node)>=CwDist(n,ls.node)
*)
<1>1. SUFFICES ASSUME NEW ls \in LSet
      PROVE LeftNeighbor(ls) \in I
      OBVIOUS
<1>2. CASE ls.left = {} 
      BY <1>2 DEF LeftNeighbor, LSet
<1>5. CASE ls.left # {}
   <2>1. \E n \in ls.left: \A p\in ls.left: CwDist(p,ls.node)>=CwDist(n,ls.node)
      BY CwMaximal, <1>5 DEF LSet
   <2>9. QED BY <2>1 DEF LeftNeighbor, LSet
<1>9. QED BY <1>2,<1>5
(*
<1>6. TAKE ls \in LSet
<1>7. CASE ls.left = <<>>
   <2>1. ls.node \in I
      BY DEF LSet
   <2>9. QED BY <1>7, <2>1 DEF LeftNeighbor
<1>8. CASE ls.left # <<>>
   <2>. ls.left \in Seq(I)
     BY  <1>6   DEF LSet
   <2>. Len(ls.left) \in Nat
     BY LenInNat
   <2>1. Len(ls.left)>=1
     BY <1>8, EmptySeq, NatZeroOrGeq1
   <2>2. (ls.left)[1] \in I
      BY <1>8, <2>1, ElementOfSeq
   <2>9. QED BY <1>8, <2>2 DEF LeftNeighbor
<1>9. QED BY <1>7,<1>8 
*)
THEOREM RightNeighborType == \A ls \in LSet: RightNeighbor(ls) \in I
OMITTED \* similar to LeftNeighborType
(*
<1>6. TAKE ls \in LSet
<1>7. CASE ls.right = <<>>
   <2>1. ls.node \in I
      BY DEF LSet
   <2>9. QED BY <1>7, <2>1 DEF RightNeighbor
<1>8. CASE ls.right # <<>>
   <2>. ls.right \in Seq(I)
      BY  <1>6   DEF LSet
   <2>. Len(ls.right) \in Nat
     BY LenInNat
   <2>1. Len(ls.right)>=1
     BY <1>8, EmptySeq, NatZeroOrGeq1
   <2>2. (ls.right)[1] \in I
      BY <1>8, <2>1, ElementOfSeq
   <2>9. QED BY <1>8, <2>2 DEF RightNeighbor
<1>9. QED BY <1>7,<1>8
*)
THEOREM RightCoverType == \A ls \in LSet: RightCover(ls) \in Nat
THEOREM LeftCoverType == \A ls \in LSet: LeftCover(ls) \in Nat
\* needs \div and % types.
THEOREM LeftMostType == \A ls \in LSet: LeftMost(ls) \in I
<1>1. SUFFICES ASSUME NEW ls \in LSet
      PROVE LeftMost(ls) \in I
      OBVIOUS
<1>2. CASE ls.left = {} 
      BY <1>2 DEF LeftMost, LSet
<1>5. CASE ls.left # {}
   <2>1. \E n \in ls.left: \A m \in ls.left: Distance(m, n) < 0 \/ n = m
      BY DistMinimal, <1>5 DEF LSet
   <2>9. QED BY <2>1 DEF LeftMost, LSet
<1>9. QED BY <1>2,<1>5
(*
<1>6. TAKE ls \in LSet
<1>7. CASE ls.left = <<>> 
   <2>1. ls.node \in I
      BY DEF LSet
   <2>9. QED BY <1>7, <2>1 DEF LeftMost
<1>8. CASE ls.left # <<>>
   <2>. ls.left \in Seq(I)
      BY  <1>6   DEF LSet
   <2>. Len(ls.left) \in Nat
      BY LenInNat
   <2>1. Len(ls.left)>=1
      BY <1>8, EmptySeq, NatZeroOrGeq1
   (** The following two steps should be unnecessary ... **)
   <2>1a. Len(ls.left) <= Len(ls.left)
      OBVIOUS 
   <2>1b. Len(ls.left) \in Int
      OBVIOUS
   <2>2. Len(ls.left) \in 1..Len(ls.left)
      BY <1>8, <2>1, <2>1a, <2>1b, DotDotDef
   <2>3. (ls.left)[Len(ls.left)] \in I
      BY <1>8, <2>1, <2>2, ElementOfSeq
   <2>9. QED BY <1>8, <2>3 DEF LeftMost
<1>9. QED BY <1>7,<1>8 
*)
THEOREM RightMostType == \A ls \in LSet: RightMost(ls) \in I
\* similar to LeftMostType
PROOF OMITTED
THEOREM EmptyLST == \A i \in I: EmptyLS(i) \in LSet /\ EmptyLS(i).node = i
<1>1. SUFFICES ASSUME NEW i \in I
   PROVE EmptyLS(i) \in LSet /\ EmptyLS(i).node = i
   OBVIOUS
<1>4. /\ EmptyLS(i).node = i
      /\ EmptyLS(i).left = {}
      /\ EmptyLS(i).right = {}
   BY DEF EmptyLS
<1>7. Cardinality({}) =< L
      BY EmptySetSize, Lmin, Unequality2
<1>8. EmptyLS(i) \in LSet
      BY <1>4, <1>7 DEF EmptyLS, LSet
<1>9. QED BY <1>4, <1>8
(*
<1>1. TAKE u \in I 
<1>2. [node |-> u, left|-> <<>>, right|-> <<>>] \in LSet
   <3>1. [node |-> u, left|-> <<>>, right|-> <<>>] 
         \in [node: I, left: Seq(I), right: Seq(I)]
      <4>1. u \in I
      BY <1>1
      <4>2. <<>> \in Seq(I)
      BY EmptySeq
      <4>9. QED BY <4>1, <4>2
   <3>2. ~InSeq(u, <<>>)
      BY ExklusionSequence
   <3>3. Len(<<>>) = 0
      BY LenEmpty
   <3>9. QED BY <1>1, <3>1, <3>2, <3>3, Lmin DEF LSet
<1>3. QED BY <1>2 DEF EmptyLS
*)
THEOREM SelectSeqType == 
        ASSUME NEW s, NEW S, NEW Test(_),
               s \in Seq(S)
        PROVE  SelectSeq(s, Test) \in Seq(S)
PROOF OMITTED
\* prover cannot handle higher order expression
\*THEOREM RemoveFromSeqType == \A s \in Seq(I), delta \in SUBSET I: 
\*                              RemoveFromSeq(s, delta) \in Seq(I)
\*PROOF OMITTED (*BY SelectSeqType DEF RemoveFromSeq*)
\* prover cannot handle higher order expression
THEOREM RemoveFromLSetType == \A s \in SUBSET I, ls \in LSet: RemoveFromLSet(s, ls) \in LSet
PROOF OMITTED
\* prover cannot handle higher order expression
THEOREM RemoveFromLSetNoChangeNode == 
    \A s \in SUBSET I, ls \in LSet:
         RemoveFromLSet(s, ls).node = ls.node
\*BY DEF RemoveFromLSet
\* prover cannot handle higher order expression
THEOREM AddToLSetType == \A s \in SUBSET I, ls \in LSet: AddToLSet(s, ls) \in LSet
PROOF OMITTED
\* prover cannot handle higher order expression
(**
THEOREM AddToLSetNoChangeNode == \A s \in SUBSET I, ls1,ls2 \in LSet:
         ls2 =  AddToLSet(s, ls1) => ls2.node = ls1.node
**)
THEOREM AddToLSetNoChangeNode ==
  \A s \in SUBSET I, ls \in LSet : AddToLSet(s, ls).node = ls.node
\*BY DEF AddToLSet
\* prover cannot handle higher order expression
THEOREM GetLSetContentType == \A ls \in LSet:  GetLSetContent(ls) \in SUBSET I
BY DEF GetLSetContent, LSet
(*
<1>100 TAKE ls \in LSet
<1>1. SeqToSet(ls.left) \in SUBSET I
   <2>1. ls.left \in Seq(I)
      BY DEF LSet
   <2>2. QED BY <1>1, <2>1, SeqToSetType
<1>2. SeqToSet(ls.right) \in SUBSET I
   <2>1. ls.right \in Seq(I)
      BY DEF LSet
   <2>2. QED BY <1>2, <2>1, SeqToSetType
<1>3. ls.node \in I
   BY DEF LSet
<1>9. QED BY <1>1, <1>2, <1>3 DEF GetLSetContent
*)
LEMMA EmptyAddEmtpy == \A a \in SUBSET I, k \in I: a = {k} => AddToLSet(a, EmptyLS(k)) = EmptyLS(k)
LEMMA NotAddSelf == \A a \in SUBSET I, ls \in LSet: 
       /\ ~ls.node \in (AddToLSet(a, ls).left) 
       /\ ~ls.node \in (AddToLSet(a, ls).right)
LEMMA AddNodeNotChange == \A a \in SUBSET I, ls \in LSet:
       /\ AddToLSet(a, ls).node = ls.node 
LEMMA EmptyLSIsEmpty == \A i \in I: 
         /\ (EmptyLS(i).left) = {} 
         /\ (EmptyLS(i).right) = {} 
         /\ GetLSetContent(EmptyLS(i)) = {i}
LEMMA EmptyLSIsEmptyCo == \A ls \in LSet: 
         /\ Lenth(ls.left) = 0
         /\ Lenth(ls.right) = 0
       => GetLSetContent(ls) = {ls.node}
LEMMA EmptyLSNoSelf == \A i \in I: ~i \in (EmptyLS(i).left) 
                                    /\ ~i \in (EmptyLS(i).right) 
LEMMA EmptySeqEmptySet == \A s \in Seq(I): s = <<>> <=> (s) = {} 
LEMMA EmptyLSetRange == \A i, k \in I:
            \/ k \in GetLSetContent(EmptyLS(i))
            \/ /\ CwDist(i, k) > CwDist(i, RightMost(EmptyLS(i))) 
               /\ CwDist(k, i) > CwDist(LeftMost(EmptyLS(i)), i)  
\* case i = k : the first 
\* case i#k: most node of emptyLS is itself, hence the right part is 0 and k#i, left part is >0
LEMMA AddMoreHasNeighbor == \A ls, s \in LSet, a \in SUBSET I:
      /\ls = AddToLSet(a, s)
      /\Cardinality(a) > 1
              =>
          /\RightNeighbor(ls) # ls.node 
          /\ LeftNeighbor(ls) # ls.node
LEMMA CompleteHasNeighbor == \A ls \in LSet: IsComplete(ls)
              =>
          /\RightNeighbor(ls) # ls.node 
          /\ LeftNeighbor(ls) # ls.node
          
          
LEMMA CompleteNotEmpty == \A ls \in LSet: IsComplete(ls) => ls.left # <<>> /\ ls.right # <<>>
LEMMA SeqLength == \A s \in Seq(I): s # <<>> <=> Len(s) >0  
LEMMA FirstEleNotI == \A i \in I,s \in Seq(I): ~i \in (s) /\ s # <<>> <=> s[1] # i
LEMMA AddToLSetComplete == \A ls \in LSet, a \in SUBSET I : 
          IsComplete(ls) \/ Cardinality(a)>L => IsComplete(AddToLSet(a, ls))
LEMMA AddToLSetNotEmpty == \A ls \in LSet, a \in SUBSET I:
          /\RightNeighbor(ls) # ls.node 
          /\ LeftNeighbor(ls) # ls.node
          => /\ RightNeighbor(AddToLSet(a, ls) ) # ls.node 
             /\ LeftNeighbor(AddToLSet(a, ls)) # ls.node
LEMMA AddToLSetNotEmptyRight == \A ls \in LSet, a \in SUBSET I:
          RightNeighbor(ls) # ls.node 
          => RightNeighbor(AddToLSet(a, ls) ) # ls.node
LEMMA  AddToLSetNotEmptyLeft == \A ls \in LSet, a \in SUBSET I:
          LeftNeighbor(ls) # ls.node
          => LeftNeighbor(AddToLSet(a, ls)) # ls.node
LEMMA AddToLSetNotEmptyCo ==  \A ls \in LSet, a \in SUBSET I:
          /\RightNeighbor(ls) = ls.node 
          /\ LeftNeighbor(ls) = ls.node
          => \/ /\ RightNeighbor(AddToLSet(a, ls) ) # ls.node 
                /\ LeftNeighbor(AddToLSet(a, ls)) # ls.node
             \/ /\RightNeighbor(AddToLSet(a, ls)) = ls.node 
                /\ LeftNeighbor(AddToLSet(a, ls)) = ls.node
             \* This is the case when we add the node to itself.
LEMMA AddToLSetNotEmptyCo1 ==  \A ls \in LSet, j \in I:
          j # ls.node
          => /\ RightNeighbor(AddToLSet({j}, ls) ) # ls.node 
             /\ LeftNeighbor(AddToLSet({j}, ls)) # ls.node
LEMMA AddToLSetInv == \A s, ls \in LSet, d \in SUBSET I: 
          ls = AddToLSet(d, s) 
              =>
             /\ \A m \in (s.left) \cup d: 
                 CwDist(LeftNeighbor(ls), ls.node)=< CwDist(m, ls.node)
             /\ \A n \in (s.right) \cup d: 
                 CwDist(ls.node, RightNeighbor(ls)) =< CwDist(ls.node, n)
LEMMA AddToLSetRange == \A ls \in LSet, k \in I, a \in SUBSET I:
                        \/ k \in GetLSetContent(ls)
                        \/ /\ CwDist(ls.node, k) > CwDist(ls.node, RightMost(ls)) 
                           /\ CwDist(k, ls.node) > CwDist(LeftMost(ls), ls.node)  
        => \/ k \in GetLSetContent(AddToLSet(a, ls))
           \/ /\ CwDist(ls.node, k) > CwDist(ls.node, RightMost(AddToLSet(a, ls))) 
              /\ CwDist(k, ls.node) > CwDist(LeftMost(AddToLSet(a, ls)), ls.node)  

LEMMA NeigborsInLset == \A ls \in LSet: LeftNeighbor(ls) \in (ls.left) 
                              /\ RightNeighbor(ls) \in (ls.right)
LEMMA NeighborSemmantic == \A s \in LSet:
       \A i \in (GetLSetContent(s)\{s.node}): 
        /\ CwDist(LeftNeighbor(s), s.node) =< CwDist(i, s.node) 
        /\ CwDist(s.node, RightNeighbor(s)) =< CwDist(s.node, i)
LEMMA NeighborMost == \A s \in LSet:
     /\CwDist(LeftNeighbor(s), s.node) =< CwDist(LeftMost(s), s.node) 
     /\CwDist(s.node, RightNeighbor(s)) =< CwDist(s.node, RightMost(s))  
      
LEMMA AddToLSetInvCo == \A s, ls \in LSet, d \in SUBSET I: 
          ls = AddToLSet(d, s) 
              =>
             /\ CwDist(LeftNeighbor(ls), ls.node)=< CwDist(LeftNeighbor(s), s.node)
             /\ CwDist(ls.node, RightNeighbor(ls)) =< CwDist(s.node, RightNeighbor(s))
BY AddToLSetInv, NeigborsInLset
LEMMA RemoveNodeNotChange == \A a \in SUBSET I, ls \in LSet:
       /\ RemoveFromLSet(a, ls).node = ls.node  
BY DEF RemoveFromLSet         
LEMMA RemoveNotAddSelf == \A a \in SUBSET I, ls \in LSet: 
       /\ ~ls.node \in (RemoveFromLSet(a, ls).left) 
       /\ ~ls.node \in (RemoveFromLSet(a, ls).right)   
BY RemoveFromLSetType, RemoveNodeNotChange, LSetInvProp

LEMMA RemoveMonotony == \A a \in SUBSET I, ls \in LSet:
      GetLSetContent(RemoveFromLSet(a, ls)) \in SUBSET GetLSetContent(ls)
LEMMA \A ls \in LSet : \A i \in 1 .. Len(ls.left) : ls.node # ls.left[i]
BY DEFS LSet

LEMMA \A ls \in LSet : \A i \in 1 .. Len(ls.right) : ls.node # ls.right[i]
BY DEFS LSet
(*
LEMMA LSetInvPropCo == \A ls \in LSet: ls.left # <<>> /\ ls.right # <<>>
                    => 
                    /\ ls.left[1] # ls.node
                    /\ ls.right[1] # ls.node
<1>1. SUFFICES ASSUME
      NEW ls,
      ls \in LSet,
      ls.left # <<>>,
      ls.right # <<>>
      PROVE 
        /\ ls.left[1] # ls.node
        /\ ls.right[1] # ls.node
   OBVIOUS
<1>3. Len(ls.left)>= 1 /\ Len(ls.right) >= 1
   BY <1>1, NonEmptySeq DEF LSet  
<1>9. QED BY <1>1, <1>3 DEF LSet
\* don't know why I can't prove it.
*)
LEMMA OverlapNotEmpty == \A ls \in LSet: Overlaps(ls) => 
            /\ RightNeighbor(ls) # ls.node 
            /\ LeftNeighbor(ls) # ls.node

<1>1. SUFFICES ASSUME NEW ls,
      ls \in LSet, 
      Overlaps(ls)
      PROVE 
            /\ RightNeighbor(ls) # ls.node 
            /\ LeftNeighbor(ls) # ls.node
   OBVIOUS
<1>2. (ls.left) # {} /\ (ls.right) # {}
   BY <1>1 DEF Overlaps
<1>3. ~ls.node \in ls.left /\ ~ls.node \in ls.right
<1>9. QED BY <1>2, <1>3 DEF RightNeighbor, LeftNeighbor
(* The following is for sequence version of Leaf set
<1>3. LeftNeighbor(ls) = ls.left[1]
   BY <1>2 DEF LeftNeighbor
<1>4. RightNeighbor(ls) = ls.right[1]
   BY  <1>2 DEF RightNeighbor
<1>6. ls.left[1] # ls.node /\ ls.right[1] # ls.node
   BY <1>1, <1>2, LSetInvPropCo
<1>9. QED BY <1>3, <1>4, <1>6
*)
LEMMA NonEmptyLSet == \A i \in I, ls \in LSet: 
      /\ i \in GetLSetContent(ls)
      /\ i # ls.node
      => LeftNeighbor(ls) # ls.node
         /\ RightNeighbor(ls) # ls.node
LEMMA EmptyLSNoNeighbor == \A ls \in LSet: 
         /\ LeftNeighbor(ls) = ls.node
         /\ RightNeighbor(ls) = ls.node
       <=> ls = EmptyLS(ls.node)
LEMMA AddSingleNodeToEmpty == 
      \A i, j \in I: 
      \* here i and j could be the same node
            /\ LeftNeighbor(AddToLSet({j}, EmptyLS(i) )) = j 
            /\ RightNeighbor(AddToLSet({j}, EmptyLS(i) )) = j
            /\ GetLSetContent(AddToLSet({j}, EmptyLS(i) )) = {i, j}
LEMMA LeftMostInLS == 
      \A ls \in LSet: LeftMost(ls) \in GetLSetContent(ls) 
LEMMA RightMostInLS ==  
      \A ls \in LSet: RightMost(ls) \in GetLSetContent(ls) 
LEMMA EmptyLSNoMost == \A ls \in LSet:
      /\ (Lenth(ls.left) = 0 <=> LeftMost(ls) = ls.node)
      /\ (Lenth(ls.right) = 0 <=> RightMost(ls) = ls.node)
=============================================================================
\* Modification History
\* Last modified Wed Nov 30 16:05:29 CET 2011 by tianlu
\* Created Mon Dec 13 12:09:01 CET 2010 by tianlu
