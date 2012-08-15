----------------------------- MODULE ProofProp -----------------------------
(* The hierarchy of the Proofs are
 ProofRingProp (The basic parameters and operations for ring calculation)
   \subset ProofLSetProp (The leaf set local properties of data structure)
    \subset ProofType (The Proof of TypeInvariant)
     \subset ProofLSetInv (The proof of Invariant of Leaf Set properties)
      \subset ProofProp (The reduction proof from Correctness properties
                         of Pastry to a list of Leaf Set properties)
*)
EXTENDS ProofType  
\* Properties of LSet 
THEOREM StatusDuality == \A i \in I: status[i] = "ready" => ~(status[i] = "dead")
OBVIOUS
THEOREM Neighborhood == \* no other node could be closer to a node than its neighbor  
TypeInvariant /\ Invariant=> 
  \A x, y \in I: 
     /\ status[x] = "ready"
     /\ status[y] = "ready"
     /\ ~(x = y)
     => 
        /\ ~(CwDist(y, x) < CwDist(LeftNeighbor(lset[x]), x))
        /\ ~(CwDist(x, y) < CwDist(x, RightNeighbor(lset[x])))
<1>1. SUFFICES ASSUME NEW x \in I,
        NEW y \in I,
        status[x] = "ready",
        status[y] = "ready",
        ~(x = y),
        TypeInvariant,
        NeighborClosest
   PROVE /\ ~(CwDist(y, x) < CwDist(LeftNeighbor(lset[x]), x))
         /\ ~(CwDist(x, y) < CwDist(x, RightNeighbor(lset[x])))
   BY DEF Invariant

<1>2.  x \in NodesReady /\ y \in NodesReady /\ ~(x = y)
   BY <1>1 DEF NodesReady

<1>4. ~Cardinality(NodesReady) =< 1
   BY <1>2, CardinalityTwoNode, ReadyInI
<1>5. /\ CwDist(LeftNeighbor(lset[x]), x) =< CwDist(y, x) 
      /\ CwDist(x, RightNeighbor(lset[x])) =< CwDist(x, y)
   BY <1>1, <1>2, <1>4 DEF NeighborClosest 
<1>9. QED BY <1>5, Unequality2, CwDistType, IisNat,  
   LeftNeighborType, RightNeighborType, TypeInvariant DEF TypeInvariant
\* proof sketch: either the right neighbor of x is the left neighbor of y,
\* or the two neighbors are different, but neighbors are always the closest node 
\* the its corresponding node on its side. 
\* the situation of x having  neighbor closer to y and y having a neighbor closer to x
\* can never happen, because the neighbor should first discovered 
\* (joined) by its closest ready node.

THEOREM NoPartition == 
TypeInvariant /\ Invariant=> 
    \A i, n \in I: 
                 /\status[i] \in { "ready", "ok"}
                 /\status[n] \in {"ready", "ok"}
                 /\ ~(i = n)
            => /\~RightNeighbor(lset[i]) = i
               /\~LeftNeighbor(lset[i]) = i
<1>1. SUFFICES ASSUME NEW i \in I,
        NEW n \in I,
        status[i] \in {"ready", "ok"},
        status[n] \in {"ready", "ok"},
        ~(i = n),
        TypeInvariant,
        HalfNeighbor
   PROVE  /\~RightNeighbor(lset[i]) = i
          /\~LeftNeighbor(lset[i]) = i
   BY DEF Invariant 

<1>2.  i \in ReadyOK /\ n \in ReadyOK /\ ~(i = n)
   BY <1>1 DEF ReadyOK, NodesReady, NodesOK

<1>4. ~\E k \in ReadyOK: ReadyOK = {k}
   BY <1>2, ReadyInI
<1>5. \A k \in ReadyOK : RightNeighbor(lset[k]) # k /\ LeftNeighbor(lset[k]) # k
   BY <1>1, <1>4 DEF HalfNeighbor
<1>9. QED BY <1>2, <1>5
THEOREM HalfNeighborNoReady == 
TypeInvariant /\ Invariant=> 
  \A i \in I: 
      status[i] \in  {"ready", "ok"}
      =>  (LeftNeighbor(lset[i]) = i /\ RightNeighbor(lset[i]) = i)
                            \/(~LeftNeighbor(lset[i]) = i /\ ~RightNeighbor(lset[i]) = i)
BY DEF Invariant, HalfNeighbor, ReadyOK, NodesReady, NodesOK
------------------------------------------------------------------------------------------------------------
\* Reduction

\* Basis Coverage calculation
THEOREM NeighborCoverageComponent == \A i, j \in I:
         /\RightNeighbor(lset[i]) = j
         /\ i # j
         => CwDist(i, j) = CwDist(i, RightCover(lset[i])) + CwDist(RightCover(lset[i]), LeftCover(lset[j])) + CwDist(LeftCover(lset[j]), j)
           /\ CwDist(RightCover(lset[i]), LeftCover(lset[j])) = 1
\* BY DEF RightCover, LeftCover
THEOREM NeighborhoodStrongCo == 
TypeInvariant=>
   \A i, ln, rn\in I:
        /\ln = LeftNeighbor(lset[i])
        /\ rn = RightNeighbor(lset[i]) 
      =>
         CwDist(LeftCover(lset[rn]), ln) >= CwDist(LeftCover(lset[rn]), rn)
       /\CwDist(rn, RightCover(lset[ln])) >= CwDist(ln, RightCover(lset[ln]))
\* BY CwDistRingCo2, prove CwDist(LeftCover(lset[rn]), rn) =< CwDist(ln, rn)

THEOREM NeighborhoodStrongCo2 == 
TypeInvariant=>
    \A i, ln, rn\in I:
        /\ln = LeftNeighbor(lset[i])
        /\ rn = RightNeighbor(lset[i]) 
      =>
         CwDist(LeftCover(lset[rn]), ln) >= CwDist(LeftCover(lset[ln]), ln)  
       /\CwDist(rn, RightCover(lset[ln])) >= CwDist(rn, RightCover(lset[rn]))
\* BY CwDistRingCo2 , prove CwDist(LeftCover(lset[ln]), ln) =<  CwDist(LeftCover(lset[ln]), LeftCover(lset[rn])) 

THEOREM CoverComponent ==\* Coverage consist of left coverage and right coverage
    \A i \in I: CwDist(LeftCover(lset[i]), RightCover(lset[i])) =  
                       CwDist(LeftCover(lset[i]), i) \*left coverage
                     + CwDist(i, RightCover(lset[i]))\*right coverage
\* BY DEF Covers
THEOREM LeftCoverToTheLeft == 
 TypeInvariant => 
       \A i \in I: CwDist(LeftCover(lset[i]), i) = AbsDist(LeftCover(lset[i]), i)
<1>1. SUFFICES ASSUME NEW i \in I,
      TypeInvariant
      PROVE CwDist(LeftCover(lset[i]), i) = AbsDist(LeftCover(lset[i]), i)
    OBVIOUS
<1>8. ~Distance(LeftCover(lset[i]), i) < 0
\* Proof sketch: the farest node as left neighbor to i would be the node i-1.  And the left distance from i to i-1
\* is 2^M - 1 which determines that the LeftCover(lset[i]) - i \in [0, -2^(M-1)]  
\* According to the definition of Dist(), The Dist(lc, i) = lc - i, hence negative.
<1>9. QED BY <1>8 DEF CwDist
\* BY DEF Covers, AbsDist

THEOREM SelfCover == 
TypeInvariant =>
    \A i \in I: Covers(lset[i], i)
<1>1. SUFFICES ASSUME NEW i \in I,
               TypeInvariant
      PROVE Covers(lset[i], i)
   OBVIOUS
<1>. lset[i] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>2. CwDist(LeftCover(lset[i]), i) =< CwDist(LeftCover(lset[i]), RightCover(lset[i])) 
   BY CoverComponent, RingLEQSemmantic, LeftCoverType, RightCoverType, IisNat
<1>9. QED BY <1>2 DEF Covers

THEOREM CoverSemmanticCoRight == 
    TypeInvariant => 
    \A i, k \in I: Covers(lset[i], k) /\ CwDist(i, k) = AbsDist(i, k)
                => CwDist(i, k) =< CwDist(i, RightCover(lset[i]))
<1>1. SUFFICES ASSUME NEW i \in I,
                      NEW k \in I,
                      Covers(lset[i],k), 
                      CwDist(i, k) = AbsDist(i, k),
                      TypeInvariant
      PROVE CwDist(i, k) =< CwDist(i, RightCover(lset[i]))
   OBVIOUS
<1>. lset[i] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>2. CwDist(LeftCover(lset[i]), i) =< CwDist(LeftCover(lset[i]), k)
   BY LeftCoverToTheLeft, <1>1, PassThrough, 
      LeftCoverType, IisNat
<1>3. CwDist(LeftCover(lset[i]), k) =< CwDist(LeftCover(lset[i]), RightCover(lset[i]))
   BY DEF Covers
<1>9. QED BY <1>2, <1>3, CwDistPropAddCo2, 
      CwDistType, LeftCoverType, RightCoverType, IisNat
THEOREM CoverSemmanticCoLeft == 
    TypeInvariant => 
    \A i, k \in I: Covers(lset[i], k) /\ CwDist(k, i) = AbsDist(k, i)
                => CwDist(k, i) =< CwDist(LeftCover(lset[i]), i) 
\* Similar to the CoverSemmanticCoRight
OMITTED

THEOREM CoverSemmanticCo1 == 
  ASSUME TypeInvariant,
         NEW i \in I, NEW k \in I,
         ~Covers(lset[i], k) 
  PROVE  CwDist(k, i) > CwDist(LeftCover(lset[i]), i) 
<1>. lset[i] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>1. SUFFICES ASSUME CwDist(k, i) =< CwDist(LeftCover(lset[i]), i)
               PROVE  FALSE
   BY Unequality3, CwDistType, LeftCoverType, IisNat
<1>2. CwDist(LeftCover(lset[i]), k) < CwDist(LeftCover(lset[i]), i)
   BY <1>1, CwDistProp, LeftCoverType, IisNat
<1>3. CwDist(LeftCover(lset[i]), i) =< CwDist(LeftCover(lset[i]), RightCover(lset[i]))
   BY RingLEQSemmantic, CoverComponent, LeftCoverType, RightCoverType, IisNat
<1>4. CwDist(LeftCover(lset[i]), k) < CwDist(LeftCover(lset[i]), RightCover(lset[i]))
   BY <1>1, <1>2, <1>3, TransLESS, 
      LeftCoverType, RightCoverType, CwDistType, IisNat 
<1>5. Covers(lset[i], k) 
   BY <1>4, Unequality6, 
      CwDistType, LeftCoverType, RightCoverType, IisNat
      DEF Covers
<1>9. QED BY <1>5, <1>1

THEOREM CoverSemmanticCo2 == 
    TypeInvariant =>
    \A i, k \in I: 
       ~Covers(lset[i], k) 
        =>CwDist(i, k) > CwDist(i, RightCover(lset[i])) 
\* similar to CoverSemmanticCo1
OMITTED
THEOREM CoverSemmanticCo3 ==  
    TypeInvariant =>
    \A i, k \in I: 
       CwDist(k, i) > CwDist(LeftCover(lset[i]), i) /\ CwDist(i, k) > CwDist(i, RightCover(lset[i]))
         =>~Covers(lset[i], k)        
<1>1. SUFFICES ASSUME NEW i \in I,
               NEW k \in I,
               CwDist(k, i) > CwDist(LeftCover(lset[i]), i),
               CwDist(i, k) > CwDist(i, RightCover(lset[i])),
               Covers(lset[i], k),
               TypeInvariant
      PROVE FALSE
   OBVIOUS
<1>. lset[i] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>2. CASE CwDist(i, k) = AbsDist(i, k)
   <2>1. CwDist(i, k) =< CwDist(i, RightCover(lset[i]))
      BY <1>1, <1>2, CoverSemmanticCoRight
   <2>2. QED BY <1>1, <2>1, Unequality3, 
         RightCoverType, CwDistType, IisNat
<1>3. CASE CwDist(k, i) = AbsDist(k, i)
   <2>1. CwDist(k, i) =< CwDist(LeftCover(lset[i]), i) 
      BY <1>1, <1>3, CoverSemmanticCoLeft
   <2>2. QED BY <1>1, <2>1, Unequality3, 
         LeftCoverType, CwDistType, IisNat
<1>9. QED BY <1>2,<1>3, AbsIsLeftOrRight, IisNat,AbsCommutativity
THEOREM CoverSemmanticCo == 
    TypeInvariant =>
    \A i, k \in I: 
       CwDist(k, i) > CwDist(LeftCover(lset[i]), i) /\ CwDist(i, k) > CwDist(i, RightCover(lset[i]))
         <=>~Covers(lset[i], k) 
BY CoverSemmanticCo1, CoverSemmanticCo2, CoverSemmanticCo3

THEOREM NeighborCoverageCoLeft == 
ASSUME TypeInvariant
PROVE \A i \in I: ~LeftNeighbor(lset[i]) = i
         => CwDist(LeftCover(lset[i]), i) = CwDist(LeftNeighbor(lset[i]), i) \div 2
<1>1. \A k \in I: lset[k] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>2. \A ls \in LSet: LeftNeighbor(ls) \in I 
   BY LeftNeighborType
<1>3. SUFFICES ASSUME NEW i \in I,
                      NEW ln \in I,
                ln = LeftNeighbor(lset[i]),
                ~ln = i,
                TypeInvariant
      PROVE CwDist(LeftCover(lset[i]), i) = CwDist(ln, i) \div 2
   BY <1>1,<1>2
<1>9. QED BY <1>3, CwDistCalculation2, IisNat, TypeInvariant DEF LeftCover, TypeInvariant
THEOREM NeighborCoverageCoRight == \* Neighbors separate the coverage between them half half
ASSUME TypeInvariant 
PROVE \A i \in I: 
           ~RightNeighbor(lset[i]) = i
           =>
           CwDist(i, RightCover(lset[i])) =< CwDist(i, RightNeighbor(lset[i])) \div 2
<1>1. \A n \in I: lset[n] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>2. \A ls \in LSet:RightNeighbor(ls) \in I
   BY RightNeighborType
<1>3. SUFFICES ASSUME NEW i \in I,
                      NEW rn \in I,
                rn = RightNeighbor(lset[i]),
                ~rn = i,
                TypeInvariant
      PROVE  CwDist(i, RightCover(lset[i])) =< CwDist(i, rn) \div 2
   BY <1>1,<1>2
<1>7. QED BY <1>3, CwDistCalculation1, IisNat, TypeInvariant DEF RightCover, TypeInvariant
THEOREM NeighborCoverageCoCoRight == 
     TypeInvariant => \A i \in I: 
           CwDist(i, LeftCover(lset[RightNeighbor(lset[i])])) 
           =< (CwDist(i, RightNeighbor(lset[i])) + 1) \div 2
THEOREM NeighborConventionLeft == 
   TypeInvariant => \A x \in I: 
            ~LeftNeighbor(lset[x]) = x
           => 
              CwDist(LeftCover(lset[x]), x) < CwDist(LeftNeighbor(lset[x]), x)
<1>1. SUFFICES ASSUME NEW x \in I,
            TypeInvariant,
            ~LeftNeighbor(lset[x]) = x
      PROVE CwDist(LeftCover(lset[x]), x) < CwDist(LeftNeighbor(lset[x]), x)
   OBVIOUS
<1>. lset[x] \in LSet
BY TypeInvariant DEF TypeInvariant
<1>2. CwDist(LeftNeighbor(lset[x]), x) # 0 
   BY <1>1, CwDistZero, LeftNeighborType, IisNat
<1>4. CwDist(LeftCover(lset[x]), x) = CwDist(LeftNeighbor(lset[x]), x) \div 2
   BY <1>1, NeighborCoverageCoLeft
<1>9. QED BY <1>2, <1>4, DivLess, CwDistType, LeftNeighborType, 
             LeftCoverType, IisNat
THEOREM NeighborConventionRight == 
   TypeInvariant => \A x \in I: 
           ~RightNeighbor(lset[x]) = x
           => CwDist(x, RightCover(lset[x])) < CwDist(x, RightNeighbor(lset[x])) 
<1>1. SUFFICES ASSUME NEW x \in I,
            TypeInvariant,
            ~RightNeighbor(lset[x]) = x
      PROVE CwDist(x, RightCover(lset[x])) < CwDist(x, RightNeighbor(lset[x]))
   OBVIOUS
<1>. lset[x] \in LSet
BY TypeInvariant DEF TypeInvariant
<1>2. CwDist(x, RightNeighbor(lset[x])) # 0
   BY <1>1, CwDistZero,RightNeighborType, IisNat
<1>4. CwDist(x, RightCover(lset[x])) =< CwDist(x, RightNeighbor(lset[x])) \div 2
   BY <1>1, NeighborCoverageCoRight
<1>9. QED BY <1>2, <1>4, DivLess, CwDistType, RightNeighborType, 
             RightCoverType, IisNat
THEOREM NeighborCoverageCo2 == 
   TypeInvariant => \A i, rn \in I: ~(i = rn) /\ rn = RightNeighbor(lset[i])=> 
   CwDist(LeftCover(lset[rn]), rn)< CwDist(RightCover(lset[i]), rn)
<1>0. SUFFICES ASSUME TypeInvariant PROVE
      \A i, rn \in I: ~(i = rn) /\ rn = RightNeighbor(lset[i])=> 
   CwDist(LeftCover(lset[rn]), rn)< CwDist(RightCover(lset[i]), rn)
   OBVIOUS
<1>. \A n \in I: lset[n] \in LSet
   BY TypeInvariant DEF TypeInvariant 
<1>1. SUFFICES ASSUME NEW i \in I,
               NEW rn \in I, 
               ~(i = rn),
               rn = RightNeighbor(lset[i]),
               NEW lcrn \in Nat, 
               lcrn = LeftCover(lset[rn]),
               NEW rci \in Nat,
               rci = RightCover(lset[i])
      PROVE CwDist(lcrn, rn)< CwDist(rci, rn)
   BY LeftCoverType, RightCoverType, IisNat, CwDistType
<1>2. CwDist(i, rn) = CwDist(i, rci) + 
           CwDist(rci, lcrn) + CwDist(lcrn, rn)
   BY <1>1, NeighborCoverageComponent
<1>3. CwDist(rci, rn) = CwDist(rci, lcrn) + CwDist(lcrn, rn)
   BY <1>2, RingComposite, IisNat, SlowestZenon \* don't know why
<1>4. CwDist(rci, rn) = 1 + CwDist(lcrn, rn)
   BY <1>1, NeighborCoverageComponent, <1>3
<1>9. QED BY <1>4, LessAddRel, CwDistType,IisNat

THEOREM NeighborCoverageLemma1 == 
TypeInvariant =>
       \A i, rn\in I:
        /\ rn = RightNeighbor(lset[i])
        /\ ~(rn = i)
       =>
        CwDist(LeftCover(lset[i]), RightCover(lset[i])) 
           =< CwDist(LeftCover(lset[i]), rn)
<1>1. SUFFICES ASSUME NEW i \in I,
                      NEW rn \in I, 
                      rn = RightNeighbor(lset[i]),
                      ~(rn = i), 
                      TypeInvariant
   PROVE CwDist(LeftCover(lset[i]), RightCover(lset[i])) 
           =< CwDist(LeftCover(lset[i]), rn)
   OBVIOUS
<1>. lset[i] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>2. CwDist(i, RightCover(lset[i])) =< CwDist(i, rn)
   BY <1>1, NeighborConventionRight, Unequality6, 
   CwDistType, RightCoverType, IisNat
<1>4. CwDist(LeftCover(lset[i]), i) =< CwDist(LeftCover(lset[i]), RightCover(lset[i]))
   BY <1>1, CoverComponent,  RingLEQSemmantic, LeftCoverType, RightCoverType, IisNat
<1>9. QED BY CwDistPropAddCo2,  <1>2, <1>4, LeftCoverType, RightCoverType, IisNat

THEOREM NeighborCoverageLemmaRight == 
\* if node i covers k, then k must pass through right cover to reach right neighbor
\* by going to the right 
ASSUME TypeInvariant
PROVE
    \A i, rn, k \in I:
        /\ rn = RightNeighbor(lset[i]) 
        /\ Covers(lset[i], k)
        /\ ~(rn = i)
      =>
        CwDist(k, RightCover(lset[i])) =< CwDist(k, rn)
  
<1>. \A j \in I: lset[j] \in LSet
   BY TypeInvariant, SlowestZenon DEF TypeInvariant
<1>1. SUFFICES ASSUME NEW i \in I, 
          NEW k \in I,
          NEW rn \in I,
          rn = RightNeighbor(lset[i]), 
          Covers(lset[i], k),
          ~(rn = i),
          lset[i] \in LSet,
          NEW lc \in Nat,
          NEW rc \in Nat,
          lc = LeftCover(lset[i]),
          rc = RightCover(lset[i]),
          TypeInvariant
      PROVE  CwDist(k, rc) =< CwDist(k, rn)  
   BY CwDistType, RightCoverType, LeftCoverType, IisNat
<1>4. CwDist(lc, rc)  =< CwDist(lc, rn)
   BY <1>1,NeighborCoverageLemma1, TypeInvariant
<1>5. CwDist(lc, k) =< CwDist(lc, rc)
   BY <1>1 DEF Covers
<1>6. CwDist(lc, k) =< CwDist(lc, rn)
   BY <1>4,<1>5, TransLEQ, CwDistType, IisNat
<1>9. QED BY <1>1, <1>4, <1>5, <1>6, CwDistPropAddCo2, 
      CwDistType, LeftCoverType, RightCoverType, 
      LeftNeighborType, RightNeighborType, IisNat
THEOREM NeighborCoverageLemmaLeft == 
\* if node i covers k, then k must pass through left cover to reach left neighbor
\* by going to the left 
TypeInvariant => 
    \A i, ln, k \in I:
        /\ ln = LeftNeighbor(lset[i]) 
        /\ Covers(lset[i], k)
        /\ ~(ln = i)
      =>
        CwDist(LeftCover(lset[i]), k) =< CwDist(ln, k) 
OMITTED \* similar to the NeighborCoverageLemmaRight one
THEOREM NeighborCoverageRight == \* if node i covers k, then k is more left than the left cover of i's right neighbor
                               \* and k is more right to the right cover of i's left neighbor
    TypeInvariant=>
    \A i, rn, k \in I:
        /\ rn = RightNeighbor(lset[i]) 
        /\ Covers(lset[i], k)
        /\ ~(rn = i)
      =>
        CwDist(k, rn) > CwDist(LeftCover(lset[rn]), rn)
<1>1. SUFFICES ASSUME NEW i \in I, 
          NEW k \in I,
          NEW rn \in I,
          rn = RightNeighbor(lset[i]), 
          Covers(lset[i], k),
          ~(rn = i),
          TypeInvariant
      PROVE CwDist(k, rn) > CwDist(LeftCover(lset[rn]), rn)    
   OBVIOUS
<1>. \A j \in I: lset[j] \in LSet
   BY <1>1 DEF TypeInvariant
<1>3. CwDist(k, RightCover(lset[i])) =< CwDist(k, rn)
   BY <1>1, NeighborCoverageLemmaRight
<1>4. CwDist(k, rn)= CwDist(k, RightCover(lset[i])) + CwDist(RightCover(lset[i]), rn) 
   BY <1>3, RingLEQSemmantic,
         CwDistType, RightCoverType, IisNat
<1>5. CwDist(RightCover(lset[i]), rn) =< CwDist(k, rn)
   BY <1>4, RingLEQSemmanticCo, 
      CwDistType, RightCoverType, IisNat
<1>6. CwDist(LeftCover(lset[rn]), rn) < CwDist(RightCover(lset[i]), rn)
   BY <1>1, NeighborCoverageCo2
<1>9. QED BY <1>5,<1>6, TransLESS, LessGreaterDuality,
      CwDistType, RightCoverType, LeftCoverType, IisNat 
THEOREM NeighborCoverageLeft == 
    TypeInvariant => 
    \A i, ln, k \in I:
        /\ln = LeftNeighbor(lset[i]) 
        /\ Covers(lset[i], k)
        /\ ~(ln = i)
      =>
        CwDist(ln, k) > CwDist(ln, RightCover(lset[ln]))
\* similar to THEOREM NeighborCoverageRight
OMITTED
THEOREM CoverDisjointnessCo == \* even x= y, it holds
    TypeInvariant => 
     \A i, rn, k \in I: /\RightNeighbor(lset[i]) = rn 
                      /\ rn # i
                      /\ Covers(lset[i], k)
                      /\ AbsDist(i, k) = CwDist(i, k) 
                     => CwDist(i, k) < CwDist(i, LeftCover(lset[rn]))
<1>1. SUFFICES ASSUME 
      NEW i \in I, 
      NEW rn \in I, 
      NEW k \in I,
      rn # i,
      RightNeighbor(lset[i]) = rn,
      Covers(lset[i], k),
      AbsDist(i, k) = CwDist(i, k),
      TypeInvariant
      PROVE  CwDist(i, k) < CwDist(i, LeftCover(lset[rn]))
   OBVIOUS
<1>. \A j \in I: lset[j] \in LSet 
   BY TypeInvariant DEF TypeInvariant
<1>3. CwDist(i, k) =< CwDist(i, RightCover(lset[i]))
   BY <1>1, CoverSemmanticCoRight
<1>4. CwDist(i, RightCover(lset[i])) < CwDist(i, rn)
   BY <1>1, NeighborConventionRight
<1>5. CwDist(i, k) <  CwDist(i, rn)
   BY TransLESS, <1>3, <1>4, CwDistType, RightCoverType, IisNat
<1>6. CwDist(LeftCover(lset[rn]), rn) < CwDist(k, rn)
   BY <1>1, NeighborCoverageRight, LessGreaterDuality, CwDistType, LeftCoverType, IisNat
<1>9. QED BY CwDistPropAdd, <1>6,<1>5, CwDistType, RightCoverType, LeftCoverType, IisNat
THEOREM NeighborhoodStrongCo3 ==
   TypeInvariant => 
   \A i, ln, rn, k \in I:
        /\ln = LeftNeighbor(lset[i])
        /\ rn = RightNeighbor(lset[i]) 
        /\ ~ (ln = i)
        /\ ~ (rn = i)
        /\ Covers(lset[i], k)
      =>
        /\CwDist(ln, k) =< CwDist(rn, k)
        /\CwDist(k, rn) =< CwDist(k, ln)
<1>1. SUFFICES ASSUME NEW i \in I,
        NEW ln \in I, 
        NEW rn \in I,
        NEW k \in I,
        ln = LeftNeighbor(lset[i]),
        rn = RightNeighbor(lset[i]), 
        ~ (ln = i),
        ~(rn = i),
        Covers(lset[i], k), 
        TypeInvariant
   PROVE CwDist(ln, k) =< CwDist(rn, k)
        /\CwDist(k, rn) =< CwDist(k, ln)
   OBVIOUS
<1>. lset[i] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>2. CwDist(LeftCover(lset[i]), k) =< CwDist(ln, k) 
      BY <1>1, NeighborCoverageLemmaLeft, TypeInvariant
<1>3. CwDist(LeftCover(lset[i]), k) =< CwDist(LeftCover(lset[i]), RightCover(lset[i]))
      BY Covers(lset[i], k) DEF Covers
<1>4. CwDist(k, RightCover(lset[i])) =< CwDist(k, rn) 
      BY <1>1, NeighborCoverageLemmaRight, TypeInvariant
<1>5. CwDist(ln, k) =< CwDist(ln, rn) 
      BY <1>2,<1>3,<1>4, CwDist5Postions, LeftCoverType, RightCoverType, IisNat
<1>9. QED BY <1>5,CwDistRingCo, LeftCoverType, RightCoverType, IisNat

THEOREM NeighborCoverageDisjoint == \* neighbors of i doesn't share coverage with i 
   TypeInvariant => 
   \A i, k,ln, rn \in I: Covers(lset[i], k)
                        /\ status[i] = "ready"
                        /\ ln = LeftNeighbor(lset[i])
                        /\ rn = RightNeighbor(lset[i])
                        /\ ~(ln= i)
                        /\ ~(rn = i)
                      =>   /\~Covers(lset[ln], k) 
                           /\~Covers(lset[rn], k) 
<1>1. SUFFICES ASSUME NEW i\in I, 
               NEW k \in I,
               NEW ln \in I, 
               NEW rn \in I,
               ~(ln= i),
               ~(rn = i),
               ln = LeftNeighbor(lset[i]), 
               rn = RightNeighbor(lset[i]),
               Covers(lset[i], k),
               TypeInvariant
      PROVE  
            ~Covers(lset[rn], k)
            /\~Covers(lset[ln], k)
   OBVIOUS
<1>. \A a \in I: lset[a] \in LSet 
   BY TypeInvariant DEF TypeInvariant
<1>2. CwDist(ln, k) > CwDist(ln, RightCover(lset[ln]))
   BY <1>1, NeighborCoverageLeft
<1>3. CwDist(k, rn) > CwDist(LeftCover(lset[rn]), rn)
   BY <1>1, NeighborCoverageRight
<1>4. CwDist(k, ln) >= CwDist(k, rn)
   BY <1>1, NeighborhoodStrongCo3
<1>5. CwDist(rn, k) >= CwDist(ln, k)
   BY <1>1, NeighborhoodStrongCo3

<1>6. CwDist(k, ln) > CwDist(LeftCover(lset[ln]), ln)
\* With alrithmatic reasoner  the proof would be shorter 
   <2>1. CwDist(k, ln) = CwDist(k, rn) + CwDist(rn, ln)
      BY <1>4, RingGEQSemmantic,
         CwDistType, IisNat
   <2>3. CwDist(LeftCover(lset[rn]), ln) >= CwDist(LeftCover(lset[rn]), rn)
      BY <1>1, NeighborhoodStrongCo
   <2>4. CwDist(LeftCover(lset[rn]), ln) = 
             CwDist(LeftCover(lset[rn]), rn) + CwDist(rn, ln)
      BY <2>3, RingGEQSemmantic, 
         CwDistType, LeftCoverType, IisNat
   <2>5. CwDist(rn, ln) +  CwDist(k, rn)
         > CwDist(rn, ln) +  CwDist(LeftCover(lset[rn]), rn)
      BY <1>3, MonotonyAddNeg, 
      CwDistType, LeftCoverType, IisNat
   <2>6. CwDist(k, rn) + CwDist(rn, ln)
         >  CwDist(LeftCover(lset[rn]), rn)+ CwDist(rn, ln)
      BY <2>5, CommutativityAdd,
      CwDistType, LeftCoverType, IisNat
   <2>7. CwDist(k, ln) > CwDist(LeftCover(lset[rn]), ln)
      BY <2>1, <2>4, <2>6 
   <2>8. CwDist(LeftCover(lset[rn]), ln) >= CwDist(LeftCover(lset[ln]), ln)
      BY <1>1, NeighborhoodStrongCo2
   <2>9. QED BY <2>7, <2>8, TransGEATER,
      CwDistType, LeftCoverType, IisNat
      
<1>7. CwDist(rn, k) > CwDist(rn, RightCover(lset[rn]))
   <2>1. CwDist(rn, k) = CwDist(rn, ln) + CwDist(ln, k)
      BY <1>5, RingGEQSemmanticCo, 
         CwDistType, IisNat
   <2>3. CwDist(rn, RightCover(lset[ln])) >= CwDist(ln, RightCover(lset[ln]))
      BY <1>1, NeighborhoodStrongCo
   <2>4. CwDist(rn, RightCover(lset[ln])) = 
             CwDist(rn, ln) + CwDist(ln, RightCover(lset[ln]))
      BY <2>3, RingGEQSemmanticCo, 
         CwDistType, RightCoverType, IisNat
   <2>6. CwDist(rn, ln) + CwDist(ln, k)
         >  CwDist(rn, ln) + CwDist(ln, RightCover(lset[ln]))
      BY <1>2, MonotonyAddNeg,
      CwDistType, RightCoverType, IisNat
   <2>7. CwDist(rn, k) > CwDist(rn, RightCover(lset[ln]))
      BY <2>1, <2>4, <2>6 
   <2>8. CwDist(rn, RightCover(lset[ln])) >= CwDist(rn, RightCover(lset[rn]))
      BY <1>1, NeighborhoodStrongCo2
   <2>9. QED BY <2>7, <2>8, TransGEATER,
      CwDistType, RightCoverType, IisNat
<1>8. ~Covers(lset[ln], k) 
   BY <1>2, <1>6, CoverSemmanticCo, TypeInvariant
<1>9. ~Covers(lset[rn], k)
   BY <1>3, <1>7, CoverSemmanticCo, TypeInvariant
<1>10. QED BY <1>8, <1>9
THEOREM RightNeighborCoverageDis == \*right neighbor of a "ready" node i doesn't share coverage with i
  TypeInvariant/\ Invariant
=> 
  \A x, y, k \in I: Covers(lset[x], k)
                   /\ status[x] = "ready"
                   /\ y = RightNeighbor(lset[x])
                   /\ ~(y = x)
                 =>~Covers(lset[y], k)    
<1>1. SUFFICES ASSUME 
          NEW x \in I,
          NEW y \in I, 
          NEW k \in I,
          Covers(lset[x], k),
          status[x] = "ready",
          y = RightNeighbor(lset[x]),
          ~(y = x), 
          TypeInvariant, 
          Invariant
      PROVE ~Covers(lset[y], k)   
   OBVIOUS
<1>2. ~(LeftNeighbor(lset[x]) = x) 
   BY <1>1, HalfNeighborNoReady, Invariant
<1>3. lset[x] \in LSet
   BY <1>1 DEF TypeInvariant   
<1>9. QED BY <1>1, <1>2, <1>3, NeighborCoverageDisjoint, RightNeighborType, LeftNeighborType


THEOREM CoverMonotony == \* if a node lies left to another node, 
                         \* then its left cover lies also to the left to
                         \* the other's left cover
    TypeInvariant/\ Invariant 
 =>
      \A x, y, z \in I: CwDist(x, z) < CwDist(x, y) 
                  /\  RightNeighbor(lset[x]) = z 
                  /\ status[x] = "ready" 
                  /\ status[y] = "ready" 
                  /\ x # y
                  /\ z # y
                => 
                  CwDist(x, LeftCover(lset[z])) =<  CwDist(x, LeftCover(lset[y]))
<1>1. SUFFICES ASSUME 
            NEW x \in I,
            NEW y \in I, 
            NEW z \in I, 
            CwDist(x, z) < CwDist(x, y),
            RightNeighbor(lset[x]) = z, 
            status[x] = "ready", 
            status[y] = "ready", 
            x # y,
            z # y, 
            TypeInvariant,
            Invariant
      PROVE CwDist(x, LeftCover(lset[z])) =<  CwDist(x, LeftCover(lset[y]))
   OBVIOUS
<1>. \A i \in I: lset[i] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>2. CwDist(LeftNeighbor(lset[y]), y) =< CwDist(x, y)
   BY <1>1, Neighborhood, Invariant, Unequality2, LeftNeighborType, CwDistType, IisNat
<1>3. CwDist(LeftCover(lset[y]), y) = CwDist(LeftNeighbor(lset[y]), y) \div 2
   BY <1>1, NeighborCoverageCoLeft, NoPartition, Invariant, TypeInvariant
<1>4. CwDist(LeftNeighbor(lset[y]), y) \div 2 =< CwDist(x, y) \div 2
   BY <1>2, MonotonyDiv, 
      LeftNeighborType, LeftCoverType, CwDistType, IisNat
<1>5. CwDist(LeftCover(lset[y]), y) =< CwDist(x, y) \div 2
   BY <1>3, <1>4
<1>6. CwDist(x, LeftCover(lset[z])) =< (CwDist(x, z) + 1) \div 2
   BY <1>1, NeighborCoverageCoCoRight
<1>7. (CwDist(x, z) + 1) =< CwDist(x, y)
   BY <1>1, OneDistance,  IisNat
<1>8. CwDist(x, LeftCover(lset[z])) =< CwDist(x, y) \div 2
   BY <1>6,<1>7, CwDistMonotonyDivCo, LeftCoverType, IisNat 
<1>9. CwDist(x, y) \div 2 =< CwDist(x, LeftCover(lset[y]))
   BY <1>5, CwDistCalculation4, LeftCoverType, IisNat
<1>10. QED BY <1>9, <1>8, TransLEQ,
       CwDistType, LeftCoverType, IisNat, DivType
----------------------------------------------------------------------------------------------------------
THEOREM CoverageLemma == 
\* If key k lies within the coverage of a "ready" node i, then i is the closest "ready" node
           \* left node should take the coverage 
TypeInvariant /\  Invariant =>
   \A i, k, n \in I: 
      /\ status[i] = "ready" 
      /\ status[n] = "ready"
      /\ Covers(lset[i], k)
   => AbsDist(i, k) =< AbsDist(n, k)
         
<1>1.SUFFICES 
           ASSUME NEW i \in I,
                  NEW k \in I,
                  NEW n \in I,
                  TypeInvariant,
                  Invariant,
                  status[i] = "ready",
                  status[n] = "ready",
                  Covers(lset[i], k),
                  ~(AbsDist(i, k) =< AbsDist(n, k))
           PROVE FALSE
   BY DEF Covers
<1>2. CASE n = i
   <2>1. AbsDist(i, k) = AbsDist(n, k)
      BY <1>2
   <2>2. ~(AbsDist(i, k) = AbsDist(n, k))
      BY <1>1, Unequality6, AbsDistType, IisNat
   <2>9. QED BY <2>1,<2>2
<1>3. CASE ~(n = i)
   <2>. lset[i] \in LSet 
      BY TypeInvariant DEF TypeInvariant
   <2>01. ~RightNeighbor(lset[i]) = i /\~LeftNeighbor(lset[i]) = i
      BY status[i] = "ready", status[n] = "ready", <1>3, NoPartition, Invariant, TypeInvariant
   <2>1. CASE AbsDist(i, k) = CwDist(i, k) /\ AbsDist(n, k) = CwDist(n, k)
       \* n and i are to the left of k
       \* Proof sketch (backwards top down):
       \* We know that a node n (to the right of i) cannot be closer to i 
       \* than i's direct right neighbor (<3>8).
       \* Then we try to prove that n lies between i and its direct right neighbor(<3>7).
       \* To prove this, we show that the right distance from i to its right cover 
       \* should be smaller than the right distance from i to its right neighbor(<3>6);
       \* Bisides, we show that the right distance from i to n is less than to its 
       \* right cover(<3>5).
       \* By transitivity, we know that the right distance from i to n is less than to its 
       \* direct neighbor. 
       \* <3>5 is followed basically by case condition and <3>6 by NeighborConvention.
       \* There are a bunch of lemmas for the distance calculation on the ring used.
       \* Mathematical rules for unequality are heavily used here.
       \* Besides, the type invariant is used for proving lset[i] \in LSet.
      <3>1. CwDist(n, k) < CwDist(i, k)
         BY <1>1, <2>1,  Unequality2, CwDistType, IisNat
      <3>3. CwDist(i, n) =< CwDist(i, k) 
         BY <3>1, CwDistPropCo, IisNat
      <3>4. CwDist(i, k) =< CwDist(i, RightCover(lset[i]))
         BY <2>1, Covers(lset[i], k), CoverSemmanticCoRight, TypeInvariant
      <3>5. CwDist(i, n) =< CwDist(i, RightCover(lset[i]))
         BY <3>3, <3>4, TransLEQ, CwDistType, RightCoverType, IisNat
      <3>6. CwDist(i, RightCover(lset[i])) < CwDist(i, RightNeighbor(lset[i])) 
         BY <1>3, NoPartition, <1>1, NeighborConventionRight, Invariant
      <3>7. CwDist(i, n) < CwDist(i, RightNeighbor(lset[i]))
         BY <3>5, <3>6, CwDistType, IisNat, RightNeighborType, RightCoverType, TransLESS
      <3>8. ~(CwDist(i, n) < CwDist(i, RightNeighbor(lset[i])))
         BY status[i] = "ready", status[n] = "ready", Neighborhood, StatusDuality, <1>3,
             CwDistType, RightNeighborType, IisNat, TypeInvariant, Invariant
      <3>9. QED BY <3>8, <3>7
   <2>2. CASE AbsDist(i, k) = CwDist(i, k) /\ AbsDist(n, k) = CwDist(k, n)
   \* i is to the left and n is to the right of k
   \* Proof Idea: We assume that k is closer to n than i, then we try to prove 
   \* k is closer to i than n. To prove this, we use the right cover of i. 
   \* Since k is closer to i than the right cover of i by assumption, 
   \* which is less than or equal to the half of the distance between i and n, 
   \* due to their neighborhood,
   \* we can conclude that k is closer to i than n. QED
      <3>7. CwDist(i, k) > CwDist(k, n) 
      BY ~(AbsDist(i, k) =< AbsDist(n, k)), <2>2, 
         Unequality2, LessGreaterDuality, CwDistType, IisNat
      <3>8. CwDist(i, k) =< CwDist(k, n)
         <4>1. CwDist(i, n) = CwDist(i, k) + CwDist(k, n)
             <5>1. Distance(n, k) < 0
                BY <2>2, AbsDistRightSide, IisNat
             <5>2. Distance(k, i) < 0
                BY <2>2, AbsDistLeftSide, IisNat
             <5>4. CwDist(i, n) = CwDist(i, k) + CwDist(k, n)
                BY <1>3, <5>1, <5>2, RingAddProp, IisNat
             <5>9. QED BY <5>4
         <4>2. CwDist(i, k) =< CwDist(i, n) \div 2
             <5>1. CwDist(i, RightNeighbor(lset[i])) =< CwDist(i, n)
                <6>1. CASE RightNeighbor(lset[i]) = n
                   BY <6>1, Unequality6, IisNat, RightNeighborType, CwDistType
                <6>2. CASE ~ (RightNeighbor(lset[i]) = n)
                   <7>2. ~CwDist(i, n) < CwDist(i, RightNeighbor(lset[i]))
                      BY <1>1, Neighborhood, StatusDuality, <1>3
                   <7>3. CwDist(i, n) >= CwDist(i, RightNeighbor(lset[i]))
                      BY <7>2, Unequality22, CwDistType, IisNat, RightNeighborType
                   <7>9. QED BY <7>3, LessGreaterDuality2,
                                IisNat, RightNeighborType, CwDistType
                <6>9. QED BY <6>1, <6>2
             <5>2. CwDist(i, RightCover(lset[i])) =< CwDist(i, RightNeighbor(lset[i])) \div 2
                BY <2>01, NeighborCoverageCoRight, IisNat, RightCoverType, RightNeighborType, TypeInvariant
             <5>3. CwDist(i, RightCover(lset[i])) =< CwDist(i, n) \div 2          
                <6>1. CwDist(i, RightNeighbor(lset[i])) \div 2 =< CwDist(i, n) \div 2
                   BY <5>1, <5>2, MonotonyDiv,CwDistType, IisNat, RightNeighborType
                <6>2. QED BY <6>1, <5>2, TransLEQ, 
                DivType, CwDistType, RightNeighborType, RightCoverType,IisNat, 
                TypeInvariant DEF TypeInvariant
             <5>4. CwDist(i, k)  =< CwDist(i, RightCover(lset[i]))
                BY <2>2, Covers(lset[i], k), CoverSemmanticCoRight, TypeInvariant
             <5>9. QED BY <5>4, <5>3, TransLEQ, CwDistType, RightCoverType, IisNat, DivType
         <4>9. QED BY <4>1, <4>2, Unequality5, CwDistType, IisNat
      <3>9. QED BY <3>7,<3>8, Unequality3, CwDistType, IisNat
   <2>3. CASE AbsDist(k, i) = CwDist(k, i) /\ AbsDist(k, n) = CwDist(k, n)
     \* i and n lie right to k
     \* Proof sketch: symmetry to the <2>1
       <3>1. CwDist(k, n) < CwDist(k, i) \*and n lies between i and k
          BY <2>3, <1>1, Unequality2, IisNat, CwDistType, AbsCommutativity
       <3>3. CwDist(n, i) =< CwDist(k, i)
          BY <3>1, CwDistProp, IisNat, SideDuality
       <3>4. CwDist(k, i) =< CwDist(LeftCover(lset[i]), i)
         BY <2>3, Covers(lset[i], k), CoverSemmanticCoLeft, TypeInvariant
       <3>5. CwDist(n, i) =< CwDist(LeftCover(lset[i]), i)
          BY <3>3, <3>4, TransLEQ, CwDistType, LeftCoverType, IisNat
       <3>6. CwDist(LeftCover(lset[i]), i) < CwDist(LeftNeighbor(lset[i]), i) 
          BY <1>1, <1>3, NeighborConventionLeft, TypeInvariant, NoPartition
       <3>7. CwDist(n, i) < CwDist(LeftNeighbor(lset[i]), i)
          BY <3>5, <3>6, CwDistType, IisNat, LeftNeighborType, LeftCoverType, TransLESS
       <3>8. ~(CwDist(n, i) < CwDist(LeftNeighbor(lset[i]), i))
          BY status[i] = "ready", status[n] = "ready", Neighborhood, StatusDuality, 
             <1>3, TypeInvariant, Invariant
       <3>9. QED BY <3>7,<3>8  
   <2>4. CASE AbsDist(i, k) = CwDist(k, i) /\ AbsDist(n, k) = CwDist(n, k)
      \* n is to the left and i is to the right to k
   \* i is to the right and n is to the left of k
   \* Proof Idea: We assume that k is closer to n than i, then we try to prove 
   \* k is closer to i than n. To prove this, we use the left cover of i. 
   \* Since k is closer to i than the left cover of i by assumption, 
   \* which is less than or equal to the half of the distance between i and n, 
   \* due to their neighborhood,
   \* we can conclude that k is closer to i than n. QED
      <3>7. CwDist(k, i) > CwDist(n, k) 
      BY ~(AbsDist(i, k) =< AbsDist(n, k)), <2>4, 
         Unequality2, LessGreaterDuality, CwDistType, IisNat
      <3>8. CwDist(k, i) =< CwDist(n, k)
         <4>1. CwDist(n, i) =  CwDist(n, k) + CwDist(k, i)
             <5>1. Distance(k, n) < 0
                BY <2>4, AbsDistLeftSide, IisNat
             <5>2. Distance(i, k) < 0
                BY <2>4, AbsDistRightSide, IisNat
             <5>4. CwDist(n, i) = CwDist(n, k) + CwDist(k, i)
                BY <5>1, <5>2, RingAddProp, IisNat, <1>3
             <5>9. QED BY <5>4
         <4>2. CwDist(k, i) =< CwDist(n, i) \div 2
             <5>1. CwDist(LeftNeighbor(lset[i]), i) =< CwDist(n, i)
                <6>1. CASE LeftNeighbor(lset[i]) = n
                   BY <6>1, Unequality6, IisNat, LeftNeighborType, CwDistType
                <6>2. CASE ~ (LeftNeighbor(lset[i]) = n)
                   <7>2. CwDist(n, i) >= CwDist(LeftNeighbor(lset[i]), i)
                      BY <1>1, Neighborhood, Unequality22, <1>3, StatusDuality,
                         CwDistType, IisNat, LeftNeighborType
                   <7>9. QED BY <7>2, LessGreaterDuality2,
                                IisNat, LeftNeighborType, CwDistType
                <6>9. QED BY <6>1, <6>2
             <5>2. CwDist(LeftNeighbor(lset[i]), i) \div 2 = CwDist(LeftCover(lset[i]), i)
                BY <2>01, NeighborCoverageCoLeft, IisNat, LeftCoverType, LeftNeighborType, TypeInvariant
             <5>3. CwDist(LeftCover(lset[i]), i) =< CwDist(n, i) \div 2
                (*BY <5>1, <5>2, MonotonyDiv, CwDistType, IisNat, RightNeighborType*)                
                <6>1. CwDist(LeftNeighbor(lset[i]), i) \div 2 =< CwDist(n, i) \div 2
                   BY <5>1, <5>2, MonotonyDiv, CwDistType, IisNat, LeftNeighborType
                <6>2. QED BY <6>1, <5>2
             <5>4. CwDist(k, i)  =< CwDist(LeftCover(lset[i]), i)
                BY <2>4, Covers(lset[i], k), CoverSemmanticCoLeft, TypeInvariant, AbsCommutativity, IisNat
             <5>9. QED BY <5>4, <5>3, TransLEQ, CwDistType, LeftCoverType, IisNat, DivType
         <4>9. QED BY <4>1, <4>2, CommutativityAdd, Unequality5, 
               CwDistType, IisNat
      <3>9. QED BY <3>7,<3>8, Unequality3, CwDistType, IisNat
   <2>9. QED BY <2>1, <2>2, <2>3, <2>4, AbsIsLeftOrRight, AbsCommutativity, IisNat
<1>9. QED BY <1>2, <1>3


\* System properties

THEOREM CorrectDeliverWithoutConsistency == 
TypeInvariant /\ Invariant=> 
        \A i, k, n \in I: 
        Deliver(i,k) /\ status[n] = "ready" 
      => AbsDist(i, k) =< AbsDist(n, k)
BY CoverageLemma DEF Deliver, Covers
-------------------------------------------------------------------------------------------------------------------------
THEOREM NotCovers == 
TypeInvariant /\ Invariant => \A x, y \in I:
      /\status[x] = "ready"   
      /\status[y] = "ready"
      /\ ~(x = y)
     => ~Covers(lset[x], y) /\ ~Covers(lset[y], x)
<1>1. SUFFICES ASSUME NEW x \in I,
                      NEW y \in I,
               status[x] = "ready",   
               status[y] = "ready",
               ~(x = y), 
               TypeInvariant,
               Invariant,
               Covers(lset[x], y) \/Covers(lset[y], x)
      PROVE FALSE
   OBVIOUS
<1>. lset[x] \in LSet /\ lset[y] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>5. CASE Covers(lset[y], x) /\ CwDist(y, x) = AbsDist(x, y)
   <2>1. CwDist(y, x) =< CwDist(y, RightCover(lset[y]))
      BY <1>1, <1>5, CoverSemmanticCoRight, AbsCommutativity, IisNat
   <2>3. CwDist(y, RightCover(lset[y])) <  CwDist(y, RightNeighbor(lset[y]))
      BY <1>1, NoPartition, NeighborConventionRight, Invariant DEF ReadyOK, NodesReady, NodesOK
   <2>4. CwDist(y, x) < CwDist(y, RightNeighbor(lset[y]))
      BY <2>3, <2>1, TransLESS, 
         CwDistType, RightCoverType, RightNeighborType, IisNat
   <2>5. ~(CwDist(y, x) < CwDist(y, RightNeighbor(lset[y])))
      BY <1>1, Neighborhood, Invariant
   <2>9. QED BY <2>5,<2>4
<1>6. CASE Covers(lset[x], y) /\ CwDist(y, x) = AbsDist(x, y)
   <2>1. CwDist(y, x) =< CwDist(LeftCover(lset[x]), x)
      BY <1>1, <1>6, CoverSemmanticCoLeft, AbsCommutativity, IisNat
   <2>2. CwDist(LeftCover(lset[x]), x) < CwDist(LeftNeighbor(lset[x]), x)
      BY  <1>1, NoPartition, NeighborConventionLeft, Invariant
   <2>3. CwDist(y, x) < CwDist(LeftNeighbor(lset[x]), x)
      BY <2>1, <2>2, TransLESS,
      CwDistType, LeftCoverType, LeftNeighborType, IisNat
   <2>4. ~(CwDist(y, x) < CwDist(LeftNeighbor(lset[x]), x))
      BY <1>1, Neighborhood, Invariant
   <2>9. QED BY <2>3, <2>4
<1>7. CASE Covers(lset[x], y) /\ CwDist(x, y) = AbsDist(x, y)
\* similar to <1>5, exchange x and y
   <2>1. CwDist(x, y) =< CwDist(x, RightCover(lset[x]))
      BY <1>1, <1>7, CoverSemmanticCoRight
   <2>3. CwDist(x, RightCover(lset[x])) <  CwDist(x, RightNeighbor(lset[x]))
      BY <1>1, NoPartition, NeighborConventionRight, Invariant
   <2>4. CwDist(x, y) < CwDist(x, RightNeighbor(lset[x]))
      BY <2>3, <2>1, TransLESS, 
         CwDistType, RightCoverType, RightNeighborType, IisNat
   <2>5. ~(CwDist(x, y) < CwDist(x, RightNeighbor(lset[x])))
      BY <1>1, Neighborhood, Invariant
   <2>9. QED BY <2>5,<2>4
<1>8. CASE Covers(lset[y], x) /\ CwDist(x, y) = AbsDist(x, y)
\* similar to <1>6, exchange x and y
   <2>1. CwDist(x, y) =< CwDist(LeftCover(lset[y]), y)
      BY <1>1, <1>8, CoverSemmanticCoLeft, AbsCommutativity, IisNat
   <2>2. CwDist(LeftCover(lset[y]), y) < CwDist(LeftNeighbor(lset[y]), y)
      BY  <1>1, NoPartition, NeighborConventionLeft, Invariant
   <2>3. CwDist(x, y) < CwDist(LeftNeighbor(lset[y]), y)
      BY <2>1, <2>2, TransLESS,
      CwDistType, LeftCoverType, LeftNeighborType, IisNat
   <2>4. ~(CwDist(x, y) < CwDist(LeftNeighbor(lset[y]), y))
      BY <1>1, Neighborhood, Invariant
   <2>9. QED BY <2>3, <2>4
<1>9. QED BY <1>1,<1>5,<1>6,<1>7,<1>8, AbsIsLeftOrRight

THEOREM ConsistentInv == 
TypeInvariant /\ Invariant =>  
\A x, y, k \in I: 
   (   status[x] = "ready"   
    /\ Covers(lset[x], k)
    /\ status[y] = "ready"
    /\ Covers(lset[y], k)
    )
    => x = y
\* Proof by contradiction. Assume k is covered both by x and y prove FALSE
\* We can derive from Coveragelemma that k must be in the middle of x and y
\* Then, by proving the neighborhood of x and y (see next comment), we can deduce that k 
\* cannot be shared by two neighbors x and y. QED
<1>1. SUFFICES ASSUME NEW x \in I, 
                      NEW y \in I, 
                      NEW k \in I,
      status[x] = "ready",
      status[y] = "ready",
      Covers(lset[x], k),
      Covers(lset[y], k),
      TypeInvariant, 
      Invariant,
      ~(x = y)
      PROVE FALSE
   BY DEF Covers
<1>. \A i \in I: lset[i] \in LSet
   BY TypeInvariant DEF TypeInvariant
<1>11. ~Covers(lset[x], y) /\ ~Covers(lset[y], x)
   BY <1>1, NotCovers
<1>2. AbsDist(x, k) =< AbsDist(y, k) 
   BY <1>1, CoverageLemma
<1>3. AbsDist(y, k) =< AbsDist(x, k)
   BY <1>1, CoverageLemma
<1>4. AbsDist(x, k) = AbsDist(y, k)
   BY <1>2,<1>3, Antisymmetry, AbsDistType, IisNat
<1>5. CASE AbsDist(x, k) = CwDist(x, k) /\ AbsDist(y, k) = CwDist(y, k)
   BY <1>5, <1>4, CwDistInjectivity, ~(x = y), IisNat
<1>6. CASE AbsDist(x, k) = CwDist(x, k) /\ AbsDist(y, k) = CwDist(k, y)
   <2>1. CwDist(x, y) = CwDist(x, k) + CwDist(k, y)
      <3>1. Distance(k, x) < 0 /\ Distance(y, k) < 0
         BY <1>6, AbsDistRightSide, AbsDistLeftSide, IisNat 
      <3>2. QED BY <3>1,  ~(x=y), RingAddProp, IisNat
   <2>2. RightNeighbor(lset[x]) = y
   \* Proof sketch: assume there is another node z to be the right neighbor of x
   \* then try to derive FALSE
   \* We know that no "ready" node could stay between a node and its direct neighbor 
   \* according to Neighborhood. Then we will derive that z lies between x and y.(*)
   \* We know by assumption that x covers k and k between x and its right cover by <2>1.
   \* (left dist from x to k) is less than the left distance from x to the left cover of z by CoverDisjointnessCo
   \* BY CoverMonotony, we know that left dist from x to left cover of z is less than 
   \* the left dist from x to left cover of y, because z lies between x and y. (<3>4)
   \* Transitivity tells us that (left dist from x to k) is less than left dist from x to left cover of y.
   \* Hence, we know k is outside the left coverage of y. On the otherside, we know k
   \* lies to the right of x and y shouldn't be covered by x, so k is even further to the right and hence
   \* not in the right coverage of y.
   \* Hence, k is not covered by y. Contradiction.
      <3>1. SUFFICES ASSUME NEW z \in I, 
            RightNeighbor(lset[x]) = z,
            ~(z = y)
            PROVE FALSE
         BY IisNat, RightNeighborType
      <3>11. x # z
         BY <1>1, <3>1, NoPartition
      <3>2. CwDist(x, k) < CwDist(x, LeftCover(lset[z]))
         BY CoverDisjointnessCo, <3>11, RightNeighbor(lset[x]) = z, <1>6, Covers(lset[x], k), TypeInvariant
      <3>3. CwDist(x, z) < CwDist(x, y)
         <4>6.  ~(CwDist(x, z) = CwDist(x, y))
            BY ~(z = y), RightDistInjectivity, IisNat
         <4>8. ~(CwDist(x, z) > CwDist(x, y))
            <5>2. ~(CwDist(x, y) < CwDist(x, z))
               BY <1>1, Neighborhood, Invariant, RightNeighbor(lset[x]) = z, StatusDuality
            <5>3. QED BY <5>2, LessGreaterDuality, CwDistType, IisNat
         <4>9. QED BY <4>6, <4>8, Unequality23, CwDistType, IisNat
      <3>4. CwDist(x, LeftCover(lset[z])) =< CwDist(x, LeftCover(lset[y]))
         BY CoverMonotony, <3>3, RightNeighbor(lset[x]) = z,
         status[x] = "ready", status[y] = "ready", ~x=y, z#y, TypeInvariant, Invariant
      <3>5. CwDist(x, k) < CwDist(x, LeftCover(lset[y]))
         BY <3>2,<3>4,TransLESS, CwDistType, LeftCoverType, IisNat 
      <3>6. CwDist(y, k) > CwDist(y, RightCover(lset[y]))
         <4>7. CwDist(y, k) >= CwDist(y, x) 
            BY CwDistSideProp, <1>6, IisNat, LessGreaterDuality2
         <4>8. CwDist(y, x) > CwDist(y, RightCover(lset[y]))
            BY <1>11, CoverSemmanticCo, TypeInvariant
         <4>9. QED BY <4>7, <4>8, TransGEATER, CwDistType, RightCoverType, IisNat
      <3>7. CwDist(k, y) > CwDist(LeftCover(lset[y]), y)
         BY <3>5, <1>11, CoverSemmanticCo, CwDistPropAddCo, 
         LeftCoverType, CwDistType, IisNat, TypeInvariant
      <3>8. ~Covers(lset[y], k)
         BY <3>7, <3>6, CoverSemmanticCo, TypeInvariant
      <3>9. QED BY <3>8, <1>1
   <2>10. QED BY <1>1, <2>2, RightNeighborCoverageDis
<1>7. CASE AbsDist(x, k) = CwDist(k, x) /\ AbsDist(y, k) = CwDist(y, k)
   \* symmetric to <1>6, simply switch x and y, change <1>6 to <1>7. COULD BE AUTOMATICALLY PROVEN!!!
   <2>1. CwDist(y, x) = CwDist(y, k) + CwDist(k, x)
      <3>1. Distance(x, k) < 0 /\ Distance(k, y) < 0
         BY <1>7, ~(x=y), AbsDistRightSide, AbsDistLeftSide, IisNat 
      <3>2. QED BY <3>1,  ~(x=y), RingAddProp, IisNat
   <2>2. RightNeighbor(lset[y]) = x
      <3>1. SUFFICES ASSUME NEW z \in I, 
            RightNeighbor(lset[y]) = z,
            ~(z = x)
            PROVE FALSE
         BY IisNat, RightNeighborType
      <3>11. y # z
         BY <1>1, <3>1, NoPartition
      <3>2. CwDist(y, k) < CwDist(y, LeftCover(lset[z]))
         BY CoverDisjointnessCo, <3>11, RightNeighbor(lset[y]) = z, <1>7, Covers(lset[y], k), TypeInvariant
      <3>3. CwDist(y, z) < CwDist(y, x)
         <4>6.  ~(CwDist(y, z) = CwDist(y, x))
            BY ~(z = x), RightDistInjectivity, IisNat
         <4>8. ~(CwDist(y, z) > CwDist(y, x))
            <5>2. ~(CwDist(y, x) < CwDist(y, z))
               BY <1>1, Neighborhood, Invariant, RightNeighbor(lset[y]) = z, StatusDuality
            <5>3. QED BY <5>2, LessGreaterDuality, CwDistType, IisNat
         <4>9. QED BY <4>6, <4>8, Unequality23, CwDistType, IisNat
      <3>4. CwDist(y, LeftCover(lset[z])) =< CwDist(y, LeftCover(lset[x]))
         BY CoverMonotony, <3>3,RightNeighbor(lset[y]) = z, <1>1, <3>1,IisNat,EqualCommutativity,
          status[x] = "ready", status[y] = "ready"
      <3>5. CwDist(y, k) < CwDist(y, LeftCover(lset[x]))
         BY <3>2,<3>4,TransLESS, CwDistType, LeftCoverType, IisNat 
      <3>6. CwDist(x, k) > CwDist(x, RightCover(lset[x]))
         <4>7. CwDist(x, k) >= CwDist(x, y) 
            BY CwDistSideProp, <1>7, IisNat, LessGreaterDuality2
         <4>8. CwDist(x, y) > CwDist(x, RightCover(lset[x]))
            BY <1>11, CoverSemmanticCo, TypeInvariant
         <4>9. QED BY <4>7, <4>8, TransGEATER, CwDistType, RightCoverType, IisNat
      <3>7. CwDist(k, x) > CwDist(LeftCover(lset[x]), x)
         BY <3>5, <1>11, CoverSemmanticCo, CwDistPropAddCo, LeftCoverType, CwDistType, IisNat, TypeInvariant
      <3>8. ~Covers(lset[x], k)
         BY <3>7, <3>6, CoverSemmanticCo, TypeInvariant
      <3>9. QED BY <3>8, <1>1
   <2>10. QED BY <1>1, <2>2, RightNeighborCoverageDis
<1>8. CASE AbsDist(x, k) = CwDist(k, x) /\ AbsDist(y, k) = CwDist(k, y)
\* symmetric to <1>5
   BY <1>8, <1>4, RightDistInjectivity, ~(x = y), IisNat
<1>9. QED BY <1>5, <1>6,<1>7,<1>8, AbsIsLeftOrRight

THEOREM CoverDisjoint ==
   TypeInvariant/\ Invariant => \A i, j, k \in I: 
      /\status[i]= "ready" 
      /\status[j]= "ready"
      /\ Covers(lset[i], k) 
      /\ ~(j=i) 
    =>  ~Covers(lset[j], k)
BY ConsistentInv
-------------------------------------------------------------------------------------------------------------------------------
THEOREM CompleteCoverage ==
\A k \in I: \E i \in I: status[i] = "ready" /\ CwDist(LeftCover(lset[i]), k) =< CwDist(LeftCover(lset[i]), RightCover(lset[i]))
\* TODO Next
(*
   \A i, k \in I:
      /\status[i] = "ready"
      /\ ~(CwDist(LeftCover(lset[i]), k) =< CwDist(LeftCover(lset[i]), RightCover(lset[i])))
      => \E n \in I: 
            /\ ~ (n = i)
            /\ status[n] = "ready"
            /\ CwDist(LeftCover(lset[n]), k) =< CwDist(LeftCover(lset[n]), RightCover(lset[n]))
            *)
\* System Theorems
THEOREM ConsistencyTheorem == Spec => Consistency
(* 
   /\ Spec => TypeInvariant
   /\ Spec /\ TypeInvariant => Invariant
   /\ Spec /\ TypeInvariant /\ Invariant => ConsistentInv
*)
THEOREM CorrectNessTheorm == Spec => Correctness
(* 
   /\ Spec => TypeInvariant
   /\ Spec /\ TypeInvariant => Invariant
   /\ Spec /\ TypeInvariant /\ Invariant => CorrectDelivery
*)

=============================================================================
\* Modification History
\* Last modified Wed Mar 21 17:14:42 CET 2012 by tianlu
\* Last modified Tue Feb 15 21:38:19 CET 2011 by tianlu
\* Last modified Mon Feb 14 17:20:33 CET 2011 by merz
\* Last modified Mon Feb 14 17:19:23 CET 2011 by merz
\* Last modified Wed Oct 20 10:09:06 CEST 2010 by tianlu
\* Last modified Tue Oct 19 15:10:33 CEST 2010 by merz
\* Last modified Mon Oct 04 11:43:39 CEST 2010 by tianlu
\* Last modified Sun Oct 03 15:39:58 CEST 2010 by merz
\* Created Fri Sep 17 12:22:37 CEST 2010 by tianlu
