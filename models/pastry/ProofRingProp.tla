--------------------------- MODULE ProofRingProp ---------------------------
(* The hierarchy of the Proofs are
ProofBasic
  \subset ProofRingProp (The basic parameters and operations for ring calculation)
   \subset ProofLSetProp (The leaf set local properties of data structure)
    \subset ProofType (The Proof of TypeInvariant)
     \subset ProofLSetInv (The proof of Invariant of Leaf Set properties)
      \subset ProofProp (The reduction proof from Correctness properties
                         of Pastry to a list of Leaf Set properties)
*)
EXTENDS ProofBasic

\* Assumptions

AXIOM EnoughReadyNodes == Cardinality(A)> 0 /\ ~(Cardinality(A)<1)
AXIOM OneLESS2L == 1 \leq L
AXIOM LType == L \in Nat
AXIOM Lmin == L >0
AXIOM LenEmpty == Len(<<>>) = 0
AXIOM AbsMinimal == \A k \in I, can \in SUBSET I: ~can = {}
        => \E n \in can: \A m \in can: AbsDist(n, k) =< AbsDist(m, k)
AXIOM CwMaximal == \A k \in I, can \in SUBSET I: ~can = {}
        => \E n \in can: \A p\in can: CwDist(p, k)>=CwDist(n, k)
AXIOM DistMinimal == \A can \in SUBSET I: ~can = {}
        => \E n \in can: \A m \in can: Distance(m, n) < 0 \/ n = m

THEOREM AType == A \in SUBSET I 
\*THEOREM AType == A \in I
THEOREM CwDistType == \A x, y \in Nat: CwDist(x, y) \in Nat
THEOREM AbsDistType == \A x, y \in Nat: AbsDist(x, y) \in Nat

--------------------------------------------------------------

\* Properties of Ring
THEOREM IisNat== \A i \in I: i \in Nat
        \* BY assumption in Ring.tla:  I \in SUBSET Nat 
THEOREM OneDistance == \A x, y, z \in Nat: CwDist(x, z) < CwDist(x, y) => CwDist(x, z) + 1 =< CwDist(x, y)
THEOREM AbsIsLeftOrRight == \A x,y \in I : AbsDist(x,y) \in {CwDist(x,y), CwDist(y,x)}
THEOREM AbsDistRightSide == \A x, y \in Nat: AbsDist(x, y) = CwDist(y, x) => Distance(x, y)<0
THEOREM AbsDistLeftSide == \A x, y \in Nat: AbsDist(x, y) = CwDist(x, y) => Distance(y, x)<0
THEOREM AbsShortest == \A x, y \in Nat: \* absolute distance is always shorter than any kind of distances 
           AbsDist(x, y) =< CwDist(x, y) /\ AbsDist(x, y) =< CwDist(y, x)     
THEOREM AbsCommutativity == \A x, y \in Nat: AbsDist(x, y) = AbsDist(y, x)
\*THEOREM DistDuality == \A x, y \in Nat: CwDist(x, y) = CwDist(y, x)
THEOREM PassThrough == 
TypeInvariant => 
     \A x, y, i \in Nat: AbsDist(x, i) = CwDist(x, i)/\ AbsDist(i, y) = CwDist(i, y) 
                => CwDist(x, i) =< CwDist(x, y)
THEOREM RingCompleteness == \A x, y \in Nat: CwDist(x, y) + CwDist(y, x) = RingCap
THEOREM SideDuality == \A x, y \in Nat: Distance(x, y) < 0 <=> ~(Distance(y, x) < 0)
THEOREM RingComposite == \A a, b, c, d \in Nat: CwDist(a, d) = CwDist(a, b) + CwDist(b, c) + CwDist(c, d)
                         => CwDist(b, d) = CwDist(b, c) + CwDist(c, d) 
THEOREM RingLEQSemmantic == \A x, y, i \in Nat:
                      CwDist(x, i) =< CwDist(x, y)
                       <=> CwDist(x, y) = CwDist(x, i) + CwDist(i, y) 
THEOREM RingLEQSemmanticCo == \A x, y, i \in Nat:
                      CwDist(i, y) =< CwDist(x, y)
                       <=> CwDist(x, y) = CwDist(x, i) + CwDist(i, y) 
THEOREM RingGEQSemmantic == \A a, b, c \in Nat:
                      CwDist(a, c) >= CwDist(a, b) 
                       <=> CwDist(a, c) = CwDist(a, b) + CwDist(b, c)
THEOREM RingGEQSemmanticCo == \A a, b, c \in Nat:
                      CwDist(a, c) >= CwDist(b, c) 
                       <=> CwDist(a, c) = CwDist(a, b) + CwDist(b, c)
THEOREM CwDistProp == \A x, i, y \in Nat: 
                          CwDist(x, i) < CwDist(x, y) 
                      <=> CwDist(i, y) =< CwDist(x, y) 
THEOREM CwDistPropCo == \A x, i, y \in Nat: 
                          CwDist(i, y) < CwDist(x, y) 
                      <=> CwDist(x, i) =< CwDist(x, y) 
THEOREM CwDistSideProp == \A x, y, k \in Nat: 
               AbsDist(x, k) = CwDist(x, k)/\ AbsDist(y, k) = CwDist(k, y)
               => CwDist(k, x) >= CwDist(y, x) /\ CwDist(y, k) >= CwDist(y, x)  
THEOREM CwDistPropAdd == \A a, b, c, d \in Nat: 
                         /\ CwDist(a, b) < CwDist(a, d)
                         /\ CwDist(c, d) < CwDist(b, d)
                    => CwDist(a, c) < CwDist(a, d) /\ CwDist(a, b) < CwDist(a, c)
THEOREM CwDistRing == \A a, b, c \in Nat:
           CwDist(a, b) < CwDist(a, c) => CwDist(c, b) > CwDist(c, a)
THEOREM CwDistRingCo == \A a, b, c \in Nat:
           CwDist(a, b) =< CwDist(a, c) => 
                     /\CwDist(a, b) =< CwDist(c, b)
                     /\CwDist(b, c) =< CwDist(b, a)
THEOREM CwDistRingCo2 == \A a, b, c \in Nat:
           CwDist(b, c) =< CwDist(a, c)
            => CwDist(a, b) =< CwDist(c, b)/\ CwDist(b, c) =< CwDist(b, a)
THEOREM CwDistPropAddCo == \A a, b, c, d \in Nat:
            /\CwDist(a, b) < CwDist(a, c) 
            /\ CwDist(a, d) > CwDist(c, d)
            => CwDist(b, d) > CwDist(c, d)
THEOREM CwDistPropAddCo2 == \A a, b, c, d \in Nat:
            CwDist(a, b) =< CwDist(a, c)
            => (CwDist(b, c) =< CwDist(b, d) <=> CwDist(a, c) =< CwDist(a, d))            
THEOREM   RingAddProp == \A x, i, y \in Nat: Distance(i, x)< 0 /\ Distance(y, i) < 0/\ ~(x=y)
\* If i is the opposite node of x, and x is y. Then, we have 0 on the left side and 2^E on the right side
                          => CwDist(x, y) = CwDist(x, i) + CwDist(i, y)
THEOREM CwDistInjectivity == \A x, y, k \in Nat: CwDist(x, k) = CwDist(y, k) => x = y
THEOREM RightDistInjectivity == \A x, y, k \in Nat: CwDist(k, x) = CwDist(k, y) => x = y       
THEOREM ToTheRightOfProp == \A n, i \in I: 
           Distance(n, i) < 0 <=> 2 * CwDist(i, n) < RingCap

THEOREM CwDistCalculation1 == 
  \A i, n, m \in Nat: CwDist(i, (n + CwDist(i,n)\div 2 + 1)%RingCap) =<  CwDist(i, n) \div 2

THEOREM CwDistCalculation2== 
  \A i, n, m \in Nat: CwDist((i + CwDist(n,i)\div 2)%RingCap, i) =  CwDist(n, i) \div 2     
THEOREM CwDistCalculation3 == 
 \A a, b, c \in Nat: CwDist(a, b) + CwDist(b, c) = CwDist(a, c) /\ CwDist(b, c) = CwDist(a, c) \div 2 
                => CwDist(a, b) >= CwDist(a, c) \div 2
THEOREM CwDistCalculation4 == 
 \A x, y, z\in Nat: CwDist(z, y) =< CwDist(x, y) \div 2 => 
               CwDist(x, y) \div 2 =< CwDist(x, z)
THEOREM CwDistZero == \A x, y \in Nat: CwDist(x, y) = 0 <=> x = y
THEOREM CwDistZeroCo == \A x, y \in Nat:  CwDist(x, y) >0 <=> x # y
THEOREM CwDistZeroExt == \A x, y, z \in Nat: CwDist(y, z) >0 => CwDist(x, z) > CwDist(x, y)
THEOREM CwDist5Postions == \A a, b, c, d, e \in Nat: 
              /\ CwDist(b, c) =< CwDist(a, c)
              /\ CwDist(b, c) =< CwDist(b, d)
              /\ CwDist(c, d) =< CwDist(c, e)
            => CwDist(a, c) =< CwDist(a, e) 
THEOREM CwDistMonotonyDivCo == 
   \A x, y, z, k \in Nat:
     /\ CwDist(x, k) =< (CwDist(x, z) + 1) \div 2
     /\ CwDist(x, z) + 1 =< CwDist(x, y)
    => CwDist(x, k) =< CwDist(x, y) \div 2

THEOREM RingRange ==
  \A i, lm, rm, k \in I: 
   ~(/\ CwDist(i, k) > CwDist(i, rm) 
     /\ CwDist(k, i) > CwDist(lm, i))
   => /\ CwDist(i, k) =< CwDist(i, rm)
      /\ CwDist(k, i) =< CwDist(lm, i)
  
=============================================================================
\* Modification History
\* Last modified Thu Apr 07 15:33:25 CEST 2011 by tianlu
\* Created Mon Dec 13 12:13:20 CET 2010 by tianlu
