--------------------------- MODULE ProofBasic ---------------------------
(* The hierarchy of the Proofs are
ProofBasic
  \subset ProofRingProp (The basic parameters and operations for ring calculation)
   \subset ProofLSetProp (The leaf set local properties of data structure)
    \subset ProofType (The Proof of TypeInvariant)
     \subset ProofLSetInv (The proof of Invariant of Leaf Set properties)
      \subset ProofProp (The reduction proof from Correctness properties
                         of Pastry to a list of Leaf Set properties)
*)
EXTENDS TLAPS, MSPastry, Actions, SequencesTheorems

\* Assumptions
AXIOM EmptySetSize == Cardinality({}) = 0
AXIOM EmptySet == 1..0 = {}
AXIOM CardinalityType == \A s \in SUBSET I: Cardinality(s) \in Nat
THEOREM NatZeroOrGeq1 == \A n \in Nat: n # 0 => n >= 1
BY Arithmetic
\* Arithmatics
LEMMA DivType == \A x, y \in Nat: x \div y \in Nat
LEMMA DivZero == \A x \in Nat: 0 \div x = 0
LEMMA TransLESS == \A x, y, z \in Nat: \/(x =< y /\ y < z) 
                                       \/(x < y /\ y =< z)
                                       \/(x < y /\ y < z) 
                                      => x < z
LEMMA SuccessorUnequal == \A i \in Nat: ~(i + 1 = i)                                     
LEMMA TransLEQ == \A x, y, z \in Nat: x =< y /\ y =< z => x =< z
LEMMA Antisymmetry == \A a, b \in Nat: a=< b /\ b =< a => a = b
LEMMA CommutativityAdd == \A x, y \in Nat: x + y = y + x
LEMMA MonotonyAdd == \A a, b, c \in Nat: a + b =< a + c <=> b =< c 
LEMMA MonotonyAddCo == \A a, b, c \in Nat: a + b =< c + b => a =< c
LEMMA MonotonyAddNeg == \A a, b, c \in Nat: a+ b > a + c <=> b > c
LEMMA MonotonyDiv == \A a, b, c \in Nat: a =< b => a \div c =< b \div c
LEMMA LessAddRel == \A a, b, c \in Nat: a = b + c /\ b=1=> b < a /\ c < a
LEMMA LessAddRel2 == \A x, y \in Nat: x < y => \E z \in Nat: ~(z = 0) /\ x + z = y
LEMMA Unequality2 == \A a, b \in Nat: ~ (a =< b) <=> b < a
LEMMA Unequality22 == \A a, b \in Nat: ~(a <  b) <=> a >=b 
LEMMA Unequality23 == \A a, b \in Nat: ~(a =b) /\ ~(a>b) <=> a< b
LEMMA Unequality3 == \A a, b \in Nat: a =< b <=> ~(a > b)
LEMMA LessGreaterDuality == \A a, b \in Nat: a < b <=> b > a
LEMMA LessGreaterDuality2 == \A a, b \in Nat: a=< b <=> b>= a
LEMMA Unequality5 == \A a, b, c \in Nat: a + b = c => (a =< b <=> a =< c \div 2)
LEMMA Unequality6 == \A a, b \in Nat: a =< b <=> (a = b) \/ a< b
LEMMA TransGEATER ==  \A x, y, z \in Nat: \/(x >= y /\ y > z) 
                                       \/(x > y /\ y >= z)
                                       \/(x > y /\ y > z) 
                                      => x > z
LEMMA DivLess == \A x, y \in Nat: 
                        /\ y # 0 
                        /\ x= y \div 2 \/ x =<y \div 2 
                        => x < y
LEMMA BiggerThan == \A a, b, c \in Nat: a = b+c /\ c> 0 => a>b 
LEMMA EqualCommutativity == \A x, y \in Nat: x = y <=> y = x

\* Cardinality
LEMMA RemoveOneNodeCar == \A a, b: Cardinality(a \{b}) =< Cardinality(a) 
LEMMA CardinalityOneNode == \A i \in I: Cardinality({i}) =1
LEMMA CardinalityOneNodeCo == \A s \in SUBSET I: Cardinality(s) = 1 => \E j \in I: s = {j}
LEMMA CardinalityOneNodeCoCo == \A s \in SUBSET I: \A i \in s: Cardinality(s) = 1 => s \ {i} = {}
\* this cannot be proved
LEMMA CardinalityTwoNode == \A i, j \in I, a \in SUBSET I: i \in a /\ j \in a /\ i#j => ~(Cardinality(a)=< 1) 
LEMMA CardinalityEmptySet == \A s: Cardinality(s) < 1 <=> s = {}
LEMMA CardinalitySimplfy1 == \A a \in SUBSET I: 
                Cardinality(a) =< L 
             <=> Cardinality(a) < L \/ Cardinality(a) = L 
LEMMA CardinalityL == \A a, b \in SUBSET I: 
                 /\ Cardinality(a) > L + 1 
                 /\ a  \in SUBSET b
                 => ~Cardinality(b) =<1
LEMMA CardinalityLess == \A a \in SUBSET I, i \in I: Cardinality(a) < L => Cardinality(a \cup {i}) =< L
LEMMA CardinalityUnion == \A a, b: Cardinality(a \cup b) =< Cardinality(a) + Cardinality(b)
LEMMA CardinalityTrans == \A a, b, k: Cardinality(a) =< Cardinality(b) /\ Cardinality(b) =< k
                           => Cardinality(a) =< k
LEMMA CardinalityRemove == \A S: \A s \in S: s \in S /\ Cardinality(S) =< 1 => S \{s} = {}
LEMMA SingleNode == \A a \in SUBSET I, i \in I: i \in a /\ Cardinality(a) = 1 <=> a = {i}


============================================================================= 
