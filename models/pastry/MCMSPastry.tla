-------------------------- MODULE MCMSPastry ---------------------------
\* This is the model checking module, only used for model checking
(* The hierarchy of the modules are
 Ring (The basic parameters and operations for ring calculation)
   \subset LS (The leaf set utilities)
      \subset RT (The routing table utilities)
         \subset Msg (The messages definitions)
            \subset InitialStates (The initial state and TypeInvariant)
               \subset Actions (All the actions)
                 \subset MSPastry (The specification of MSPastry including propertie
                   \subset MCMSPastry (The model checking file)                  
*)
(* The hierarchy of the Proofs are
 ProofBasic  
  \subset ProofRingProp (The basic parameters and operations for ring calculation)
   \subset ProofLSetProp (The leaf set local properties of data structure)
    \subset ProofProp (reductions)
     \subset ProofType (The Proof of TypeInvariant)
      \subset ProofLSetInv (The proof of Invariant of Leaf Set properties)
*)
EXTENDS MSPastry 
------------------------------------------------------------------------
\* Demo Assignment
MCI == {17, 55, 65, 70, 95} \* We model checking 5 nodes system 
MCA == {17} \* Initial READY node is 17
MCB == 4 \* base is 2^4
MCM == 8 \* ID space is 2^8
MCL == 2 \* leaf set length is 2, left one node, right one node
LightNext == \E i, j \in I:
      \/ RouteJoinRequest(i, j) 
      \/ ReceiveLSProbe(i)
      \/ ReceiveLSPrRpl(i) 
      \/ ReceiveJoinRequest(i)
      \/ ReceiveJoinReply(i)
      \/ RequestLease(i)
      \/ ReceiveLReq(i)
      \/ ReceiveBLS(i)
      \/ Deliver(i, j)
      \/ RouteLookup(i, j) 
      \* followed are application (interface) actions:
      \*\/ Join(i, j)
      \*\/ Lookup(i, j)
      (*
      \/ LeaseExpired(i, j)
      \/ GrantExpired(i, j)
      \/ NodeLeft(i)
      \/ SuspectFaulty(i, j)
      \/ ProbeTimeOut(i, j)
      \/ DeclareDead(i, j)
      \/ LSRepair(i)
      \/ Recover(i)
      \*\/ Restart(i)
      \/ ResignNode(i)
      *)
JNext == \E i, j \in I:
      \/ RouteJoinRequest(i, j) 
      \/ ReceiveLSProbe(i)
      \/ ReceiveLSPrRpl(i) 
      \/ ReceiveJoinRequest(i)
      \/ ReceiveJoinReply(i)
      \/ RequestLease(i)
      \/ ReceiveLReq(i)
      \/ ReceiveBLS(i)
-------------------------------------------------------
\* The following are liveness properties and their specification configurations
\* Successful Lookup
MCALookup == {17, 55, 65}
LookupNext == \/ Lookup(17, 95)
              \/ LightNext
SpecSuccessLookup ==
/\ Init 
/\ [][LookupNext]_vars
NeverDeliver == [][\A i, j \in I: ~Deliver(i, j)]_vars
--------------------------------------------------------------
(*Successful join*)
JoinNext == \/ Join(95, 17)
            \/ JNext
SpecSuccessJoin == 
/\ Init 
/\ [][JoinNext]_vars
NeverJoin == [](\A j \in I \ A: status[j]#"ready") 
-------------------------------------------------------
\* Successful Concjoin, used also for finding faulty properties.

MCCJA == {17, 95}
CJNext ==  \/ Join(65, 95)
           \/ Join(55, 17)
           \/ JNext
SpecConcJoin == 
/\ Init 
/\ [][CJNext]_vars
ConcurrentJoin == []~(status[95] = "ready" 
                          /\status[17] = "ready"
                          /\status[65]= "ready" 
                          /\status[55]= "ready")
---------------------------------------------------------
\* Successful Concjoin and then lookup
CcJoinDeliverNext == \/ Join(95, 17)
                     \/ Join(55, 17)
                     \/ Lookup(95, 65)
                     \/ LightNext
SpecCcJoinDeliver == 
/\ Init 
/\ [][CcJoinDeliverNext]_vars
CcJoinDeliver ==[][~\E i, j \in I: Deliver(i, j) 
                          /\status[95]= "ready" 
                          /\status[17]= "ready" 
                          /\status[55]= "ready"]_vars
--------------------------------------------------------
SymmNext == \/ Join(95, 17)
            \/ Join(55, 17)
            \/ Join(65, 95)
            \/ JNext

SpecSym ==
/\ Init 
/\ [][SymmNext]_vars
Symmetry == 
\A i, j \in I: 
   /\ status[i] = "ready" 
   /\ status[j] = "ready"
   =>
    (j \in GetLSetContent(lset[i]) 
        <=> i \in GetLSetContent(lset[j]))
    \* The membership of leaf set is symmetric between two stable nodes
    \* this is violated when someone j tries to join and be added into one of the
    \* pair, say i and push n out of i's leaf set. While n still have i in its leaf set
    \* before he knows this new comer j.  
SymmetryWeak == 
\A i, j \in ReadyOK:
    i \in GetLSetContent(lset[j]) => 
       \/j \in GetLSetContent(lset[i]) 
       \/ /\ CwDist(i, j) > CwDist(i, RightMost(lset[i])) 
          /\ CwDist(j, i) > CwDist(LeftMost(lset[i]), i)
---------------------------------------------------------
\* Faulty Properties Demo

MCANCF == {17, 95}
NCFNext == \/ Join(65, 95)
           \/ Join(55, 17)
           \/ JNext
SpecNCF ==
/\ Init 
/\ [][NCFNext]_vars

Neighbor == 
  \/ Cardinality(ReadyOK) =< 1
  \/ \A x, y \in ReadyOK: 
     ~(x = y) => 
     /\ CwDist(LeftNeighbor(lset[x]), x)  =< CwDist(y, x)
     /\ CwDist(x, RightNeighbor(lset[x])) =< CwDist(x, y)

NeighborProp == HalfNeighbor /\ NeighborClosest
\* no other node could be closer to a node than its neighbor
---------------------------------------------    
OKNext == \/ Join(95, 17)
           \/ Join(55, 17)
           \/ Join(65, 95)
           \/ JNext     
SpecOK==
/\ Init 
/\ [][OKNext]_vars        

OKNodesExlusion1 ==
~(\E a, b, c \in ReadyOK: 
   /\a \in GetLSetContent(lset[c]) 
   /\c \in GetLSetContent(lset[a])
   /\~b \in GetLSetContent(lset[c]) 
   /\~b \in GetLSetContent(lset[a]))
OKNodesExlusion2 ==
~(\E a, b, c \in ReadyOK:
   /\b \in GetLSetContent(lset[c]) 
   /\c \in GetLSetContent(lset[b])
   /\CwDist(a, b) < CwDist(a, c)
   /\CwDist(a, c) < CwDist(a, RightNeighbor(lset[a])))
   
OKInv == OKNodesExlusion1 /\ OKNodesExlusion2
---------------------------------------------------------
\* invariant model checking
SpecInvariantCheck ==
/\ Init 
/\ [][SymmNext]_vars
---------------------------------------------------------
\* debugging 
DemoDebugProp == []~\E m \in receivedMsgs: m.destination=95 /\ m.mreq.type = "BroadcastLSet" 
DemoDebugProp1 == []~(17 \in lease[95])

DemoProp == SymmetryWeak 
=======================================================================
