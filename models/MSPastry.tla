-------------------------- MODULE MSPastry ---------------------------
\* This is the specification of MSPastry
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
\* This version is based on the paper Castro04, Haeber06 
\* and the source codes from www.FreePastry.com
EXTENDS Actions
----------------------------------------------------------------------
\* here are all the global variables
vars == <<receivedMsgs, status, rtable, lset, probing, failed, lease, grant>>

  
NodesOK == {i \in I : status[i] = "ok"}
NodesReady == {i \in I : status[i] = "ready" }
NodesWait == {i \in I : status[i] = "wait" }
ReadyOK == NodesOK \union NodesReady
NonDead == {i \in I : status[i] # "dead" }
\* here are all possible actions to be applied for next step
Next == \E i, j \in I:
      \/ RouteLookup(i, j) 
      \/ RouteJoinRequest(i, j) 
      \/ Deliver(i, j)
      \/ ReceiveLSProbe(i)
      \/ ReceiveLSPrRpl(i) 
      \/ ReceiveJoinRequest(i)
      \/ ReceiveJoinReply(i)
      \/ RequestLease(i)
      \/ ReceiveLReq(i)
      \/ ReceiveBLS(i)
      \* followed are application (interface) actions:
      \/ Lookup(i, j)
      \/ Join(i, j)
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
Spec == \* The general specification of MSPastry
/\ Init 
/\ [][Next]_vars
----------------------------------------------------------------------------------
\* Properties 

LSetInv == \A i \in I: ~i \in (lset[i].left) /\ ~i \in (lset[i].right) 
Stable == \*A node is stable ("ok" or "ready") iff
\*its leaf set is complete or there are not enough nodes to complete any leaf set
\* This is not used for Theorem Proving and not proved, 
\* but MC hasn't found Counter Example till depth 21
  \/ Cardinality(ReadyOK) =< L
  \/ \A i \in ReadyOK : IsComplete(lset[i])
  
\* no other node could be closer to a node than its neighbor 
NeighborClosest == 
  \/ Cardinality(NodesReady) =< 1
  \/ \A x, y \in NodesReady: 
     ~(x = y) => 
     /\ CwDist(LeftNeighbor(lset[x]), x)=< CwDist(y, x)
     /\ CwDist(x, RightNeighbor(lset[x])) =< CwDist(x, y)
HalfNeighbor == 
  \/ \A k \in ReadyOK : 
      /\ RightNeighbor(lset[k]) # k 
      /\ LeftNeighbor(lset[k]) # k
  \/ \E k \in ReadyOK:
     /\ ReadyOK = {k} 
     /\ LeftNeighbor(lset[k]) = k 
     /\ RightNeighbor(lset[k]) = k
--------------------------------------------------------------------------------
ReadyNeighbor == 
\* Does not hold, found counter Example in vI log/HN-RN-IN.log
\A i \in ReadyOK, j \in NodesReady:
     ~(i = j) => 
     /\ CwDist(LeftNeighbor(lset[i]), i)=< CwDist(j, i)
     /\ CwDist(i, RightNeighbor(lset[i])) =< CwDist(i, j)
     /\ CwDist(LeftNeighbor(lset[j]), j)=< CwDist(i, j)
     /\ CwDist(j, RightNeighbor(lset[j])) =< CwDist(j, i)   

(*
NeighborClosestRight == 
\* This does not hold by First Join Last ProbeReply case
\* let node a, b, c, d \in I lies in the written order clockwise on a ring.
\* d is ready and b joins the ring by d
\* After d replies b with itself in the leaf set, b updates its leaf set with d and probe d
\* Before d received the probe, a and c joins the ring by d and completes the 
\* consistent join phrase and recognize each other as direct neighbors. 
\* Then a and c get the grands from c and a and d to become ready, while b is still waiting for the probe reply.
\* Now b's neighbor is d but a and c are closer to it and ready.
\* Hence, b's status is still not jet OK, because even it has d to fill the complete leaf set condition,
\* it still has outgoing probing. 
\A k \in NodesReady, i, j \in I: 
 /\ i # k
 /\ i # j
 /\ j # k
 /\ j = RightNeighbor(lset[i])
 /\ CwDist(i, k) < CwDist(i, j)
 => k \in GetLSetContent(lset[i])
NeighborClosestLeft == 
\A k, i \in ReadyOK: i # k => CwDist(LeftNeighbor(lset[i]), i) =< CwDist(k, i)

NeighborClosestInv == 
 ~\E a, b, c \in I:
 /\ a # b
 /\ a # c
 /\ b # c
 /\ b = RightNeighbor(lset[a])
 /\ a \in ReadyOK
 /\ c \in NodesReady
 /\ CwDist(a, c) < CwDist(a, b)




ReadyOKNeighbor == 
\* Does not hold, found counter Example in vI log/HN-RN-IN.log
\A i \in ReadyOK, j \in NodesReady:
     ~(i = j) => 
     /\ CwDist(LeftNeighbor(lset[j]), j)=< CwDist(i, j)  

OKReadyNeighborR == 
\* fault property, counter example see vI log/HN-CN-IN-ORN.log
\A i \in ReadyOK, j \in NodesReady:
   /\ i # j
   /\ LeftNeighbor(RightNeighbor(lset[i])) = i
  => CwDist(i, RightNeighbor(lset[i])) =< CwDist(i, j)
  
OKReadyNeighborL == 
\* fault property, similar to OKReadyNeighborR
\A i \in ReadyOK, j \in NodesReady:
   /\ i # j
   /\ RightNeighbor(LeftNeighbor(lset[i])) = i
  => CwDist(LeftNeighbor(lset[i]), i)=< CwDist(j, i)
  
ReadyOKReady == 
\A a, b \in NodesReady, e \in ReadyOK:
/\ a # b 
/\ a # e
/\ b # e
/\ CwDist(a, e) < CwDist(a, b)
=> \/ CwDist(a, RightNeighbor(lset[a])) =< CwDist(a, e)
   \/ CwDist(LeftNeighbor(lset[b]), b) =< CwDist(e, b)
   
   
LeafSetRange == 
\* too strong invariant.
\A i \in ReadyOK, j \in NodesReady:
  \/ j \in GetLSetContent(lset[i]) 
  \/ /\ CwDist(i, j) > CwDist(i, RightMost(lset[i])) 
     /\ CwDist(j, i) > CwDist(LeftMost(lset[i]), i)
     *)
-------------------------------------
CrossNeighbor == 
\*violated by vI/CN-violation
~\E i, j, l, r \in NonDead: 
   /\ i # j
   /\ l # r
   /\ {i, j} \cap ReadyOK # {}
   /\ LeftNeighbor(lset[r]) = i
   /\ RightNeighbor(lset[i]) = r
   /\ RightNeighbor(lset[l]) = j
   /\ LeftNeighbor(lset[j]) = l
   /\ CwDist(l, i) < CwDist(l, j)
   /\ CwDist(i, j) < CwDist(i, r) 
   /\ PrintT(<<"i:", i, "j:", j, "l:", l, "r:", r>>)
IncludeNeighbor == 
\*violated by vI/log/IncludeNeighborCE.log
~\E i, j, l, r \in NonDead: 
   /\ i # j
   /\ l # r
   /\ RightNeighbor(lset[i]) = j
   /\ LeftNeighbor(lset[j]) = i
   /\ RightNeighbor(lset[l]) = r
   /\ LeftNeighbor(lset[r]) = l
   /\ CwDist(l, i) < CwDist(l, r)
   /\ CwDist(l, j) < CwDist(l, r)
   /\ PrintT(<<"i:", i, "j:", j, "l:", l, "r:", r>>)

----------------------------------------------   
   
Invariant ==
 /\ LSetInv
 /\ HalfNeighbor
 /\ NeighborClosest
\* /\ LemmaExclusion1
\* /\ LeafSetRange
\* /\ ReadyNeighbor

\* lookup msg is always delivered by the closest "ready" node to its key
Correctness == 
[][\A i, k, n \in I: Deliver(i,k) /\ status[n] = "ready" 
         => AbsDist(i, k) =< AbsDist(n, k)]_vars
                     
Consistency == \* At any time, there exist at most one node taking charge of a key k
[][\A x, y, k \in I: ENABLED Deliver(x, k) /\ ENABLED Deliver(y, k) => x = y]_vars
(*\A x, y, k \in I: 
   (   status[x] = "ready"   
    /\ LeftDist(LeftCover(lset[x]), k) 
       =< LeftDist(LeftCover(lset[x]), RightCover(lset[x]))
    /\ status[y] = "ready"
    /\ LeftDist(LeftCover(lset[y]), k) 
       =< LeftDist(LeftCover(lset[y]), RightCover(lset[y]))
    )
    => x = y
*)
CorrectDelivery == \A i,k \in I: 
  ENABLED Deliver(i, k)
  => /\ \A n \in I: status[n] = "ready"=> AbsDist(i, k) =< AbsDist(n, k)
     /\ \A j \in I\{i}: ~ENABLED Deliver(j, k) 
     
CorrectCoverage == \A i,k \in I: 
  /\ status[i] = "ready" 
  /\ \E m \in receivedMsgs: 
     /\ m.mreq.type = "Lookup"
     /\ m.destination = i
     /\ m.mreq.node = k
     /\ Covers(lset[i], k)
  => /\ \A n \in I: status[n] = "ready"=> AbsDist(i, k) =< AbsDist(n, k)
     /\ \A j \in I\{i}: ~ /\ status[j] = "ready" 
                          /\ \E m \in receivedMsgs: 
                             /\ m.mreq.type = "Lookup"
                             /\ m.destination = j
                             /\ m.mreq.node = k
                             /\ Covers(lset[j], k)


==============================================================
