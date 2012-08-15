 -------------------------- MODULE Actions ---------------------------
\* This module defines all the actions

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
EXTENDS InitialStates
---------------------------------------------------------------
\* Application relevant actions

\* an application on node i tries to find the node k 
\* or to find the node which is closest to the key k.
\* The node i generate a Lookup msg and ask himself to
\* route it to k. 
Lookup(i, k) ==
  /\ ~\E m \in receivedMsgs: 
     /\ m.destination = i
     /\ m.mreq.type = "Lookup"
     /\ m.mreq.node = k
  /\ receivedMsgs'= receivedMsgs \cup 
                    {[destination |-> i, 
                      mreq |-> [
                                type |-> "Lookup", 
                                node |-> k]
                     ]}
  /\ UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>


\* a node i has got an ID "seed" from the application running based
\* on the overlay network and he wants to join the network.
\* Seed is one of the status nodes in the network who is in charge of
\* some range of keys which is numerrically close to him.
\* The node i generate the JoinRequest msg for seed to let him
\* route the msg to the ID i. By doing this, the msg will be replied
\* by the node nummerically closest to i and hence find the correct
\* place for i to join into the network.
Join(i, seed) == 
  /\ i # seed 
  /\ ~\E m \in receivedMsgs: 
     /\ m.destination = seed
     /\ m.mreq.type = "JoinRequest"
     /\ m.mreq.node = i    
  /\ status[i] = "dead" /\ status[seed] ="ready"        
  /\ lset[i] = EmptyLS(i)           
  /\ receivedMsgs'= receivedMsgs \cup 
                    {[destination |-> seed, 
                      mreq |-> [
                                type |-> "JoinRequest", 
                               rtable |-> InitRTable, 
                               node |-> i]
                     ]}
  /\ status' = [status EXCEPT ![i]="wait"]
  /\ UNCHANGED <<rtable, lset, probing, failed, lease, grant>>
------------------------------------------------
\* Internal behavior of system 

\* (1) Delivering 
\* a node i deliver the lookup message it take charge of k
\* Only the status node can deliver Lookup messages,
\* which destination is leaseed by this node
Deliver(i, k) == 
  /\ status[i] = "ready" 
  /\ \E m \in receivedMsgs: 
     /\ m.mreq.type = "Lookup"
     /\ m.destination = i
     /\ m.mreq.node = k
     /\ Covers(lset[i], k)
     /\ receivedMsgs'= (receivedMsgs \{m}) 
  /\ UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>
---------------------------------------------------------
\* (2) Routing

\*Help function for route
FindNext(k, i) ==
  LET 
     lsCan ==  {c \in GetLSetContent(lset[i]) \ failed[i]: status[c] # "dead"}
     canrelax ==
           {can \in (GetLSetContent(lset[i]) 
                    \cup GetRTableContent(rtable[i]))
                    \ failed[i]:
           AbsDist(k, can) < AbsDist(k, i)  /\ status[can] # "dead"}
  IN 
   
    IF \* We should find the next hop in leaf set
     \* when the leaf set of i covers whole ring,
     \* or i is within the range of leaf set;
     (\/ Overlaps(lset[i])      
      \/ CwDist(LeftMost(lset[i]), i) =< CwDist(LeftMost(lset[i]), RightMost(lset[i])))
     /\ ~ lsCan = {}
    THEN CHOOSE n \in lsCan: \A m \in lsCan: AbsDist(n, k) =< AbsDist(m, k)
  \* Real network will check the liveness via underlying TCP PING, but here
  \* we assume the TCP is reliable and we pretend to get the liveness
    ELSE \*Otherwise we should try the rtable
       IF ~canrelax = {} 
       THEN CHOOSE can \in canrelax: \A m \in canrelax: AbsDist(can, k) =< AbsDist(m, k)
       ELSE i
(* The following is the complex algorithm involves routing table lookup
(* To get the next forward destination.*)
\* since we check the liveness of a node before pick it as candidate, 
\* we don't take it if it is "dead"
  IF \* We should find the next hop in leaf set
     \* when the leaf set of i covers whole ring,
     \* or i is within the range of leaf set;
     \/ Overlaps(lset[i])      
     \/ CwDist(LeftMost(lset[i]), i) =< CwDist(LeftMost(lset[i]), RightMost(lset[i]))
  THEN LET lsCan ==  {c \in GetLSetContent(lset[i]) \ failed[i]: status[c] # "dead"}
  \* Real network will check the liveness via underlying TCP PING, but here
  \* we assume the TCP is reliable and we pretend to get the liveness
       IN CHOOSE n \in lsCan: \A m \in lsCan: AbsDist(n, k) =< AbsDist(m, k)
  ELSE \*Otherwise we should try the rtable
       LET r == SharedDig(k, i)
           rtCan == rtable[i][<<r, GetDigit(k, r+1)>>]
       IN IF rtCan # null /\ status[rtCan] # "dead"
          THEN rtCan
          ELSE \* If we cannot find anyone from rtable, we relax the condition and try with 
               \* all we know from rtable and lset
               LET canrelax ==
                   {can \in (GetLSetContent(lset[i]) 
                            \cup GetRTableContent(rtable[i]))
                            \ failed[i]:
                   AbsDist(k, can) < AbsDist(k, i) /\ SharedDig(k, can) >= r /\ status[can] # "dead"}
                   \* again, we simulate the check liveness here
               IN IF canrelax # {} 
               THEN CHOOSE can \in canrelax: \A m \in canrelax: AbsDist(can, k) =< AbsDist(m, k)
               ELSE null
*)

\* the node i forwards a look up to a closer node to the final destination k
\* when it is "ready" and the destination key is outside of its range
\* If we can't find the closer node, then we fire an Error
RouteLookup(i, k) == 
  /\ status[i] = "ready"
  /\ \E m \in receivedMsgs:
     /\ m.destination = i
     /\ m.mreq.type ="Lookup" 
     /\ m.mreq.node = k 
     /\ ~Covers(lset[i], k)
     \* the k is not in the cover range of i
     /\ LET nh ==  FindNext(k, i)
        IN  receivedMsgs'= (receivedMsgs \{m}) \cup 
              IF nh # i
              THEN {[destination |-> nh, mreq |-> m.mreq]}
              ELSE {[destination |-> i, mreq |-> [type |-> "NoLegalRoute", key |-> k]]}\*fire the error
  /\ UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>
          
\* the node i forwards a join request to a closer node to the final destination k
\* when it is "ready" and the destination key is outside of its range
\* If we can't find the closer node, then we fire an Error
RouteJoinRequest(i, k) == 
  /\ status[i] = "ready"
  /\ \E m \in receivedMsgs:
     /\ m.destination = i
     /\ m.mreq.type = "JoinRequest"
     /\ m.mreq.node = k 
     /\ ~k \in GetLSetContent(lset[i]) 
     \* to avoid the case that a node left and rejoin before its neighbor deleted it from their leaf set
     /\ ~Covers(lset[i], k)
     /\ LET nh ==  FindNext(k, i)
        IN 
        receivedMsgs'= (receivedMsgs \{m}) \cup 
          IF nh # i
          THEN {[destination |-> nh, mreq |-> 
                   [type |-> "JoinRequest",
                    rtable |-> AddToTable(GetRTableContent(rtable[i]), m.mreq.rtable, i),
                    node |-> k]]}\*for join request, we update the rtable by each hop
          ELSE {[destination |-> i, mreq |-> [type |-> "NoLegalRoute", key |-> k]]}\*fire the error
  /\ UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>
-----------------------------------------------------------------------------------------------
\* (3) Consistent Join

\* node i receives join request msg and send back join reply with its leaf set
\* when the node i is "ready" and the destination is within the cover range
ReceiveJoinRequest(i) ==  
  /\ status[i] = "ready" 
  /\ \E m \in receivedMsgs: 
   /\ m.destination = i
   /\ m.mreq.type = "JoinRequest"
   /\ ~m.mreq.node \in GetLSetContent(lset[i]) 
   \* to avoid the case that a node left and rejoin before its neighbor deleted it from their leaf set
   /\ CwDist(LeftCover(lset[i]), m.mreq.node) =< CwDist(LeftCover(lset[i]), RightCover(lset[i]))
   /\ LET newmjr == [type |-> "JoinReply",  
                            rtable |-> m.mreq.rtable,
                              lset |-> lset[i]]
          newmj == [destination |-> m.mreq.node,
                           mreq |-> newmjr]
      IN receivedMsgs'= (receivedMsgs \{m}) \cup {newmj}
  /\ UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>
   
\* A function to build the Probe Message to its neighbour
Probe(i, ls, f, toprob) == 
  {[destination |-> j,
          mreq |-> [type |-> "LSProbe",  
                    node |-> i,
                    lset |-> ls,
                  failed |-> f
                   ]
  ]: j\in toprob}
  
\* Node i receives join reply msg, it updates its rtable and lset with
\* the received information and probe the new nodes in its leaf set.
ReceiveJoinReply(i) == 
/\ status[i] = "wait" 
\* 1) A node shouldnot receive join reply if it is no more in the network ("dead")
\*    to avoid to be "activated" by gabage message.
\* 2) To receive join reply after it turns to be "ok" or "ready" makes no sense.
/\ probing[i] = {}
\* to ensure that he is waiting for join reply, not for prob reply. 
/\ lset[i] = EmptyLS(i)
\* this is used for proving that the node waiting to join should have empty leaf set.
/\ \E m \in receivedMsgs: 
   /\ m.destination = i
   /\ m.mreq.type = "JoinReply"
   /\ LET
        newrtable ==  AddToTable(GetLSetContent(m.mreq.lset)
                                \cup GetRTableContent(m.mreq.rtable), 
                                 rtable[i], i)
        newlset == AddToLSet(GetLSetContent(m.mreq.lset), lset[i])
        toprob == GetLSetContent(newlset) \ {i}
        probmsgs == Probe(i, newlset, {}, toprob)
      IN
     /\ rtable'= [rtable EXCEPT ![i] = newrtable] 
     /\ lset'= [lset EXCEPT ![i] = newlset] 
     /\ probing'= [probing EXCEPT ![i] = toprob]
     /\ failed'=[failed EXCEPT ![i] = {}]
     /\ receivedMsgs'= (receivedMsgs \ {m}) \cup probmsgs
/\ UNCHANGED <<status, lease, grant>>

ReceiveLSProbeInner(i, m) ==
LET j == m.mreq.node
        fi == failed[i] \ {j} \*failed[i] removes j
       ls1 == IF j \in GetLSetContent(lset[i]) 
              THEN lset[i]
              ELSE AddToLSet({j}, lset[i]) \* lset[i] extended with j
       \*ls2 == RemoveFromLSet(m.mreq.failed, ls1)\*lset[i] removes the common members of m.failed
       \* we don't remove any node from leaf set before node i's lease finishes.
     lprim == GetLSetContent(AddToLSet((GetLSetContent(m.mreq.lset) \ fi), ls1))\* see above
      prb1 == GetLSetContent(ls1) \cap m.mreq.failed \* need to confirm if the told failed nodes are real failed
      \* before we want to delete them from the leaf set
      prb2 == lprim \ GetLSetContent(ls1) \* need to confirm the new candidates for the leaf set are real alive
      \* before we want to add them
      prb == (prb1 \cup prb2) \ (probing[i] \cup fi) 
      newm == [type |-> "LSProbeReply",  
                  node |-> i,
                  lset |-> ls1,
                  failed |-> fi]
     IN
         /\failed' = [failed EXCEPT ![i]=fi]
         /\rtable' = [rtable EXCEPT ![i] = AddToTable({j}, @, i)]
         /\lset'   = [lset EXCEPT ![i] = ls1]
         /\probing'= [probing EXCEPT ![i] = @ \cup prb] 
         \* If node i has probed j and waiting its reply but then get the probe msg from j
         \* it continue to wait j's reply. So, the probing' might contains j 
         
         \* we delete the change of status status because we don't allow the remove of leaf set member here.
         \*/\status' = [status EXCEPT ![i] = IF ~IsComplete(ls2) /\ @ \in {"ready", "ok"} THEN "wait" ELSE @]
         \* In case we removed the nodes of m.mreq.failed from leaf set of i, then it is no more complete
         \* we need to change the node's status in order to complete the leaf set first before it can route badly
         \* see vE-pastry/log/log-receiveProbeWithFailedNodes.txt since step 19, when node 17 received msg from 18
         \* containing the failed node 95, node 17 removes 95 from its leaf set, then it is no more completed
         /\receivedMsgs' = (receivedMsgs \ {m}) 
                           \cup { [destination |-> j, mreq |-> newm]} 
                           \cup Probe(i, ls1, fi, prb)
/\ UNCHANGED <<lease, status, grant>>
\* Node i receives probe msg from j. 
\* It updates the local knowledge w.r.t. j and send reply back to j.
\* It probes nodes in leaf set which are in failed and removes them from its leaf set.(prb1)
\* Then it creates the clone L' of its leaf set and add nodes in L, which it 
\* consideres not to be faulty. (lprim)
\* It probes the new nodes in lprim before inclusion. (prb2)
ReceiveLSProbe(i) ==
/\ status[i] # "dead" \* Only "dead" nodes donnot react on probe. 
/\ status[i] = "wait" => lset[i] # EmptyLS(i)
\*/\ status[i] \in {"ready","ok"} \* if there are only one ready node on the ring
\* and two other nodes wants to join, they have to reply each other's probe to
\* complete their leaf set. So this must allow the "wait" nodes.
/\ \E m \in receivedMsgs:
  /\ m.destination = i
  /\ m.mreq.type = "LSProbe"
  /\ m.mreq.node # i
  /\ ReceiveLSProbeInner(i, m) 

\* A node i receives probe reply msg. It does similar things as receiving probe msg except:
\* instead of sending reply, it removes j from probing; (prb3)
\* If there is still out standing probes, do nothing. (prb3 = {})
\* If no out standing probes exists, it checks if its leaf set is complete
\* when yes, it turns its status to "ok" and thus finish the consistent join phrase.
\* If the leaf set is not complete, it probes the farest nodes (leftmost and rightmost) 
\* in leaf set to complete it.
ReceiveLSPrRplInner(i,m) ==
  LET j == m.mreq.node
      Ls == m.mreq.lset
      fi == failed[i] \ {j} \*failed[i] removes j
     ls1 == IF j \in GetLSetContent(lset[i]) 
              THEN lset[i]
              ELSE AddToLSet({j}, lset[i]) \* lset[i] extended with j
     \* ls2 == RemoveFromLSet(m.mreq.failed, ls1)
     \* we don't remove any node from leaf set before node i's lease finishes.
   lprim == GetLSetContent(AddToLSet((GetLSetContent(Ls) \ fi), ls1))
            \* potential new leaf set by adding received leaf set.
    prb1 == (GetLSetContent(ls1) \cap m.mreq.failed )\ (probing[i] \cup fi)
     \* heard of some failed nodes, which are my leaf set member, need to be confirmed before 
     \* remove
    prb2 == lprim \ (GetLSetContent(ls1) \cup probing[i] \cup fi \cup prb1)
      \* brand new nodes in the potential new leaf set need first to be probed then be added.
    prb3 == ((probing[i] \cup prb1 \cup prb2) \ failed[i]) \ {j} 
      \* overall all probing nodes after this action
    (*
    cand == (GetLSetContent(ls1) \cup GetRTableContent(rtable[i])) \ {i}

      lm == \* left most of leaf set
            IF Lenth(ls1.left) = 0 \* if left set is empty, we try to get candidate from rtable
            THEN {x \in cand: \A p \in cand: CwDist(p, i) =< CwDist(x, i)}
            ELSE {LeftMost(ls1)}
      rm == \* right most of leaf set
            IF Lenth(ls1.right) = 0 \* if right set is empty, we try to get candidate from rtable
            THEN {y \in cand: \A q \in cand: CwDist(i, q) =< CwDist(i, y)}
            ELSE {RightMost(ls1)}  
 newprob == IF  IsComplete(ls1)
            THEN {}
            ELSE IF Lenth(ls1.left) < L /\ Lenth(ls1.right) < L
                 THEN lm \cup rm
                 ELSE IF Lenth(ls1.left) < L /\ Lenth(ls1.right) = L
                      THEN lm
                      ELSE rm
     *)
shouldBeOK == \* A node has no outstanding probe and has completed its leaf set
              \* then it should turn to be status ("ok")
              /\ status[i] = "wait" 
              /\ prb3={}
              /\ Overlaps(ls1)\/IsComplete(ls1)
  IN /\ rtable' = [rtable EXCEPT ![i] = AddToTable({j}, @, i)]
     /\ lset'   = [lset EXCEPT ![i] = ls1]
     /\ failed' = [failed EXCEPT ![i] = IF prb3={} /\ IsComplete(ls1) THEN {} ELSE fi]       
     /\ probing'= [probing EXCEPT ![i] = prb3]
     /\ status'= [status EXCEPT ![i] = IF shouldBeOK THEN "ok" ELSE @]      
     /\ receivedMsgs' = (receivedMsgs \ {m}) 
                        \cup Probe(i, ls1, fi, prb1)
                        \cup Probe(i, ls1, fi, prb2)
                       \* \cup Probe(i, ls2, fi, newprob)
     /\ UNCHANGED <<lease, grant>>

ReceiveLSPrRpl(i) ==
/\ status[i] # "dead"
\* only "dead" nodes donnot react on probe reply.
/\ \E m \in receivedMsgs: 
   /\ m.destination = i
   /\ m.mreq.type = "LSProbeReply" 
   /\ m.mreq.node \in probing[i] \* others' faked probe-reply might make i status
                                 \* and hence create a partition of network
   /\ m.mreq.node # i
   /\ ReceiveLSPrRplInner(i,m)
       
\* A node i suspected j to be faulty and hence probe j
SuspectFaulty(i, j) == 
  /\ status[i] \in {"ready", "ok"} \* it doesn't make sense for a waiting node to suspect any dead node
       \* By enhencing this condition, we are able to say, i cannot be
       \* the single ready/ok node on the ring, since its leaf set is not empty.
  /\ status[j]= "dead" \* For simplicity we enforce it. 
  /\ i # j \* node doesnot suspect itself
  /\ j \in GetLSetContent(lset[i]) \* node only suspect nodes in its leaf set
  /\ j \notin probing[i] \*node does not suspect outstanding probed node
  /\ j \notin failed[i] \*node does not suspect a 'dead' node it knows
  /\ receivedMsgs'= receivedMsgs \cup Probe(i, lset[i], failed[i], {j})
  /\ probing'=[probing EXCEPT ![i]= @\cup {j}]
  /\ UNCHANGED <<rtable, lset, failed, lease, grant, status>>

\* Simulation of a normal behavior.
\* A node i stops waiting reply from node j and considers j to be failed  
\* In the real system, 
\* the node i will try several times before it gives up waiting. 
\* Besides it will try different ways
\* to contact node j, including using virtual link techniques.
\* We simplified the virtual link technique in our model:
\* If a node has blocked incoming channel but not outgoing channel,
\* Then we assume that a virtual link will be set up so that it behaves
\* exactly like a normal node. Hence, after using virtual link, 
\* the node can contact each other. Hence all the probe will be ordinarily handled.
\* In all, as soon as probe time out happend by i for probing j, it means
\* there is no way for i to find j, even through virtual link. 
\* Then there is only two possibilities: either i has already left the
\* network or j has. 
\* The first case is ruled out by previous gard, so j must have left the network.
\* That's why we simulate the real situation like this. 
ProbeTimeOut(i, j)== 
/\ status[i]# "dead" \* for nodes no more in the network, it does not matter
/\ \/ status[j]= "dead" 
   \/ /\ status[j]= "wait"
      /\ lset[j] = EmptyLS(j)\* For simplicity we enforce it. 
/\ j \in probing[i]
/\ failed' = [failed EXCEPT ![i] = @\cup {j}]
/\ probing' = [probing EXCEPT ![i] = @ \ {j}]
/\ lset' = [lset EXCEPT ![i] = IF ~(j \in grant[i]) /\ j \in GetLSetContent(@)
                               THEN RemoveFromLSet({j},@) 
                               ELSE @]
   \* A fix after log/vI-Pastry/HN-NC-newProbe-newGrant.log, to prevent a node becoming 
   \* wait when some previous leafset node left the network. Now, only if someone from 
   \* the current leaf set left the network, this node will change its status
/\ receivedMsgs' = receivedMsgs \
                          IF \E m \in receivedMsgs: m.mreq.type = "LSProbe"
\* here we delete all the gabage probe msgs from i to j, since 
\* we are sure no one will get a reply any more. 
                                /\ m.mreq.node = i
                                /\ m.destination = j
                          THEN  {m \in receivedMsgs: m.mreq.type = "LSProbe"
                                   /\ m.mreq.node = i
                                   /\ m.destination = j}
                          ELSE {}
/\ status'= [status EXCEPT ![i] = IF ~(j \in grant[i]) /\ j \in GetLSetContent(lset[i]) THEN "wait" ELSE @] 
/\ lease'= [lease EXCEPT ![i] = @ \ {j}]
/\ UNCHANGED <<rtable, grant>>
-----------------------------------------------------------------------------------------------------
\* (4) Periodic maintenance protocol

\* A node has complete the consistent join phrase, then he should
\* request for leases from both its left and right neighbor. 
\* A lease is a time period for denoting if the node is "in charge" or not. 
\* Every status node ("ok" or "ready") should keep the lease of both its neighbors. 
\* When both of their neighbors have granded the leases to it, then 
\* it should turn to be "ready". After this, a node is completely joined 
\* the network and it can deliver msgs, chosen to be the seed node for 
\* joining new node etc. A node turns from "ready" to "ok" when at least one of 
\* its neighbors' lease has expired. He needs to request a new lease from 
\* the neighbor. 

\* In the implementation, we have another version of this part, 
\* which will be modeled in the new version: vF-MSPastry:
\* A node has complete the consistent join phrase 
\* or the lease is expired, 
\* both of the cases, it as the status of "ok".
\* Whenever a node is "ok", it should aggressively try to become "ready", 
\* It first needs to exchange the leaf set with its neighbor. 
\* Then after it receives leaf set broadcast msgs from both neighbors, 
\* it becomes "ready" to route and receive join request.
\* After a fixed period of time since it tries to exchange the leaf set, 
\* its "lease" will expire and it turns back to "ok" and restart the some 
\* process. 
\* In our model, we abstract the 'period of time' to an indeterministic action.


\* One problem occurs by our model until vG-MSPastry, namely the intention problem.
\* When two nodes join concurrently as neighbors, they might end up with the same 
\* lease value, e.g. 2, when they both try to grand the lease and hope the other to
\* accept it. Then the property LeaseOrder is violeted.
\* LeaseOrder == \* two neighbors can not have the same lease time of each other
\* \A i, j\in I, k \in {1, 2}: lease[i][j] = k /\ i # j => lease[j][i] # k
\* The consequence of contention is that no one of them can "release" the lease according 
\* to our model, because none of them has the value 1 and wait for the other to release first.
\* The only way to release the lease is that one of them is dead, according to
\* /\ lease[i][j] = 2 \*or after node i has granded lease to its neighbor j for a time period
\* /\ lease[j][i] = 0     \*and the node j's lease of i has already expired
\* But here we used a unrealistic trick, because a node should never know other node's information.
\* A fix of this problem is done in the vH-MSPastry, which used an approach in FreePastry Implementation.

\* Here we fix this problem by using another variable grant and simply the lease variable to be
\* just noticing from which nodes does a node get the leased granted.
\* the variable grant is used to remember to which nodes a node has granted a lease. 
\* this variable is only used to make sure that a node can only remove a node from its leaf set when 
\* its grant has expired, which means the lease of the other node of this node has expired already. 

RequestLease(i) ==
    /\ status[i] = "ok" 
    /\ lset[i] # EmptyLS(i)
    /\ LET ln == LeftNeighbor(lset[i])
           rn == RightNeighbor(lset[i])
       IN receivedMsgs' = (receivedMsgs 
                        \cup IF ~ (ln \in lease[i])
                             THEN {[destination |-> ln, 
                                  mreq |-> [type |-> "LeaseRequest",
                                            node |-> i]]}
                             ELSE {})
                        \cup IF ~ (rn \in lease[i])
                             THEN {[destination |-> rn, 
                                  mreq |-> [type |-> "LeaseRequest",
                                            node |-> i]]}
                             ELSE {}
    /\ UNCHANGED <<status, lset, rtable, probing, failed, lease, grant>>
    
\* A node received a LeaseRequest msg, 
\* if it is from neighbor, then it grands the lease and send reply back
\* if not from its neighbor, it deletes the request msg   
ReceiveLReq(i) ==  
/\ status[i] \in {"ok", "ready"} 
/\ lset[i] # EmptyLS(i)
/\ \E m \in receivedMsgs: 
   /\ m.destination = i
   /\ m.mreq.type = "LeaseRequest"
   \* There are two cases the request is taken care of: 1. a new node join
   \* 2. the lease has expired and it request it for a new lease
   \* For both cases, we grand a lease
   /\ grant' = [grant EXCEPT ![i] = 
                  IF m.mreq.node \in {LeftNeighbor(lset[i]), RightNeighbor(lset[i])}
                  THEN @ \cup {m.mreq.node} 
                  ELSE @]\* if the node is my neighbor then I should grant it
   /\ receivedMsgs' = (receivedMsgs \ {m})
                  \cup {[destination |-> m.mreq.node, 
                              mreq |-> [type |-> "BroadcastLSet",
                                        lset |-> lset[i],
                                        grant|->  m.mreq.node \in 
                                           {LeftNeighbor(lset[i]), 
                                            RightNeighbor(lset[i])}
                                                 ]]}
/\ UNCHANGED <<status, rtable, lset, probing, failed, lease>>      

\* A node receives BroadcastLSet msg. 
\* It could be two kinds of BLS: 
\* granding BLS come from the neighbor for granding the lease
\* We update the local leaf set and then see if the granding comes from neighbor
\* We update the lease if it is one of the neighbor;
\* and turns the node's status to ready if both of the neighbors have granded the lease
ReceiveBLS(i) ==  
/\ status[i] \in {"ok", "ready"}  
/\ lset[i] # EmptyLS(i)
/\ IsComplete(lset[i])
/\ \E m \in receivedMsgs: 
   /\ m.destination = i
   /\ m.mreq.type = "BroadcastLSet"
   /\ m.mreq.lset.node # i
   /\ LET \* First, we update the local leaf set
         ls == AddToLSet(GetLSetContent(m.mreq.lset)\ failed[i] , lset[i])
         ln == LeftNeighbor(ls)
         rn == RightNeighbor(ls)
         newlease == [lease EXCEPT ![i] = 
                       IF /\ m.mreq.lset.node \in  {ln, rn} 
                          /\ m.mreq.grant = TRUE
                       THEN @ \cup {m.mreq.lset.node}
                       ELSE @]
         shouldBeReady == ln \in newlease[i] /\ rn \in newlease[i]
      IN 
      /\ lset' = [lset EXCEPT ![i] = ls]
      /\ lease' = newlease
      /\ status' = [status EXCEPT ![i] =   IF shouldBeReady
                                           THEN "ready"
                                           ELSE @ ]
      /\ receivedMsgs' = (receivedMsgs \ {m})
/\ UNCHANGED <<rtable, probing, failed, grant>>
       
\* One of a node's lease has expired after a fixed time period T after it has requested for a lease.
\* A node starts to count the time down for lease expiration in two different cases: 
\* (1). it initially requested its neighbor for a lease
\* (2). it received the request and then grand the lease for its neighbor.
\* Since there is an order of this two cases, (1) must happen before (2) for a pair of neighbors,
\* the lease expires also in the same order. 
\* Therefore, whenever the node's lease is in the situation of 2, we need to make sure its 
\* neighbor has already expired the lease in our simulation.
\* the lease of node j has expired by i.  This is done with the following two actions.
LeaseExpired(i, j) == 
  \*/\ \E k \in I: k#i /\ status[k]="ready" \*if this is the only ready node, its lease cannot expire
  \* even if there is only one node ready on the network, it should expire its dead neighbor's lease
  /\ status[i] \in {"ready", "ok"}
  (*
  /\ \/ lease[i][j] = 1 \*after node i has got grand from its neighbor j for a time period
     \/ /\ lease[i][j] = 2 \*or after node i has granded lease to its neighbor j for a time period
        /\ lease[j][i] = 0     \*and the node j's lease of i has already expired
  /\ lease' = [lease EXCEPT ![i][j] = 0]
  *) 
  /\ i # j
  /\ j \in lease[i]
  /\ lease' = [lease EXCEPT ![i] = @ \{j}]
  /\ status' = [status EXCEPT ![i] = IF j \in {LeftNeighbor(lset[i]), RightNeighbor(lset[i])} /\ @ = "ready"
                                     THEN "ok" 
                                     ELSE @]
  /\ UNCHANGED <<receivedMsgs, rtable, lset, probing, failed, grant>>
  
\* This is a simulation of the order of the lease expiration. (see above action's comments)
GrantExpired(i, j) == 
/\ i # j
/\ status[i] \in {"ready", "ok"}
/\ j \in grant[i] /\ ~ (i \in lease[j])
/\ grant'= [grant EXCEPT ![i] = @ \ {j}]
/\ UNCHANGED <<receivedMsgs, status, lease, lset, probing, failed, rtable>>


\* node i finally removes its critical neighbor j from its leaf set. 
\* if there is no more possible repair for the node, it will
\* try to resign to the network
DeclareDead(i,j) == 
/\ status[i] \in {"ok", "ready"}
/\ j \in failed[i] \* After i has put j in failed for a while.
/\ j \in GetLSetContent(lset[i])   \* and it is still in leaf set
/\ j = LeftNeighbor(lset[i]) => ~ j \in grant[i]
/\ j = RightNeighbor(lset[i])=> ~ j \in grant[i]
\* If j is i's neighbor, then its lease must be already expired before 
\* it can be declared dead.
/\ lset' = [lset EXCEPT ![i] = RemoveFromLSet({j},@)]
/\ status'= [status EXCEPT ![i] = "wait"] 
/\ UNCHANGED <<receivedMsgs, rtable, lease, probing, failed, grant>>

ResignNode(i) == \* need to resign and rejoin
\* when half of the leaf set nodes drop
/\ status[i] = "wait"
/\ probing[i] = {}
/\ Lenth(lset[i].left) = 0  \/ Lenth(lset[i].right) = 0
/\ ~\E m \in receivedMsgs: m.mreq.type = "JoinReply" /\ m.destination = i 
/\ \E n \in I: n#i /\ status[n] = "ready"
    /\ rtable'= [rtable EXCEPT ![i] = AddToTable({i}, InitRTable, i)]
    /\ lset'= [lset EXCEPT ![i] = EmptyLS(i)]
    /\ probing' = [probing EXCEPT ![i] =  {}]
    /\ lease' = [lease EXCEPT ![i] = {}]
    /\ grant' =  [grant EXCEPT ![i] =  {}]
    /\ failed' = [failed EXCEPT ![i] = {}]
    /\ receivedMsgs' = receivedMsgs \cup 
                      {[destination |-> n, 
                        mreq |-> [
                            type |-> "JoinRequest", 
                           rtable |-> InitRTable, 
                           node |-> i]
                       ]}
/\ UNCHANGED status
Recover(i)== \* when resign is needed but no one could be found to resign,
\* i will recover the network by probing the farest element in its leaf set.
/\ status[i] = "wait"
/\ probing[i] = {}
/\ Lenth(lset[i].left) = 0  \/ Lenth(lset[i].right) = 0 
/\ ~\E n \in I:  status[n] \in {"ready", "ok"}
/\ ~(Lenth(lset[i].left) = 0  /\ Lenth(lset[i].right) = 0) 
\* The "ok" nodes are the first candidate to set up the network than this one
\* so as long as there is "ok" node, this node should wait till the "ok" node turns
\* "ready" see log-concurrent-leave-last.txt in vE...
/\ LET 
      pe == IF Lenth(lset[i].left) = 0 
            THEN RightMost(lset[i])
            ELSE LeftMost(lset[i])
   IN 
   /\ probing' = [probing EXCEPT ![i] =  probing[i] \cup {pe}]
   /\ receivedMsgs' = receivedMsgs \cup Probe(i, lset[i], failed[i], {pe})
/\ UNCHANGED <<lset, rtable, failed, lease, status, grant>>


\* if all the nodes go to wait or dead, one must be able to be ready again.
\* to ensure the assumption that at least one node is ready on the network.
\* This action is a simulation to a server restart, only the oracle can do this.
\* Because other waiting nodes, who has more information could trigger the 
\* recover action. So as long as there is some node being able to recover,
\* we do not restart.
(*Restart(i)== \* when resign is needed but no one could be found to resign,
\* and no one can be found to recover
\* i will restart the network and select itself to be the only ready one
/\ status[i] = "wait"
/\ probing[i] = {}
\* The following sentence contains the information only from the oracle
/\ \A k \in NonDead: Lenth(lset[k].left) = 0  /\ Lenth(lset[k].right) = 0 
/\ ~\E n \in I:  status[n] \in {"ready", "ok"}
\* The "ok" nodes are the first candidate to set up the network than this one
\* so as long as there is "ok" node, this node should wait till the "ok" node turns
\* "ready" see log-concurrent-leave-last.txt in vE...
\*-------------- This part is added just for simply the proof of HalfNeighbor
\* since we use this action just to prevent the complete down case,
\* we don't really care how it match the original protocol, because it was not 
\* described.
/\ ~\E ms \in receivedMsgs: ms.mreq.type = "LSProbeReply" 
/\ ~\E mk \in receivedMsgs: mk.mreq.type = "LSProbe" /\ mk.destination # i
/\ \A mj \in receivedMsgs: mj.mreq.type = "JoinReply"
                           => GetLSetContent(mj.mreq.lset) = {i}
/\ ~\E mb \in receivedMsgs: mb.mreq.type = "BroadcastLSet"
\*----------
/\ status' = [status EXCEPT ![i] = "ready"]
/\ rtable'= [rtable EXCEPT ![i] = AddToTable({i}, InitRTable, i)]
/\ lset'= [lset EXCEPT ![i] = EmptyLS(i)]
/\ probing' = [probing EXCEPT ![i] =  {}]
/\ lease' = [lease EXCEPT ![i] = {}]
/\ grant' = [grant EXCEPT ![i] = {}]
/\ failed' = [failed EXCEPT ![i] = {}]
/\ UNCHANGED <<receivedMsgs>>               
     *)
LSRepair(i) == 
\* find the new candidate for the missing entry in leaf set and try to complete it
/\ status[i] = "wait"
/\ probing[i] = {}
/\ ~IsComplete(lset[i])
/\ Lenth(lset[i].left) # 0  /\ Lenth(lset[i].right) # 0 
/\ LET
   lm == {LeftMost(lset[i])}
   rm == {RightMost(lset[i])}
   newprob == IF Lenth(lset[i].left) < L /\ Lenth(lset[i].right) < L
              THEN lm \cup rm
              ELSE IF Lenth(lset[i].left) < L /\ Lenth(lset[i].right) = L
                   THEN lm
                   ELSE rm \* here it contains the case when leaf set are complete 
                           \* because of overlap happens
   IN 
   /\ probing' = [probing EXCEPT ![i] =  probing[i] \cup newprob]
   /\ receivedMsgs' = receivedMsgs \cup Probe(i, lset[i], failed[i], newprob)
/\ UNCHANGED <<lset, rtable, failed, lease, status, grant>>
----------------------------------------------------------------
\* (5) Failure simulation actions
MsgLost == 
/\\E m \in receivedMsgs:
   \*/\ PrintT(<<"MsgLost", m>>)
   /\ receivedMsgs' = receivedMsgs \ {m}
/\ UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>
NodeLeft(i) ==
  /\ status[i] = "ready" \* for the moment we assume only ready node can leave
  \*/\ status[i] # "dead" \* a dead node has already left
  \*/\ \E j \in I: j # i /\ status[j] = "ready"
  /\ Cardinality({k \in I: status[k] = "ready"}) > L + 1\*to make sure there is at lease L+1 nodes working
  /\ status' = [status EXCEPT ![i] = "dead"]
  /\ rtable' = [rtable EXCEPT ![i] = AddToTable({i}, InitRTable, i)]
  /\ lset' = [lset EXCEPT ![i] = EmptyLS(i)]
  /\ probing' = [probing EXCEPT ![i] = {}]
  /\ failed' = [failed EXCEPT ![i] = {}]
  /\ lease' = [lease EXCEPT ![i]= {}]
  /\ grant'= [grant EXCEPT ![i]= {}]
  /\ UNCHANGED <<receivedMsgs>> 
==============================================================