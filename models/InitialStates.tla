-------------------------- MODULE InitialStates ---------------------------
\* This module defines the initial state and type invariants

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
EXTENDS Msg
(*
CONSTANTS 
   READY, OK, WAIT, DEAD

(*Assumptions*)
ASSUME   ~READY = WAIT
ASSUME   ~READY = DEAD
ASSUME   ~OK = WAIT
ASSUME   ~OK = DEAD
ASSUME   ~WAIT = DEAD
*)
VARIABLE 
   receivedMsgs, (* To maintain the pool of unhandled message*)
   status,       \* To record the activity of a node
\* Cover mechanism is introduced after the talk with Prof. Peter Druschel.
\* The key coverage of a node could be dynamically calculated out by its
\* left and right neighbor. But to maintain a consistent coverage in order
\* to maintain a consistent DHT, we have to allow a node to still use
\* its stable coverage for a reasonable time while its neighbor changes. 
\* Hence we store a node's coverage in the local memory. When routing,
\* the bound will not be calculated but only read from the local storage.
\* Each node keep its "cover", denoting which key space he is in charge of. 
\* A node is in charge of the interval from cover.left to cover.right (exclusive). 
\* For example, if the node 18 is the only active node in the network, its 
\* cover is [18, 19, 20, ..., 2^Exp-1, 0, 1, ..., 16, 17], cover.left should be 18
\* cover.right should be 17
\*   cover,        \* To record the key ownership of a node
   lease,        \* To record the leases it get from others
   grant,        \* To record the leases it grant to the others
   rtable,       \* To store the routing table of the nodes
   lset,         \* To store the leaf set of the nodes
   probing,      \* To keep the trace of each node, which nodes they are probing
   failed        \* To mark the unreachable/non-restatus nodes after the node has failed probing them
------------------------------------------------------------------------------
Init == 
  /\ receivedMsgs = {}
  /\ status = [i \in I |-> IF i \in A THEN "ready" ELSE "dead"] 
 (*
  /\ lease = [i \in I |-> [j \in I |-> IF i \in A /\ j \in A /\ i < j 
                                       THEN 1
                                       ELSE IF i \in A /\ j \in A /\ i >=j
                                            THEN 2
                                            ELSE 0]]
                                            *)
  /\ rtable = [i \in I |-> IF i \in A 
                           THEN AddToTable(A, InitRTable, i)
                           ELSE AddToTable({i}, InitRTable, i)]
  /\ lset = [i \in I |->  IF i \in A
                          THEN AddToLSet(A, EmptyLS(i))
                          ELSE EmptyLS(i)]
  /\ probing = [i \in I |-> {}]
  /\ failed = [i \in I |-> {}]
  /\ lease = [i \in I |-> IF i \in A
                          THEN A\{i}
                          ELSE {}]
  /\ grant = [i \in I |-> IF i \in A
                          THEN A\{i}
                          ELSE {}]
---------------------------------------------------------------------------
TypeInvariant == 
  /\ receivedMsgs \in SUBSET DMsg
  /\ status \in [I -> {"ready", "ok", "wait", "dead"}]
  \*/\ cover \in [I -> [left: Nat, right: Nat]]
  \*/\ lease \in [I -> [I -> {0, 1, 2}]]\*0: no lease, 1: got grand from, 2: got request from and grand to
  /\ lease \in [I -> SUBSET I] \* from which nodes does a node got lease permission
  /\ grant \in [I -> SUBSET I] \* to which nodes does a node grant the lease permission  
  /\ rtable \in [I -> RTable]
  /\ lset \in [I -> LSet] /\ \A i \in I: lset[i].node = i
  /\ probing  \in [I -> SUBSET I]
  /\ failed \in [I -> SUBSET I]
  

==============================================================
