-------------------------- MODULE RT ---------------------------
\* This model extends the data structures with definitions for RTable

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
EXTENDS LS
--------------------------------------------------------------
RTable == SUBSET I
InitRTable == {}\*Empty routing table
GetRTableContent(rt) == rt
AddToTable(newSet, rt, i) == rt \cup newSet
RemoveFromTable(set, rt, index) == rt \ set
(*
MaxDigit == M \div B
Row == 1..MaxDigit \* row indexes, e.g. {1, 2} for two-rows-table
Col == 0..Base-1   \* column indexes, e.g. {1, 2} for two-columns-table
Pos == Row \X Col  \* The position of x value in the table
RTable == [Pos -> (I \cup {null})]
\*Routing table is a mapping from position to node ID or null

InitRTable == [p \in Pos |-> null]\*Empty routing table

GetRTableContent(rt) == {rt[pos]: pos \in Pos} \ {null}
 
GetDigit(nodeId, digPos) == 
(* (I, digPos) Get the digPos'th digit of the given I*)
LET p == MaxDigit - digPos
IN 
  (nodeId % (Base^(p+1))) \div Base^p

SharedDig(i, j) == 
(* (nodeA, nodeB) returns the shared prefix length of the both I up to the MaxDigit*)
LET helpSD[k \in Nat] == 
      IF k > MaxDigit \/ GetDigit(i, k) # GetDigit(j, k)
      THEN k-1 ELSE helpSD[k+1]
IN helpSD[1] 

GetPos(index, nodeId) == 
\* calculate the proper position for the given nodeId wrt. node index i
   LET r == SharedDig(index, nodeId)
       c == GetDigit(nodeId, r+1)
   IN <<r+1,c>>

TheBetterNode(i ,j) == j 
(*(oldNode, newnode), returns the better node according to approximity metric. 
   In the real implementation, this should be replaced by the function checking the 
     approximity metric*) 

AddOthersToTable(newSet, rt, i) == 
\* Add nodes (except the corresponding node i) into routingtable of i.
  LET
    posToChange == {GetPos(i, j): j \in newSet}
  IN [p \in Pos |-> 
      IF  p \in posToChange 
      THEN LET newNode == CHOOSE v \in newSet: GetPos(i, v) = p
           IN TheBetterNode(rt[p], newNode)
      ELSE rt[p]
     ]

AddItselfToTable(rt, i) == 
\* Add the node itself into its routing table
LET 
  posToChange == {<<k, GetDigit(i, k)>>: k \in 1..MaxDigit}
IN [p \in Pos |-> 
      IF  p \in posToChange 
      THEN i
      ELSE rt[p]
   ]

AddToTable(newSet, rt, i) == 
     AddItselfToTable(AddOthersToTable(newSet \ {i}, rt, i), i)
(*(delta, rtable, index), update the rtable wrt. node index i
  by given set of nodes delta. If change the order of this two 
  operations, then we will allow the value i on its position be changed to other node.
  In fact, it makes no sense to store the itself in its routing table in
  each row. *)

RemoveFromTable(set, rt, index) == 
(*(delta, rtable, index), 
   remove the Is in set delta from the table rtable wrt. node index i.*) 
  LET 
    posToRemove == {pos \in Pos: \E j \in set: rt[pos] = j}
  IN [p \in Pos |->
      IF p \in posToRemove 
      THEN null
      ELSE rt[p]
     ]
*)
==============================================================
