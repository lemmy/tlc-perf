-------------------------- MODULE Msg ---------------------------
\* This module adds the declaration of different types of messages

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
EXTENDS RT
--------------------------------------------------------------
JReq == [type : {"JoinRequest"}, rtable: RTable, node: I] 
JRpl == [type : {"JoinReply"}, rtable: RTable, lset: LSet] 
Prb  == [type : {"LSProbe"}, node: I, lset: LSet, failed: SUBSET I] 
PRpl == [type : {"LSProbeReply"}, node: I, lset: LSet, failed: SUBSET I] 
Look == [type : {"Lookup"}, node: I] 
LReq == [type : {"LeaseRequest"}, node: I]
BLS  == [type : {"BroadcastLSet"}, lset: LSet, grant: BOOLEAN]
NoLR == [type : {"NoLegalRoute"},  key: I]

MReq == JReq \cup JRpl \cup Prb \cup PRpl \cup Look \cup LReq \cup BLS \cup NoLR
DMsg == [destination: I, mreq: MReq]
==============================================================
