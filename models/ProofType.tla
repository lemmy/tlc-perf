---- MODULE ProofType ----
(* The hierarchy of the Proofs are
 ProofRingProp (The basic parameters and operations for ring calculation)
   \subset ProofLSetProp (The leaf set local properties of data structure)
    \subset ProofType (The Proof of TypeInvariant)
     \subset ProofLSetInv (The proof of Invariant of Leaf Set properties)
      \subset ProofProp (The reduction proof from Correctness properties
                         of Pastry to a list of Leaf Set properties)
*) 
EXTENDS ProofLSetProp   
LEMMA ReadyInI== /\ NodesReady \in SUBSET I 
                 /\ ReadyOK \in SUBSET I 
                 /\ NodesReady \in SUBSET ReadyOK
                 /\ NonDead \in SUBSET I
                 /\ ReadyOK \in SUBSET NonDead
                 /\ NodesWait \in SUBSET NonDead
BY DEF NodesReady, ReadyOK, NodesOK, NodesWait, NonDead

\*AXIOM ExklusionSequence == \A i \in I: ~InSeq(i, <<>>)
\*There should be a library for axioms on sequence
\*AXIOM SeqToSetType == \A S: \A seq \in Seq(S): SeqToSet(seq) \in SUBSET S
\*RTable Theorems 
THEOREM AddToTableType == \A s \in SUBSET I, t \in RTable, i \in I: 
                           AddToTable(s, t, i) \in RTable
<1>1. TAKE u \in SUBSET I, v \in RTable, w \in I
<1>2. v \cup u \in RTable
   BY DEF RTable 
<1>9. QED BY <1>2 DEF AddToTable

THEOREM GetRTableContentType == \A t \in RTable: GetRTableContent(t) \in SUBSET I
PROOF BY DEF GetRTableContent, RTable

THEOREM InitRTableType == InitRTable \in RTable
PROOF BY DEF InitRTable, RTable


\* Actions Theorems
THEOREM ProbeType == \A i \in I, ls \in LSet, fi, prb \in SUBSET I: 
                     Probe(i, ls, fi, prb) \in SUBSET DMsg 
<1>1. TAKE i \in I
<1>2. TAKE ls \in LSet
<1>3. TAKE f, prb \in SUBSET I
<1>5. [type |-> "LSProbe",  
                    node |-> i,
                    lset |-> ls,
                  failed |-> f
                   ] \in Prb
   BY DEF Prb
<1>6. {[destination |-> j,
          mreq |-> [type |-> "LSProbe",  
                    node |-> i,
                    lset |-> ls,
                  failed |-> f
                   ]
       ]: j \in prb} \in SUBSET DMsg
   <2>1. \A q \in prb: [destination |-> q,
          mreq |-> [type |-> "LSProbe",  
                    node |-> i,
                    lset |-> ls,
                  failed |-> f
                   ] ] \in DMsg
      <3>1. TAKE k \in prb
      <3>2. [destination |-> k,
          mreq |-> [type |-> "LSProbe",  
                    node |-> i,
                    lset |-> ls,
                  failed |-> f
                   ] ] \in DMsg
         BY <1>3, <3>1, <1>5 DEF MReq, DMsg
      <3>9. QED BY <3>1, <3>2 
   <2>9. QED BY <2>1
<1>9. QED BY <1>6  DEFS  Probe

THEOREM ProbeMsgType == \A k \in I, ls \in LSet, f, prb \in SUBSET I: 
                           \A ms \in Probe(k, ls, f, prb): 
                                 /\ms.mreq.type = "LSProbe" 
                                 /\ms.destination \in prb
<1>1. ASSUME NEW k \in I, 
             NEW ls \in LSet,
             NEW f \in SUBSET I,
             NEW prb \in SUBSET I,
             NEW ms \in Probe(k, ls, f, prb)
      PROVE /\ms.mreq.type = "LSProbe" 
            /\ms.destination \in prb
   <2>1. ms \in {[destination |-> j,
          mreq |-> [type |-> "LSProbe",  
                    node |-> k,
                    lset |-> ls,
                  failed |-> f
                   ]
         ]: j\in prb}
      BY <1>1 DEF Probe
   <2>3. \A m \in {[destination |-> j,
          mreq |-> [type |-> "LSProbe",  
                    node |-> k,
                    lset |-> ls,
                  failed |-> f
                   ]
         ]: j\in prb}: m.mreq.type = "LSProbe"
      BY SimplifyAndSolve 
   <2>7. ms.mreq.type =  "LSProbe" 
      BY <2>1, <2>3  
   <2>8. ms.destination  \in prb
      BY <2>1
   <2>9. QED BY <2>7,<2>8
<1>9. QED BY <1>1
THEOREM FindNextType == \A k, i \in I: TypeInvariant => FindNext(k, i) \in I
<1>1.TAKE k, i \in I
<1>2.ASSUME 
     TypeInvariant,
     NEW lsCan, 
     lsCan = {c \in GetLSetContent(lset[i]) \ failed[i]: status[c] # "dead"},
     NEW canrelax,
     canrelax = 
           {can \in (GetLSetContent(lset[i]) 
                    \cup GetRTableContent(rtable[i]))
                    \ failed[i]:
           AbsDist(k, can) < AbsDist(k, i)  /\ status[can] # "dead"}
     PROVE
        (IF 
         (\/ Overlaps(lset[i])      
          \/ CwDist(LeftMost(lset[i]), i) =< CwDist(LeftMost(lset[i]), RightMost(lset[i])))
         /\ ~ lsCan = {}
         THEN CHOOSE n \in lsCan: \A m \in lsCan: AbsDist(n, k) =< AbsDist(m, k)
         ELSE 
           IF ~canrelax = {} 
           THEN CHOOSE can \in canrelax: \A m \in canrelax: AbsDist(can, k) =< AbsDist(m, k)
           ELSE i) \in I
   <2>1. lsCan \in SUBSET I
      BY <1>2, GetLSetContentType DEF TypeInvariant
   <2>2. canrelax \in SUBSET I
      BY <1>2, GetLSetContentType, GetRTableContentType DEF TypeInvariant
   <2>7.CASE (\/ Overlaps(lset[i])      
             \/ CwDist(LeftMost(lset[i]), i) =< CwDist(LeftMost(lset[i]), RightMost(lset[i])))
             /\  ~ lsCan = {}
      <3>1. \E n \in lsCan: \A m \in lsCan: AbsDist(n, k) =< AbsDist(m, k)
         BY <2>1, <2>7, AbsMinimal
      <3>2. QED
        BY <1>2, <2>1, <2>7, <3>1
   <2>8. CASE ~(\/ Overlaps(lset[i])      
                \/ CwDist(LeftMost(lset[i]), i) =< CwDist(LeftMost(lset[i]), RightMost(lset[i])))
              \/ lsCan = {}
      <3>1. CASE canrelax = {}
         <4>9.QED BY <1>2, <2>8, <3>1
      <3>2. CASE canrelax # {}
         <4>3. \E can \in canrelax: \A m \in canrelax: AbsDist(can, k) =< AbsDist(m, k)
            BY <2>2, <3>2, AbsMinimal
         <4>9. QED BY <1>2, <2>2, <2>8, <3>2, <4>3
      <3>9. QED BY <3>1, <3>2
   <2>9. QED BY <1>2, <2>7, <2>8 
<1>9.QED BY <1>1, <1>2 DEF FindNext




THEOREM InitTypeCorrect == Init => TypeInvariant
(*  BY DEFS Init, TypeInvariant *)
  <2>. HAVE Init
  <2>1.  /\ receivedMsgs \in SUBSET DMsg
         /\ status \in [I -> {"ready", "ok", "wait", "dead"}]
         /\ lease \in [I -> SUBSET I]
         /\ grant \in [I -> SUBSET I]
         /\ probing  \in [I -> SUBSET I]
         /\ failed \in [I -> SUBSET I]
      BY AType DEFS Init
  <2>2.  rtable \in [I -> RTable]
      BY AType DEFS RTable, AddToTable, Init, InitRTable
  <2>3.  lset \in [I -> LSet] /\ \A i \in I: lset[i].node = i
      BY AType, EmptyLST, AddToLSetType, AddToLSetNoChangeNode DEF Init
  <2>99. QED
      BY <2>1, <2>2, <2>3 DEF TypeInvariant
      
THEOREM NextTypeCorrect == TypeInvariant /\ [Next]_vars => TypeInvariant'
   <2>. SUFFICES ASSUME TypeInvariant,
                        [Next]_vars
                 PROVE  TypeInvariant'
      OBVIOUS
   <2>2. ASSUME NEW i \in I, NEW j \in I,
                 RouteLookup(i,j)
         PROVE  TypeInvariant'
         <3>. DEFINE  nh ==  FindNext(j, i)
         <3>. nh \in I
           BY FindNextType
         <3>1. ASSUME NEW m \in receivedMsgs,
                      m.destination = i,
                      m.mreq.type ="Lookup" ,
                      m.mreq.node = j, 
                      receivedMsgs'= (receivedMsgs \{m}) \cup 
                        IF nh # i 
                        THEN {[destination |-> nh, mreq |-> m.mreq]}
                        ELSE {[destination |-> i, mreq |-> [type |-> "NoLegalRoute", key |-> j]]},
                      UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>
               PROVE TypeInvariant'
            <4>1. receivedMsgs' \in SUBSET DMsg
               <5>. CASE nh # i
                  <6>4. [destination |-> nh, mreq |-> m.mreq] \in DMsg
                     BY <3>1 DEF DMsg, TypeInvariant
                  <6>9. QED BY <3>1,<6>4 DEF TypeInvariant
               <5>. CASE nh = i               
                  <6>3. [destination |-> i, mreq |-> [type |-> "NoLegalRoute", key |-> j]] \in DMsg
                        BY DEF DMsg, NoLR, MReq
                  <6>9. QED BY <3>1, <6>3 DEF TypeInvariant
               <5>3. QED OBVIOUS 
            <4>3. QED BY <3>1, <4>1 DEF TypeInvariant
         <3>2.QED BY <3>1, <2>2 DEF  RouteLookup
   <2>22.ASSUME NEW i \in I, NEW k \in I,
                RouteJoinRequest(i,k)
         PROVE  TypeInvariant'
      <3>. DEFINE nh ==  FindNext(k, i)
      <3>0. nh \in I
        BY FindNextType
      <3>1. ASSUME NEW m \in receivedMsgs,
                       m.destination = i,
                       m.mreq.type = "JoinRequest",
                       m.mreq.node = k, 
                       receivedMsgs'= (receivedMsgs \{m}) \cup 
                         IF nh # i
                         THEN {[destination |-> nh, 
                                mreq |-> [type |-> "JoinRequest",
                                          rtable |-> AddToTable(GetRTableContent(rtable[i]), m.mreq.rtable, i),
                                          node |-> k]]}
                         ELSE {[destination |-> i, mreq |-> [type |-> "NoLegalRoute", key |-> k]]},
                       UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>
            PROVE TypeInvariant'
         <4>0. m.mreq \in JReq
           BY SlowestZenon, <3>1 DEF TypeInvariant, DMsg, MReq, JReq, JRpl, Prb, PRpl, Look, LReq, BLS, NoLR
         <4>1. receivedMsgs' \in SUBSET DMsg
            <5>1. CASE nh # i 
               <6>1. [type |-> "JoinRequest",
                      rtable |-> AddToTable(GetRTableContent(rtable[i]), m.mreq.rtable, i),
                      node |-> k] \in JReq
                  BY <4>0, GetRTableContentType, AddToTableType DEF TypeInvariant, JReq
               <6>4. [destination |-> nh, 
                      mreq |-> [type |-> "JoinRequest",
                                rtable |-> AddToTable(GetRTableContent(rtable[i]), m.mreq.rtable, i),
                                node |-> k]
                     ] \in DMsg
                  BY <6>1, <3>0, <5>1 DEF DMsg, MReq
               <6>9. QED BY <3>1, <5>1, <6>4 DEF TypeInvariant
            <5>2. CASE nh = i         
               <6>. [destination |-> i, mreq |-> [type |-> "NoLegalRoute", key |-> k]] \in DMsg
                  BY DEF DMsg, MReq, NoLR
               <6>. QED BY <3>1, <5>2 DEF TypeInvariant
            <5>3. QED BY <5>1, <5>2 
         <4>3. QED BY <3>1, <4>1 DEF TypeInvariant
      <3>2.QED BY <3>1, <2>22 DEF RouteJoinRequest
   <2>3. ASSUME NEW i \in I, NEW j \in I,
                Deliver(i,j)
         PROVE  TypeInvariant'
      BY <2>3 DEF Deliver, TypeInvariant
   <2>4. ASSUME NEW i \in I,
                ReceiveLSProbe(i)
         PROVE  TypeInvariant'  
      <3>1. ASSUME NEW m \in receivedMsgs,
                   m.destination = i,
                   m.mreq.type = "LSProbe",
                   ReceiveLSProbeInner(i, m) 
            PROVE  TypeInvariant' 
         <4>. DEFINE j == m.mreq.node
         <4>. DEFINE fi == failed[i] \ {j}
         <4>. DEFINE ls1 == IF j \in GetLSetContent(lset[i]) 
                              THEN lset[i]
                              ELSE AddToLSet({j}, lset[i])
         <4>. DEFINE prb1 == GetLSetContent(ls1) \cap m.mreq.failed
         <4>. DEFINE prb2 == GetLSetContent(AddToLSet((GetLSetContent(m.mreq.lset) \ fi), ls1))
                               \ GetLSetContent(ls1)
         <4>. DEFINE prb == (prb1 \cup prb2) \ (probing[i] \cup fi) 
         <4>. DEFINE newm == [type |-> "LSProbeReply",  
                  node |-> i,
                  lset |-> lset[i],
                  failed |-> fi]
         <4>01. failed' = [failed EXCEPT ![i] = fi]
            BY <3>1 DEF ReceiveLSProbeInner
         <4>02. rtable' = [rtable EXCEPT ![i] = AddToTable({j}, @, i)]
            BY <3>1 DEF ReceiveLSProbeInner
         <4>03. lset'   = [lset EXCEPT ![i] = ls1]
            BY <3>1 DEF ReceiveLSProbeInner
         <4>04. probing'= [probing EXCEPT ![i] = @ \cup prb] 
            BY <3>1 DEF ReceiveLSProbeInner
         <4>06. receivedMsgs' = (receivedMsgs \ {m}) 
                           \cup { [destination |-> j, mreq |-> newm]} 
                           \cup Probe(i, ls1, fi, prb)
            BY <3>1, SimplifyAndSolve DEF ReceiveLSProbeInner
         <4>07. UNCHANGED <<lease, status, grant>>
            BY <3>1 DEF ReceiveLSProbeInner
         <4>1.  m.mreq \in Prb
            BY SlowestZenon, <3>1 DEF TypeInvariant, DMsg, MReq, JReq, JRpl, Prb, PRpl, Look, LReq, BLS, NoLR
         <4>2. /\ j \in I
               /\ m.mreq.failed \in SUBSET I
               /\ m.mreq.lset \in LSet
            BY <3>1, <4>1 DEF Prb
         <4>3. /\ fi \in SUBSET I
               /\ ls1 \in LSet
               /\ lset[i] \in LSet
            BY <3>1, <4>2, AddToLSetType, RemoveFromLSetType,
            SlowestZenon DEF TypeInvariant     
         <4>4. prb1 \in SUBSET I
            BY <3>1, <4>2
         <4>5. prb2 \in SUBSET I
           <5>1. GetLSetContent(m.mreq.lset) \in SUBSET I
             BY <4>2, GetLSetContentType
           <5>2. AddToLSet((GetLSetContent(m.mreq.lset) \ fi), ls1) \in LSet
             BY <5>1, <4>3, AddToLSetType
           <5>3. QED
             BY <3>1, <5>2, GetLSetContentType
         <4>6. newm \in PRpl
             BY <3>1, <4>3 DEF PRpl
         <4>7. prb \in SUBSET I
            BY <4>5,<4>4,<4>3 DEF TypeInvariant
         <4>11. failed' \in [I -> SUBSET I]
            BY <4>01, <4>3 DEF TypeInvariant
         <4>12. rtable' \in [I -> RTable]
            BY <4>02, <4>2, AddToTableType DEF TypeInvariant
         <4>13. lset' \in [I -> LSet]
            BY <4>03, <4>3 DEF TypeInvariant
         <4>. HIDE DEF prb1, prb2, fi
         <4>14. probing' \in [I -> SUBSET I]
            BY <4>04, <4>4, <4>5 DEF TypeInvariant
         <4>16. receivedMsgs' \in SUBSET DMsg
            <5>1. (receivedMsgs \ {m}) \in SUBSET DMsg
               BY DEF TypeInvariant
            <5>2. [destination |-> j, mreq |-> newm] \in DMsg
               BY <4>2, <4>6 DEF DMsg, MReq
            <5>3. Probe(i, ls1, fi, prb) \in SUBSET DMsg
               BY <2>4, <4>3, <4>7, ProbeType
            <5>9. QED BY <4>06, <5>1, <5>2,<5>3
         <4>17./\ lease' \in [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
               /\ status' \in  [I -> {"ready", "ok", "wait", "dead"}]
            BY <4>07 DEF TypeInvariant
         <4>. HIDE DEF j
         <4>18. \A k \in I: lset'[k].node = k
            <5>1. ls1.node = i
               BY <4>2, ls1 = IF j \in GetLSetContent(lset[i]) 
                              THEN lset[i]
                              ELSE AddToLSet({j}, lset[i]), 
               AddToLSetNoChangeNode DEF TypeInvariant
            <5>9. QED BY <5>1, lset'   = [lset EXCEPT ![i] = ls1] DEF TypeInvariant
         <4>99. QED BY <4>11,<4>12, <4>13, <4>14, <4>16, <4>17, <4>18 DEF TypeInvariant
      <3>2.QED BY <3>1, <2>4, SlowestZenon DEF ReceiveLSProbe
   <2>5. ASSUME NEW i \in I,
                ReceiveLSPrRpl(i)
         PROVE  TypeInvariant'
     \*Prover cannot handle too many assumptions at once, how to apply divide and conquer technique? 
     \* Here we cannot prove
      <3>1. ASSUME NEW m \in receivedMsgs,
                   m.destination = i,
                   m.mreq.type = "LSProbeReply",
                   ReceiveLSPrRplInner(i,m)
            PROVE  TypeInvariant' 
        (* The following auxiliary definitions are copied from the LET-bindings in the action definition. *)
        <4>. DEFINE j == m.mreq.node
        <4>. DEFINE Ls == m.mreq.lset
        <4>. DEFINE fi == failed[i] \ {j}
        <4>. DEFINE ls1 == IF j \in GetLSetContent(lset[i]) 
                              THEN lset[i]
                              ELSE AddToLSet({j}, lset[i])
        \*<4>. DEFINE ls2 == RemoveFromLSet(m.mreq.failed, ls1)
        <4>. DEFINE lprim == GetLSetContent(AddToLSet((GetLSetContent(Ls) \ fi), ls1))
        <4>. DEFINE prb1 == (GetLSetContent(ls1) \cap m.mreq.failed )\ (probing[i] \cup fi)
        <4>. DEFINE prb2 == lprim \ (GetLSetContent(ls1) \cup probing[i] \cup fi \cup prb1)
        <4>. DEFINE prb3 == ((probing[i] \cup prb1 \cup prb2) \ failed[i]) \ {j} 
        <4>. DEFINE shouldBeOK == 
              /\ status[i] = "wait" 
              /\ prb3={}
              /\ Overlaps(ls1)\/IsComplete(ls1)
        <4>1. rtable' = [rtable EXCEPT ![i] = AddToTable({j}, @, i)]
          BY <3>1 DEF ReceiveLSPrRplInner
        <4>2. lset'   = [lset EXCEPT ![i] = ls1]
          BY <3>1 DEF ReceiveLSPrRplInner
        <4>3. failed' = [failed EXCEPT ![i] = IF prb3={} /\ IsComplete(ls1) THEN {} ELSE fi]
          BY <3>1 DEF ReceiveLSPrRplInner
        <4>4. probing'= [probing EXCEPT ![i] = prb3]
          BY <3>1 DEF ReceiveLSPrRplInner
        <4>5. status'= [status EXCEPT ![i] = IF shouldBeOK THEN "ok" ELSE @]
          BY <3>1 DEF ReceiveLSPrRplInner
        <4>6. receivedMsgs' = (receivedMsgs \ {m}) 
                              \cup Probe(i, ls1, fi, prb1)
                              \cup Probe(i, ls1, fi, prb2)
          BY <3>1 DEF ReceiveLSPrRplInner
        <4>7. UNCHANGED <<lease, grant>>
          BY <3>1 DEF ReceiveLSPrRplInner
        <4>49. m.mreq.type = "LSProbeReply" /\ m \in DMsg
          BY <3>1 DEF TypeInvariant, DMsg
        <4>50. m.mreq \in PRpl
          BY <4>49 DEF TypeInvariant, DMsg, MReq, JReq, JRpl, Prb, PRpl, Look, LReq, BLS, NoLR
        (* We now prove typing information for each of the auxiliary operators defined above, then hide their definitions.
           This helps to keep the terms small enough for the prover to handle them. *)
        <4>51. j \in I
          BY <4>50 DEF PRpl
        <4>. HIDE DEF j
        <4>52. fi \in SUBSET I
          BY <4>51 DEF TypeInvariant
        <4>. HIDE DEF fi
        <4>53. ls1 \in LSet
          BY <4>51, AddToLSetType DEF TypeInvariant
        <4>533. ls1.node = i
           BY <4>51,  
           AddToLSetNoChangeNode DEF TypeInvariant
        <4>. HIDE DEF ls1
        <4>55. lprim \in SUBSET I
          <5>1. (GetLSetContent(m.mreq.lset) \ fi) \in SUBSET I
            BY GetLSetContentType, <4>50, <4>52 DEF PRpl
          <5>2. AddToLSet((GetLSetContent(m.mreq.lset)\ fi), ls1) \in LSet
            BY AddToLSetType, <5>1, <4>53
          <5>3. QED BY <5>2, GetLSetContentType
        <4>. HIDE DEF lprim
        <4>56. prb1 \in SUBSET I
          BY GetLSetContentType, <4>53, <4>50, <4>52 DEF PRpl, TypeInvariant
        <4>. HIDE DEF prb1
        <4>57. prb2 \in SUBSET I
          BY <4>55, <4>53, <4>52, <4>56, GetLSetContentType DEF TypeInvariant
        <4>. HIDE DEF prb2
        <4>58. prb3 \in SUBSET I
          BY <4>56, <4>57 DEF TypeInvariant
        <4>. HIDE DEF prb3
        <4>91. rtable' \in [I -> RTable]
          BY <4>1, <4>51, AddToTableType DEF TypeInvariant
        <4>92. receivedMsgs' \in SUBSET DMsg
          BY <4>6, ProbeType, <4>53, <4>53, <4>52, <4>56, <4>57 DEF TypeInvariant 
        <4>93. /\ status' \in [I -> {"ready", "ok", "wait", "dead"}]
               /\ lease' \in [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
          BY <4>5, <4>7 DEF TypeInvariant
        <4>95. lset' \in [I -> LSet]
          BY <4>2, <4>53 DEF TypeInvariant
        <4>96. probing'  \in [I -> SUBSET I]
          BY <4>4, <4>58 DEF TypeInvariant
        <4>97. failed' \in [I -> SUBSET I]
          BY <4>3, <4>52 DEF TypeInvariant
        <4>98. \A k \in I: lset'[k].node = k
           BY <4>533, lset'   = [lset EXCEPT ![i] = ls1] DEF TypeInvariant
        <4>99. QED BY <4>91,<4>92,<4>93,<4>95,<4>96,<4>97, <4>98 DEF TypeInvariant
      <3>99.QED 
        BY <2>5, <3>1 DEF ReceiveLSPrRpl
   <2>6. ASSUME NEW i \in I,
                ReceiveJoinRequest(i)
         PROVE  TypeInvariant'
      <3>1. ASSUME NEW m \in receivedMsgs,
            m.destination = i,
            m.mreq.type = "JoinRequest",
            NEW newmreq, newmreq=[type |-> "JoinReply",  
                                rtable |-> m.mreq.rtable,
                                  lset |-> lset[i]],
            NEW newm, newm =  [destination |-> m.mreq.node,
                           mreq |-> newmreq ],
            receivedMsgs'= (receivedMsgs \{m}) \cup {newm},
            UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>
            PROVE TypeInvariant'
         <4>7. receivedMsgs' \in SUBSET DMsg
            <5>101. m.mreq \in JReq
            BY SlowestZenon, <3>1 DEF TypeInvariant, DMsg, MReq, JReq, JRpl, Prb, PRpl, Look, LReq, BLS, NoLR
            <5>1. m.mreq.node \in I
               BY <5>101 DEF JReq
            <5>2. m.mreq.rtable \in RTable
               BY <5>101 DEF JReq
            <5>3. newmreq \in MReq
               <6>1. lset[i] \in LSet
                  BY <2>6 DEF TypeInvariant
               <6>8. newmreq \in JRpl
                  BY <3>1, <5>2, <6>1 DEF JRpl, TypeInvariant
               <6>9. QED BY <6>8 DEF MReq
            <5>4. newm \in DMsg
               BY <3>1, <5>1, <5>3 DEF DMsg
            <5>5. (receivedMsgs \{m}) \in SUBSET DMsg
               BY <3>1 DEF TypeInvariant
            <5>6. (receivedMsgs \{m}) \cup {newm} \in SUBSET DMsg
               BY <5>5, <5>4
            <5>9.QED BY <3>1, <5>6
         <4>8. /\ status' \in [I -> {"ready", "ok", "wait", "dead"}]
               /\ lease' \in [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
               /\ rtable' \in [I -> RTable]
               /\ lset' \in [I -> LSet]/\ \A k \in I: lset'[k].node = k
               /\ probing'  \in [I -> SUBSET I]
               /\ failed' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>9.QED BY <4>7, <4>8 DEF TypeInvariant
      <3>9.QED BY <3>1, <2>6 DEF ReceiveJoinRequest    
   <2>7. ASSUME NEW i \in I,
                ReceiveJoinReply(i)
         PROVE  TypeInvariant'
      <3>1. ASSUME NEW m \in receivedMsgs,
            m.destination = i,
            m.mreq.type = "JoinReply",
            NEW newrtable,   
                newrtable =AddToTable(GetLSetContent(m.mreq.lset)
                             \cup GetRTableContent(m.mreq.rtable), 
                              rtable[i], i),
            NEW newlset,
                newlset = AddToLSet(GetLSetContent(m.mreq.lset), lset[i]),
            NEW toprob, toprob = GetLSetContent(newlset) \ {i},
            NEW probmsgs, probmsgs = Probe(i, newlset, {}, toprob),
            rtable'= [rtable EXCEPT ![i] = newrtable],
            lset'= [lset EXCEPT ![i] = newlset],
            probing'= [probing EXCEPT ![i] = toprob],
            failed'=[failed EXCEPT ![i] = {}],
            receivedMsgs'= (receivedMsgs \ {m}) \cup probmsgs,
            UNCHANGED <<status, lease, grant>>
         PROVE TypeInvariant' 
         <4>1. m.mreq \in JRpl
            BY SlowestZenon, <3>1 DEF TypeInvariant, DMsg, MReq, JReq, JRpl, Prb, PRpl, Look, LReq, BLS, NoLR
         <4>2. newrtable \in RTable
            <5>1. m.mreq.lset \in LSet
               BY <4>1 DEF JRpl
            <5>2. m.mreq.rtable \in RTable
               BY <4>1 DEF JRpl
            <5>3. i \in I
               BY <2>7
            <5>4. rtable[i] \in RTable
               BY <5>3 DEF TypeInvariant
            <5>5. GetLSetContent(m.mreq.lset) \in SUBSET I
               BY GetLSetContentType, <5>1
            <5>6. GetRTableContent(m.mreq.rtable) \in SUBSET I
               BY GetRTableContentType, <5>2
            <5>9. QED BY <3>1, <5>3,<5>4, <5>5,<5>6,AddToTableType 
         <4>3. newlset \in LSet /\ newlset.node = i
            <5>1. m.mreq.lset \in LSet
               BY <4>1 DEF JRpl
            <5>2. lset[i] \in LSet
               BY <2>7 DEF TypeInvariant
            <5>3. GetLSetContent(m.mreq.lset) \in SUBSET I
               BY <5>1, GetLSetContentType 
            <5>4. newlset \in LSet
               BY <3>1, AddToLSetType, <5>3, <5>2
            <5>5. newlset.node = i
               BY <3>1, AddToLSetNoChangeNode, <5>3, <5>2 DEF TypeInvariant
            <5>9.QED BY <5>4, <5>5
         <4>4. toprob \in SUBSET I
            BY <3>1, GetLSetContentType, <4>3, <2>7
         <4>5. probmsgs \in SUBSET DMsg
            <5>1. i \in I
               BY <2>7
            <5>2. newlset \in LSet
               BY <4>3
            <5>3. {} \in SUBSET I
               OBVIOUS
            <5>4. toprob \in SUBSET I
               BY <4>4
            <5>5. Probe(i, newlset, {}, toprob) \in SUBSET DMsg
               BY ProbeType, <5>1, <5>2, <5>3, <5>4
            <5>9.QED BY <3>1, <5>5
         <4>11. rtable' \in [I -> RTable]
            BY <3>1, <4>2 DEF TypeInvariant           
         <4>12. lset' \in   [I -> LSet]
            BY <3>1, <4>3 DEF TypeInvariant
         <4>13. probing' \in [I -> SUBSET I]
            BY <3>1, <4>4 DEF TypeInvariant
         <4>14. failed' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>15. receivedMsgs' \in SUBSET DMsg
            BY <3>1, <4>5 DEF TypeInvariant
         <4>16. /\ status' \in [I -> {"ready", "ok", "wait", "dead"}]
                /\ lease' \in [I -> SUBSET I]
                /\ grant' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>17. \A k \in I: lset'[k].node = k
            BY <4>3, lset'   = [lset EXCEPT ![i] = newlset] DEF TypeInvariant
         <4>99.QED BY <4>11,<4>12,<4>13,<4>14,<4>15,<4>16, <4>17  DEF TypeInvariant
      <3>9.QED BY <3>1, <2>7 DEF ReceiveJoinReply
   <2>8. ASSUME NEW i \in I,
                RequestLease(i)
         PROVE  TypeInvariant'
      <3>1. ASSUME NEW ln, ln = LeftNeighbor(lset[i]),
            NEW rn, rn =  RightNeighbor(lset[i]),
            NEW llr, llr =   IF ~ (ln \in lease[i])
                             THEN {[destination |-> ln, 
                                  mreq |-> [type |-> "LeaseRequest",
                                            node |-> i]]}
                             ELSE {},
            NEW rlr, rlr =   IF ~ (rn \in lease[i])
                             THEN {[destination |-> rn, 
                                  mreq |-> [type |-> "LeaseRequest",
                                            node |-> i]]}
                             ELSE {},
            receivedMsgs' = (receivedMsgs \cup llr) \cup rlr,
            UNCHANGED <<status, lset, rtable, probing, failed, lease, grant>>
         PROVE TypeInvariant'
         <4>1. receivedMsgs' \in SUBSET DMsg
            <5>1. lset[i] \in LSet
               BY <2>8 DEF TypeInvariant
            <5>2. ln \in I
               BY <3>1, <5>1, LeftNeighborType
            <5>3. rn \in I
               BY <3>1, <5>1, RightNeighborType
            <5>4. [type |-> "LeaseRequest",
                         node |-> i] \in LReq
               BY <2>8 DEF LReq
            <5>7. llr \in SUBSET DMsg
               <6>1. CASE ~ (ln \in lease[i])
                  <7>2. [destination |-> ln, 
                                   mreq |-> [type |-> "LeaseRequest",
                                   node |-> i]] \in DMsg
                     BY <5>2, <5>4 DEF MReq, DMsg
                  <7>3.llr = {[destination |-> ln, 
                                 mreq |-> [type |-> "LeaseRequest",
                                 node |-> i]]}
                     BY <3>1, <6>1
                  <7>9.QED BY <6>1, <7>2, <7>3
               <6>2. CASE (ln \in lease[i])
                  BY <3>1, <6>2
               <6>9.QED BY <6>1, <6>2
            <5>8. rlr \in SUBSET DMsg
               <6>1. CASE  ~(rn \in lease[i])
                  <7>2. [destination |-> rn, 
                                   mreq |-> [type |-> "LeaseRequest",
                                   node |-> i]] \in DMsg
                     BY <5>3, <5>4 DEF MReq, DMsg
                  <7>3.rlr = {[destination |-> rn, 
                                 mreq |-> [type |-> "LeaseRequest",
                                 node |-> i]]}
                     BY <3>1, <6>1
                  <7>9.QED BY <6>1, <7>2, <7>3
               <6>2. CASE (rn \in lease[i])
                  BY <3>1, <6>2
               <6>9.QED BY <6>1, <6>2
            <5>9. QED BY <3>1, <5>8, <5>7 DEF TypeInvariant
         <4>2. /\ status' \in [I -> {"ready", "ok", "wait", "dead"}]
               /\ lease' \in [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
               /\ rtable' \in [I -> RTable]
               /\ lset' \in [I -> LSet] /\ \A k \in I: lset'[k].node = k
               /\ probing'  \in [I -> SUBSET I]
               /\ failed' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>9.QED BY <4>1, <4>2 DEF TypeInvariant
      <3>9.QED BY <2>8, <3>1 DEF RequestLease
   <2>9. ASSUME NEW i \in I,
                ReceiveLReq(i)
         PROVE  TypeInvariant'
      <3>1. ASSUME NEW m \in receivedMsgs,
            m.destination = i,
            m.mreq.type = "LeaseRequest",
            grant' = [grant EXCEPT ![i] = 
                  IF m.mreq.node \in {LeftNeighbor(lset[i]), RightNeighbor(lset[i])}
                  THEN @ \cup {m.mreq.node} 
                  ELSE @],
            receivedMsgs' = (receivedMsgs \ {m})
                  \cup {[destination |-> m.mreq.node, 
                              mreq |-> [type |-> "BroadcastLSet",
                                        lset |-> lset[i],
                                        grant|-> IF 
                                                   m.mreq.node \in 
                                                   {LeftNeighbor(lset[i]), RightNeighbor(lset[i])}
                                                 THEN TRUE
                                                 ELSE FALSE]]},
            UNCHANGED <<status, rtable, lset, probing, failed, lease>>      
         PROVE TypeInvariant' 
         <4>0. m.mreq.node \in I 
            <5>1. m \in DMsg
               BY <3>1 DEF TypeInvariant
            <5>2. m.mreq \in LReq
               BY SlowestZenon, <3>1 DEF TypeInvariant, DMsg, MReq, JReq, JRpl, Prb, PRpl, Look, LReq, BLS, NoLR
            <5>3. QED BY <5>2 DEF LReq
         (*
         <4>. DEFINE Status == {0,1,2}
         <4>1. lease' \in [I -> [I -> Status]]
            <5>. 2 \in Status OBVIOUS
            <5>. lease \in [I -> [I -> Status]] BY DEF TypeInvariant
            <5>. lease[i][m.mreq.node] \in Status BY <4>0
            <5>. HIDE DEF Status
            <5>2. QED BY SimplifyAndSolve, <4>0, <3>1(*, <5>1*)
            *)
         <4>1. grant' \in [I -> SUBSET I]
            <5>0. grant[i] \in SUBSET I
               BY DEF TypeInvariant
            <5>1. (grant[i] \cup {m.mreq.node})  \in SUBSET I
               BY <4>0 DEF TypeInvariant 
            <5>7. CASE m.mreq.node \in {LeftNeighbor(lset[i]), RightNeighbor(lset[i])}
               BY <5>7, <5>1, <3>1 DEF TypeInvariant
            <5>8. CASE ~ (m.mreq.node \in {LeftNeighbor(lset[i]), RightNeighbor(lset[i])})
               <6>1. grant' = grant
                  BY <3>1, <5>8 DEF TypeInvariant
               <6>2. QED BY <6>1 DEF TypeInvariant
            <5>9. QED BY <5>7, <5>8
         <4>2. receivedMsgs' \in SUBSET DMsg
            <5>1. m \in DMsg
               BY DEF TypeInvariant
            <5>2. [destination |-> m.mreq.node, 
                              mreq |-> [type |-> "BroadcastLSet",
                                        lset |-> lset[i],
                                        grant|-> IF 
                                                   m.mreq.node \in 
                                                   {LeftNeighbor(lset[i]), RightNeighbor(lset[i])}
                                                 THEN TRUE
                                                 ELSE FALSE]] \in DMsg
               <6>1.[type |-> "BroadcastLSet",
                     lset |-> lset[i],
                     grant|-> IF 
                               m.mreq.node \in 
                               {LeftNeighbor(lset[i]), RightNeighbor(lset[i])}
                             THEN TRUE
                             ELSE FALSE] \in BLS
                  <7>1. lset[i] \in LSet
                     BY <3>1 DEF TypeInvariant
                  <7>2. QED BY <7>1 DEF BLS
               <6>2.[type |-> "BroadcastLSet",
                     lset |-> lset[i],
                     grant|-> IF 
                               m.mreq.node \in 
                               {LeftNeighbor(lset[i]), RightNeighbor(lset[i])}
                             THEN TRUE
                             ELSE FALSE] \in MReq
                  BY <6>1 DEF MReq
               <6>9.QED BY <4>0, <6>2 DEF DMsg          
            <5>9.QED BY <3>1, <5>1, <5>2 DEF TypeInvariant
         <4>3. /\ status' \in [I -> {"ready", "ok", "wait", "dead"}]
               /\ rtable' \in [I -> RTable]
               /\ lset' \in [I -> LSet]/\ \A k \in I: lset'[k].node = k
               /\ probing'  \in [I -> SUBSET I]
               /\ failed' \in [I -> SUBSET I]
               /\ lease' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>9. QED BY <4>1, <4>2, <4>3 DEF TypeInvariant
      <3>9.QED BY <2>9, <3>1 DEF ReceiveLReq
   <2>10. ASSUME NEW i \in I,
                ReceiveBLS(i)
         PROVE  TypeInvariant'
      <3>1. ASSUME NEW m \in receivedMsgs,
            m.destination = i,
            m.mreq.type = "BroadcastLSet",
            NEW ls, 
             ls = AddToLSet(GetLSetContent(m.mreq.lset)\ failed[i] , lset[i]),
            NEW ln, ln = LeftNeighbor(ls),
            NEW rn, rn = RightNeighbor(ls),
            NEW newlease, 
            newlease = [lease EXCEPT ![i] = 
                       IF /\ m.mreq.lset.node \in  {ln, rn} 
                          /\ m.mreq.grant = TRUE
                       THEN @ \cup {m.mreq.lset.node}
                       ELSE @],
            NEW shouldBeReady, 
            shouldBeReady = (ln \in newlease[i] /\ rn \in newlease[i]),
            lset' = [lset EXCEPT ![i] = ls],
            lease' = newlease,
            status' = [status EXCEPT ![i] =   IF shouldBeReady
                                           THEN "ready"
                                           ELSE @ ],
            receivedMsgs' = (receivedMsgs \ {m}),
            UNCHANGED <<rtable, probing, failed, grant>>
         PROVE TypeInvariant'
         <4>1. m.mreq \in BLS
            BY SlowestZenon, <3>1 DEF TypeInvariant, DMsg, MReq, JReq, JRpl, Prb, PRpl, Look, LReq, BLS, NoLR
         <4>2. m.mreq.lset \in LSet
            BY <4>1 DEF BLS
         <4>3. GetLSetContent(m.mreq.lset)\(failed[i] \cup probing[i]) \in SUBSET I
            BY <4>1, <4>2, GetLSetContentType DEF TypeInvariant
         <4>4. lset[i] \in LSet
            BY TypeInvariant DEF TypeInvariant
         <4>5. ls.node = i
            BY ls = AddToLSet(GetLSetContent(m.mreq.lset)\ failed[i] , lset[i]),
               <4>3, <4>4, AddToLSetNoChangeNode DEF TypeInvariant
         <4>20. \A k \in I: lset'[k].node = k
            BY <4>5, lset' = [lset EXCEPT ![i] = ls] DEF TypeInvariant
         <4>21. ls \in LSet
            BY <3>1, <4>1, <4>2, AddToLSetType, GetLSetContentType DEF TypeInvariant
         <4>22. ln \in I
            BY <3>1, LeftNeighborType, <4>21
         <4>23. rn \in I
            BY <3>1, RightNeighborType, <4>21
         <4>. DEFINE Status == {0, 1, 2}
         <4>24. newlease \in [I -> SUBSET I]
            <5>0. m.mreq.lset.node \in I BY <4>2 DEF LSet
            <5>1. lease[i] \cup {m.mreq.lset.node} \in SUBSET I
               BY <5>0 DEF TypeInvariant
            <5>2. CASE /\ m.mreq.lset.node \in  {ln, rn} 
                       /\ m.mreq.grant = TRUE
               <6>1. newlease = [lease EXCEPT ![i] = lease[i] \cup {m.mreq.lset.node}]
                  BY <3>1, <5>2 DEF TypeInvariant
               <6>2. QED BY <5>1, <6>1 DEF TypeInvariant
            <5>3. CASE ~(/\ m.mreq.lset.node \in  {ln, rn} 
                         /\ m.mreq.grant = TRUE)
               <6>1. newlease = [lease EXCEPT ![i] = lease[i]]
                  BY <3>1, <5>3 DEF TypeInvariant
               <6>2. QED BY <6>1, <5>3 DEF TypeInvariant
            <5>9. QED BY <5>2, <5>3
            (*1
            <5>1. m.mreq.lset.node \in I BY <4>2 DEF LSet
            <5>. 1 \in Status OBVIOUS
            <5>. lease[i][m.mreq.lset.node] \in Status BY <5>1 DEF TypeInvariant
            <5>2. lease \in [I -> [I -> Status]] BY DEF TypeInvariant
            <5>. HIDE DEF Status
            <5>3. QED BY SimplifyAndSolve, <5>1, <5>2, <3>1
            *)
         <4>25. lset' \in [I -> LSet]
            BY <3>1, <4>21 DEF TypeInvariant
         <4>26. lease' \in  [I -> SUBSET I]
            BY <3>1, <4>24
         <4>27. status' \in [I -> {"ready", "ok", "wait", "dead"}]
            BY <3>1 DEF TypeInvariant
         <4>28. receivedMsgs' \in SUBSET DMsg
            BY <3>1 DEF TypeInvariant
         <4>29./\ rtable \in [I -> RTable]
               /\ probing  \in [I -> SUBSET I]
               /\ failed \in [I -> SUBSET I]
               /\ grant \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>99.QED BY <3>1, <4>20, <4>25,<4>26,<4>27,<4>28,<4>29 DEF TypeInvariant
      <3>9. QED BY <2>10, <3>1 DEF ReceiveBLS
   <2>11. ASSUME NEW i \in I,
                NodeLeft(i)
         PROVE  TypeInvariant'
      <3>1.ASSUME status' = [status EXCEPT ![i] = "dead"],
           rtable' = [rtable EXCEPT ![i] = AddToTable({i}, InitRTable, i)],
           lset' = [lset EXCEPT ![i] = EmptyLS(i)],
           probing' = [probing EXCEPT ![i] = {}],
           failed' = [failed EXCEPT ![i] = {}],
           lease' = [lease EXCEPT ![i]= {}],
           grant'= [grant EXCEPT ![i]= {}],
           UNCHANGED <<receivedMsgs>>
         PROVE TypeInvariant'
         <4>1. status' \in [I -> {"ready", "ok", "wait", "dead"}]
            BY <3>1 DEF TypeInvariant
         <4>2. probing'  \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>3. receivedMsgs' \in SUBSET DMsg
            BY <3>1 DEF TypeInvariant
         <4>4. /\ lease' \in [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>5. rtable' \in [I -> RTable]
            BY <2>11, <3>1, AddToTableType, InitRTableType DEF TypeInvariant
         <4>6. lset' \in [I -> LSet]
            BY <2>11, <3>1, EmptyLST DEF   TypeInvariant
         <4>7. failed' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>8. \A k \in I: lset'[k].node = k
            BY <3>1, EmptyLST DEF TypeInvariant
         <4>9.QED BY <4>1,<4>2,<4>3,<4>4,<4>5,<4>6,<4>7, <4>8 DEF TypeInvariant
      <3>9.QED BY <2>11, <3>1 DEF NodeLeft
   <2>12. ASSUME NEW i \in I, NEW j \in I,
                LeaseExpired(i,j)
         PROVE  TypeInvariant'
      <3>1. ASSUME lease' = [lease EXCEPT ![i] = @ \{j}],
            status' = [status EXCEPT ![i] = 
                       IF /\ j \in {LeftNeighbor(lset[i]), RightNeighbor(lset[i])} 
                          /\ status[i] = "ready"
                       THEN "ok" 
                       ELSE status[i]],
            UNCHANGED <<receivedMsgs, rtable, lset, probing, failed, grant>>
         PROVE TypeInvariant'
         (*
         <4>.DEFINE Status == {0, 1, 2}
         <4>1. lease' \in [I -> [I -> Status]]
            <5>1. 0 \in Status OBVIOUS
            <5>2. lease \in [I -> [I -> Status]] BY DEF TypeInvariant
            <5>. HIDE DEF Status
            <5>9. QED BY <2>12, lease' = [lease EXCEPT ![i][j] = 0],  <5>1, <5>2, 
            SlowestZenon DEF TypeInvariant
         *)
         <4>1. lease' \in [I -> SUBSET I]
            BY <2>12, <3>1 DEF TypeInvariant
         <4>2. status' \in [I -> {"ready", "ok", "wait", "dead"}]
            BY <3>1 DEF TypeInvariant
         <4>3. /\ receivedMsgs \in SUBSET DMsg
               /\ rtable' \in [I -> RTable]
               /\ lset' \in [I -> LSet]/\ \A k \in I: lset'[k].node = k
               /\ probing'  \in [I -> SUBSET I]
               /\ failed' \in [I -> SUBSET I]
               /\ grant' \in  [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>9.QED BY <3>1, <4>1,<4>2,<4>3 DEF TypeInvariant
      <3>9.QED BY <2>12, <3>1 DEF LeaseExpired
   <2>121. ASSUME NEW i \in I, NEW j \in I,
                GrantExpired(i,j)
         PROVE  TypeInvariant'
      <3>1. ASSUME grant'= [grant EXCEPT ![i] = @ \ {j}],
            UNCHANGED <<receivedMsgs, rtable, lset, probing, failed, lease, status>>
         PROVE TypeInvariant'
         <4>1. grant' \in [I -> SUBSET I]
            BY <2>121, <3>1 DEF TypeInvariant
         <4>3. /\ receivedMsgs' \in SUBSET DMsg
               /\ rtable' \in [I -> RTable]
               /\ lset' \in [I -> LSet]/\ \A k \in I: lset'[k].node = k
               /\ probing'  \in [I -> SUBSET I]
               /\ failed' \in [I -> SUBSET I]
               /\ lease' \in  [I -> SUBSET I]
               /\ status' \in [I -> {"ready", "ok", "wait", "dead"}]
            BY <3>1 DEF TypeInvariant
         <4>9.QED BY <3>1, <4>1,<4>3 DEF TypeInvariant
      <3>9.QED BY <2>121, <3>1 DEF GrantExpired
   <2>13. ASSUME NEW i \in I, NEW j \in I,
                SuspectFaulty(i,j)
         PROVE  TypeInvariant'
      <3>1. ASSUME receivedMsgs'= receivedMsgs \cup Probe(i, lset[i], failed[i], {j}),
            probing'=[probing EXCEPT ![i]= @\cup {j}],
            UNCHANGED <<rtable, lset, failed, lease, status, grant>>
         PROVE TypeInvariant' 
         <4>0. {j} \in SUBSET I
            BY <2>13
         <4>1. receivedMsgs' \in SUBSET DMsg
            BY <4>0, <3>1, ProbeType DEF TypeInvariant
         <4>2. probing' \in [I -> SUBSET I]
            BY <3>1, <2>13 DEF TypeInvariant
         <4>3. /\ status' \in [I -> {"ready", "ok", "wait", "dead"}]
               /\ rtable' \in [I -> RTable]
               /\ lset' \in [I -> LSet]
               /\ failed' \in [I -> SUBSET I]
               /\ lease' \in  [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>9.QED BY <3>1, <4>1,<4>2,<4>3 DEF TypeInvariant
      <3>9.QED BY <2>13, <3>1 DEF SuspectFaulty
   <2>14. ASSUME NEW i \in I, NEW j \in I,
                ProbeTimeOut(i,j)
         PROVE  TypeInvariant'
      <3>1. ASSUME failed' = [failed EXCEPT ![i] = @\cup {j}],
            probing' = [probing EXCEPT ![i] = @ \ {j}],
            lset' = [lset EXCEPT ![i] = IF ~(j \in grant[i]) /\ j \in GetLSetContent(@)
                               THEN RemoveFromLSet({j},@) 
                               ELSE @],
            receivedMsgs' = receivedMsgs \
                          IF \E m \in receivedMsgs: m.mreq.type = "LSProbe"
                                /\ m.mreq.node = i
                                /\ m.destination = j
                          THEN  {m \in receivedMsgs: m.mreq.type = "LSProbe"
                                   /\ m.mreq.node = i
                                   /\ m.destination = j}
       
                          ELSE {},
            status'=[status EXCEPT ![i] = IF ~(j \in grant[i]) /\ j \in GetLSetContent(lset[i]) THEN "wait" ELSE @], 
            lease'= [lease EXCEPT ![i] = @ \ {j}],
            UNCHANGED <<rtable, grant>>
         PROVE TypeInvariant'
         <4>2. RemoveFromLSet({j},lset[i]).node = i
            BY <2>14, TypeInvariant, RemoveFromLSetNoChangeNode DEF TypeInvariant
         <4>3. \A k \in I: lset'[k].node = k
            BY <4>2, <3>1 DEF TypeInvariant
         <4>4. failed' \in [I -> SUBSET I]
            BY <2>14, <3>1 DEF TypeInvariant 
         <4>5. probing' \in [I -> SUBSET I]
            BY <3>1, <2>14 DEF TypeInvariant
         <4>6. lset' \in  [I -> LSet]
            BY <3>1, <2>14, RemoveFromLSetType DEF TypeInvariant
         <4>7. receivedMsgs' \in SUBSET DMsg
            BY <3>1 DEF TypeInvariant
         <4>8. /\ status' \in [I -> {"ready", "ok", "wait", "dead"}]
               /\ rtable' \in [I -> RTable]
               /\ lease' \in [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>9.QED BY <3>1, <4>3, <4>4, <4>5,<4>6,<4>7,<4>8 DEF TypeInvariant 
     <3>9.QED BY <2>14, <3>1 DEF ProbeTimeOut
   <2>15. ASSUME NEW i \in I, NEW j \in I,
                DeclareDead(i,j)
         PROVE  TypeInvariant'
      <3>1. ASSUME lset' = [lset EXCEPT ![i] = RemoveFromLSet({j},@)],
            status'= [status EXCEPT ![i] = "wait"] ,
            UNCHANGED <<receivedMsgs, rtable, lease, probing, failed, grant>>
         PROVE TypeInvariant' 
         <4>1. lset' \in [I -> LSet]
            BY <3>1, <2>15, RemoveFromLSetType DEF TypeInvariant
         <4>2. \A k \in I: lset'[k].node = k
            <5>1. {j} \in SUBSET I
               BY <2>15
            <5>2. lset[i] \in LSet
               BY TypeInvariant DEF TypeInvariant
            <5>3. RemoveFromLSet({j},lset[i]).node = i
               BY <5>1,<5>2, RemoveFromLSetNoChangeNode, 
               TypeInvariant DEF TypeInvariant
            <5>5. QED BY <3>1, <5>3 DEF TypeInvariant
         <4>7. status' \in [I -> {"ready", "ok", "wait", "dead"}]
            BY <3>1 DEF TypeInvariant
         <4>8./\ receivedMsgs \in SUBSET DMsg
              /\ lease \in [I -> SUBSET I]
              /\ rtable \in [I -> RTable]
              /\ probing  \in [I -> SUBSET I]
              /\ failed \in [I -> SUBSET I]
              /\ grant \in [I -> SUBSET I]
            BY <2>15, RemoveFromLSetType DEF TypeInvariant
         <4>9.QED BY <3>1, <4>1, <4>2, <4>7, <4>8 DEF TypeInvariant
      <3>2. QED BY <2>15, <3>1 DEF  DeclareDead   
   <2>16. ASSUME NEW i \in I, NEW seed \in I,
                 Join(i, seed)
         PROVE  TypeInvariant'
      <3>1. ASSUME  receivedMsgs'= receivedMsgs \cup 
                    {[destination |-> seed, 
                      mreq |-> [
                                type |-> "JoinRequest", 
                               rtable |-> InitRTable, 
                               node |-> i]
                     ]},
                    status' = [status EXCEPT ![i]="wait"],
                    UNCHANGED <<rtable, lset, probing, failed, lease, grant>>
          PROVE TypeInvariant'
         <4>1. receivedMsgs' \in SUBSET DMsg
            <5>7. [type |-> "JoinRequest", 
                   rtable |-> InitRTable, 
                     node |-> i] \in JReq
               BY <2>16, InitRTableType DEF JReq
            <5>8. [destination |-> seed, 
                      mreq |-> [
                                type |-> "JoinRequest", 
                               rtable |-> InitRTable, 
                               node |-> i]
                     ] \in DMsg
               BY <2>16, <5>7 DEF MReq, DMsg
            <5>9.QED BY <3>1, <5>8 DEF TypeInvariant 
         <4>2. status' \in [I -> {"ready", "ok", "wait", "dead"}]
            BY <2>16, <3>1 DEF TypeInvariant
         <4>8.    /\ lease' \in [I -> SUBSET I]
                  /\ grant' \in [I -> SUBSET I]
                  /\ rtable' \in [I -> RTable]
                  /\ lset' \in [I -> LSet]/\ \A k \in I: lset'[k].node = k
                  /\ probing'  \in [I -> SUBSET I]
                  /\ failed' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>9. QED BY <4>1,<4>2,<4>8 DEF TypeInvariant
      <3>9.QED BY <2>16, <3>1 DEF Join
   <2>17. ASSUME NEW i \in I,
                 LSRepair(i)
         PROVE  TypeInvariant'
      <3>1. ASSUME 
           NEW lm, lm = {LeftMost(lset[i])},
           NEW rm, rm = {RightMost(lset[i])},
           NEW newprob,
           newprob = 
            IF Lenth(lset[i].left) < L /\ Lenth(lset[i].right) < L
            THEN lm \cup rm
            ELSE IF Lenth(lset[i].left) < L /\ Lenth(lset[i].right) = L
                 THEN lm
                 ELSE rm,
           probing' = [probing EXCEPT ![i] =  probing[i] \cup newprob],
           receivedMsgs' = receivedMsgs \cup Probe(i, lset[i], failed[i], newprob),
           UNCHANGED <<lset, rtable, failed, lease, grant, status>>
          PROVE TypeInvariant'
         <4>1. lm \in SUBSET I
            BY <3>1, LeftMostType DEF TypeInvariant
         <4>2. rm \in SUBSET I
            BY <3>1, RightMostType DEF TypeInvariant
         <4>3. newprob \in SUBSET I
            BY <3>1, <4>1, <4>2 DEF TypeInvariant
         <4>5. probing' \in [I -> SUBSET I]
            BY  <4>3, probing' = [probing EXCEPT ![i] =  probing[i] \cup newprob] 
            DEF TypeInvariant
         <4>6. receivedMsgs' \in SUBSET DMsg 
            BY <3>1, <4>3, ProbeType DEF TypeInvariant
         <4>8. /\ lease' \in [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
               /\ rtable' \in [I -> RTable]
               /\ lset' \in [I -> LSet]/\ \A k \in I: lset'[k].node = k
               /\ failed'\in [I -> SUBSET I]
               /\ status'\in [I -> {"ready", "ok", "wait", "dead"}]
            BY <3>1 DEF TypeInvariant
         <4>9. QED BY <4>5,<4>6,<4>8 DEF TypeInvariant
      <3>9.QED BY <2>17, <3>1 DEF LSRepair 
   <2>18. ASSUME NEW i \in I, 
                 Recover(i)
         PROVE  TypeInvariant'
      <3>1. ASSUME status[i] # "dead",
                   probing[i] = {},
                   Lenth(lset[i].left) = 0  \/ Lenth(lset[i].right) = 0, 
                   ~\E n \in I:  status[n] \in {"ready", "ok"},
                   ~(Lenth(lset[i].left) = 0  /\ Lenth(lset[i].right) = 0), 
                   NEW pe,
                   pe = IF Lenth(lset[i].left) = 0 
                        THEN RightMost(lset[i])
                        ELSE LeftMost(lset[i]),
                   probing' = [probing EXCEPT ![i] =  probing[i] \cup {pe}],
                   receivedMsgs' = receivedMsgs \cup Probe(i, lset[i], failed[i], {pe}),
                   UNCHANGED <<lset, rtable, failed, lease, status, grant>>
         PROVE TypeInvariant' 
         <4>1. /\ lset' \in [I -> LSet]/\ \A k \in I: lset'[k].node = k
               /\ rtable' \in [I -> RTable]

               /\status' \in [I -> {"ready", "ok", "wait", "dead"}]
               /\lease' \in [I -> SUBSET I]
               /\ grant' \in  [I -> SUBSET I]
               /\failed' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>2. lset[i] \in LSet /\ failed[i] \in SUBSET I
            BY DEF TypeInvariant
         <4>3. pe \in I
            BY <3>1, RightMostType, LeftMostType, <4>2
         <4>4. probing'  \in [I -> SUBSET I]
            BY <3>1, <4>3 DEF TypeInvariant
         <4>7. Probe(i, lset[i], failed[i], {pe}) \in SUBSET DMsg
            BY <3>1, <4>3, ProbeType, <4>2
         <4>8. receivedMsgs' \in SUBSET DMsg
            BY <3>1, <4>7 DEF TypeInvariant 
         <4>9. QED BY <4>1,<4>4, <4>8 DEF TypeInvariant
      <3>9. QED BY <2>18, <3>1 DEF Recover
   <2>19. ASSUME NEW i \in I, 
                 ResignNode(i)
         PROVE  TypeInvariant' 
      <3>1. ASSUME NEW n \in I,
            rtable'= [rtable EXCEPT ![i] = AddToTable({i}, InitRTable, i)],
            lset'= [lset EXCEPT ![i] = EmptyLS(i)],
            probing' = [probing EXCEPT ![i] =  {}],
            lease' = [lease EXCEPT ![i] = {}],
            grant' =  [grant EXCEPT ![i] =  {}],
            failed' = [failed EXCEPT ![i] = {}],
            receivedMsgs' = receivedMsgs \cup 
                      {[destination |-> n, 
                        mreq |-> [
                            type |-> "JoinRequest", 
                           rtable |-> InitRTable, 
                           node |-> i]
                       ]},
            UNCHANGED status
         PROVE TypeInvariant'
         <4>1. receivedMsgs' \in SUBSET DMsg
            <5>1. [type |-> "JoinRequest", 
                           rtable |-> InitRTable, 
                           node |-> i] \in JReq
               BY <2>19, <3>1, InitRTableType DEF JReq, TypeInvariant
            <5>2. [type |-> "JoinRequest", 
                           rtable |-> InitRTable, 
                           node |-> i] \in MReq
               BY <5>1 DEF MReq
            <5>3. [destination |-> n, 
                        mreq |-> [
                            type |-> "JoinRequest", 
                           rtable |-> InitRTable, 
                           node |-> i]
                       ] \in DMsg
               BY <2>19, <3>1, <5>2 DEF DMsg 
            <5>9. QED BY <3>1, <5>3 DEF TypeInvariant
         <4>2. /\status' \in [I -> {"ready", "ok", "wait", "dead"}]
               /\lease' \in  [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
               /\probing'  \in [I -> SUBSET I]
               /\failed' \in [I -> SUBSET I]
            BY <3>1 DEF TypeInvariant
         <4>4. rtable' \in [I -> RTable]
            BY <3>1, AddToTableType, InitRTableType DEF TypeInvariant
         <4>5. lset' \in [I -> LSet]
            BY <3>1, EmptyLST DEF TypeInvariant
         <4>8. \A k \in I: lset'[k].node = k
            BY <3>1, EmptyLST DEF TypeInvariant
         <4>9. QED BY <4>1,<4>2,<4>4,<4>5, <4>8 DEF TypeInvariant
      <3>9. QED BY <2>19, <3>1 DEF ResignNode
   <2>20. ASSUME NEW i \in I,
                 NEW j \in I,
                 Lookup(i, j)
          PROVE TypeInvariant'
      <3>1.SUFFICES ASSUME 
          receivedMsgs'= receivedMsgs \cup 
                    {[destination |-> i, 
                      mreq |-> [
                                type |-> "Lookup", 
                                node |-> j]
                     ]}, 
          UNCHANGED <<status, rtable, lset, probing, failed, lease, grant>>
          PROVE TypeInvariant'
         BY <2>20 DEF Lookup
      <3>7. [destination |-> i, 
                      mreq |-> [
                                type |-> "Lookup", 
                                node |-> j]
                     ] \in DMsg
         BY <2>20, <3>1 DEF Look, TypeInvariant, MReq, DMsg
      <3>9. QED BY <3>1, <3>7 DEF Lookup, TypeInvariant
(*   <2>21. ASSUME NEW i \in I, 
                 Restart(i)
         PROVE  TypeInvariant' 
      <3>1. ASSUME 
            status' = [status EXCEPT ![i] = "ready"],
            rtable'= [rtable EXCEPT ![i] = AddToTable({i}, InitRTable, i)],
            lset'= [lset EXCEPT ![i] = EmptyLS(i)],
            probing' = [probing EXCEPT ![i] =  {}],
            lease' = [lease EXCEPT ![i] = {}],
            grant' = [grant EXCEPT ![i] = {}],
            failed' = [failed EXCEPT ![i] = {}],
            UNCHANGED <<receivedMsgs>>  
         PROVE TypeInvariant'
         <4>1. status' \in [I -> {"ready", "ok", "wait", "dead"}]
            BY <3>1 DEF TypeInvariant
         <4>2. /\lease' \in  [I -> SUBSET I]
               /\ grant' \in [I -> SUBSET I]
               /\probing'  \in [I -> SUBSET I]
               /\failed' \in [I -> SUBSET I]
               /\ receivedMsgs' \in SUBSET DMsg
            BY <3>1 DEF TypeInvariant
         <4>4. rtable' \in [I -> RTable]
            BY <3>1, AddToTableType, InitRTableType DEF TypeInvariant
         <4>5. lset' \in [I -> LSet]
            BY <3>1, EmptyLST DEF TypeInvariant
         <4>8. \A k \in I: lset'[k].node = k
            BY <3>1, EmptyLST DEF TypeInvariant
         <4>9. QED BY <4>1,<4>2,<4>4,<4>5, <4>8 DEF TypeInvariant
      <3>9. QED BY <2>21, <3>1 DEF Restart
      *)
   <2>90. CASE UNCHANGED vars
      BY <2>90 DEF TypeInvariant, vars
   <2>99. QED
     BY <2>2, <2>22, <2>3, <2>4, <2>5, <2>6,<2>7,<2>8,<2>9,<2>10,
               <2>11,<2>12,<2>121, <2>13,<2>14,<2>15,
               <2>16,<2>17,<2>18,<2>19,<2>20,(*<2>21,*)<2>90 DEF Next 
THEOREM TypeInvariance == Spec => []TypeInvariant
\*<1>1. Init => TypeInvariant
\*   BY InitTypeCorrect
\*<1>n. Init => TypeInvariant
\*   BY NextTypeCorrect
\*<1>q. QED
\*  BY <1>i, <1>n, Inv1 DEF Spec





====
\* Generated at Thu Jul 29 17:36:30 CEST 2010
