------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES nodes, token

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ nodes \in [Nodes -> [active : BOOLEAN, color : Color]]
  /\ token \in [t : Nodes, color : Color]

Init ==
  /\ nodes \in [Nodes -> [active : BOOLEAN, color : Color]]
  /\ token = [t |-> 0, color |-> "black"]

InitiateProbe ==
  /\ token.t = 0
  /\ token.color = "black"
  /\ nodes[0].active = FALSE
  /\ token' = [t |-> N-1, color |-> "white"]
  /\ nodes' = [nodes EXCEPT ![0] = [@ EXCEPT !.color = "white"]]

PassToken(i) ==  \* rules 0, 2, 5
  /\ nodes[i].active = FALSE
  /\ token.t = i
  /\ LET newcolor == IF nodes[i].color = "black" THEN "black" ELSE token.color
     IN token' = [t |-> i-1, color |-> newcolor]
  /\ nodes' = [nodes EXCEPT ![i] = [@ EXCEPT !.color = "white"]]

SendMsg(i) ==  \* rule 1', intro par. 2
  /\ nodes[i].active = TRUE
  /\ \E j \in Nodes \ {i} :
        nodes' = [nodes EXCEPT ![i] = [@ EXCEPT !.color = "black"],
                               ![j] = [@ EXCEPT !.active = TRUE]]
  /\ token' = token

Deactivate(i) ==  \* intro, par.2 -- rule ?
  /\ nodes[i].active = TRUE
  /\ nodes' = [nodes EXCEPT ![i] = [@ EXCEPT !.active = FALSE]]
  /\ token' = token

Next ==
  \/ InitiateProbe
  \/ \E i \in Nodes \ {0} : PassToken(i)
  \/ \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

vars == <<nodes, token>>

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

(***************************************************************************)
(* Non-invariants for validating the specification.                        *)
(***************************************************************************)
NeverBlack == \A i \in Nodes : nodes[i].color # "black"

NeverChangeColor == [][\A i \in Nodes : UNCHANGED <<nodes[i].color>>]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 then every    *)
(* node is inactive.                                                       *)
(***************************************************************************)
TerminationDetection ==
  token.t = 0 /\ token.color = "white" => \A i \in Nodes : nodes[i].active = FALSE

TerminationDetection2 ==
  ~ ENABLED <<Next>>_vars => \A i \in Nodes : nodes[i].active = FALSE

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  (\A i \in Nodes : nodes[i].active = FALSE) ~> (token.t = 0 /\ token.color = "white")

(***************************************************************************)
(* Dijkstra's invariants.                                                  *)
(***************************************************************************)
P0 == 
  \/ /\ \A i \in Nodes : token.t < i /\ i < N => nodes[i].active = FALSE
     /\ token.t = 0 /\ token.color = "white" => nodes[0].active = FALSE
  \/ /\ \E j \in 0 .. token.t : nodes[j].color = "black"
     /\ token.t = 0 /\ token.color = "white" => nodes[0].color = "white"
  \/ token.color = "black"

-----------------------------------------------------------------------------

LEMMA P0_implies_Termination == P0 => TerminationDetection
<1>1. SUFFICES ASSUME token.t = 0, token.color = "white", P0
               PROVE  \A i \in Nodes : nodes[i].active = FALSE
  BY <1>1 DEF TerminationDetection
<1>2. ~ P0!3  BY token.color = "white" DEF P0
<1>3. ~ P0!2  BY <1>1 DEF P0
<1>. QED
  <2>1. P0!1  BY P0, <1>2, <1>3 DEF P0
  <2>.  TAKE i \in Nodes
  <2>3. CASE i = 0  BY <2>1, <1>1, <2>3
  <2>4. CASE i \in 1 .. N-1
    <3>1. token.t < i  BY token.t=0, <2>4, NAssumption
    <3>2. i < N  BY NAssumption, <2>4
    <3>. QED  BY <3>1, <3>2, <2>1
  <2>. QED  BY <2>3, <2>4  DEF Nodes

LEMMA P0_init == Init => P0

LEMMA P0_inductive == TypeOK /\ P0 /\ [Next]_vars => P0'

=============================================================================
\* Modification History
\* Last modified Mon Sep 09 15:26:44 CEST 2013 by markus
\* Last modified Mon Sep 09 15:23:59 CEST 2013 by merz
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
