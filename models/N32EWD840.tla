---- MODULE N32EWD840 ----
EXTENDS EWD840, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_140101043427280000 == 
32
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_140101043428381000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_140101043429382000 ==
TypeOK
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_140101043430383000 ==
TerminationDetection2
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_140101043431384000 ==
P0
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_140101043432385000 ==
Liveness
----
=============================================================================
\* Modification History
\* Created Sun May 25 11:33:54 CEST 2014 by markus
