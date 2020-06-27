---- MODULE MC ----
EXTENDS MultiPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
V1, V2, V3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
S1, S2, S3
----

\* MV CONSTANT definitions Value
const_15932424583477000 == 
{V1, V2, V3}
----

\* MV CONSTANT definitions Acceptors
const_15932424583478000 == 
{S1, S2, S3}
----

\* SYMMETRY definition
symm_15932424583479000 == 
Permutations(const_15932424583478000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_159324245834710000 ==
0..10
----
=============================================================================
\* Modification History
\* Created Sat Jun 27 15:20:58 CST 2020 by 15150
