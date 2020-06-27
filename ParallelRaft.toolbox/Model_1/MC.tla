---- MODULE MC ----
EXTENDS ParallelRaft, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
V1, V2, V3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
S1, S2, S3
----

\* MV CONSTANT definitions Value
const_1593162016130124000 == 
{V1, V2, V3}
----

\* MV CONSTANT definitions Server
const_1593162016130125000 == 
{S1, S2, S3}
----

\* SYMMETRY definition
symm_1593162016130126000 == 
Permutations(const_1593162016130125000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1593162016130127000 ==
0..5
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1593162016130128000 ==
 A!Spec
----
=============================================================================
\* Modification History
\* Created Fri Jun 26 17:00:16 CST 2020 by 15150
