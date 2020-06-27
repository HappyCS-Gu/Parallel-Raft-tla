---- MODULE MC ----
EXTENDS ParallelRaftModified, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
S1, S2, S3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
V1, V2, V3
----

\* MV CONSTANT definitions Server
const_1593164362079198000 == 
{S1, S2, S3}
----

\* MV CONSTANT definitions Value
const_1593164362079199000 == 
{V1, V2, V3}
----

\* SYMMETRY definition
symm_1593164362079200000 == 
Permutations(const_1593164362079198000)
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1593164362079201000 ==
0..5
----
=============================================================================
\* Modification History
\* Created Fri Jun 26 17:39:22 CST 2020 by 15150
