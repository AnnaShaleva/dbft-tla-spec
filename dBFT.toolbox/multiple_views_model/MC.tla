---- MODULE MC ----
EXTENDS dBFT, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
const_1674203647942200000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:1RMFault
const_1674203647942201000 == 
{}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1674203647942202000 ==
MaxViewConstraint
----
=============================================================================
\* Modification History
\* Created Fri Jan 20 11:34:07 MSK 2023 by anna
