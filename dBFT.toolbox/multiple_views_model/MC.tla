---- MODULE MC ----
EXTENDS dBFT, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
const_1674204425530206000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:1RMFault
const_1674204425530207000 == 
{}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1674204425530208000 ==
MaxViewConstraint
----
=============================================================================
\* Modification History
\* Created Fri Jan 20 11:47:05 MSK 2023 by anna
