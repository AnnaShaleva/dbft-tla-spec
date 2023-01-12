---- MODULE MC ----
EXTENDS dBFT, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
const_167326471423466000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:1RMFault
const_167326471423467000 == 
{}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_167326471423468000 ==
MaxViewConstraint
----
=============================================================================
\* Modification History
\* Created Mon Jan 09 14:45:14 MSK 2023 by anna
