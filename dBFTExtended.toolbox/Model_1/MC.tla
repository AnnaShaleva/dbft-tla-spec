---- MODULE MC ----
EXTENDS dBFTExtended, TLC

\* CONSTANT definitions @modelParameterConstants:0RMFault
const_167352448261488000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_167352448261489000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2MaxView
const_167352448261490000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_167352448261491000 ==
MaxViewConstraint
----
=============================================================================
\* Modification History
\* Created Thu Jan 12 14:54:42 MSK 2023 by anna
