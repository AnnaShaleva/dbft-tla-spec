---- MODULE MC ----
EXTENDS dBFTExtended, TLC

\* CONSTANT definitions @modelParameterConstants:0RMFault
const_167395870927689000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_167395870927690000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2MaxView
const_167395870927691000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3MaxUndeliveredMessages
const_167395870927692000 == 
4
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_167395870927693000 ==
ModelConstraint
----
=============================================================================
\* Modification History
\* Created Tue Jan 17 15:31:49 MSK 2023 by anna
