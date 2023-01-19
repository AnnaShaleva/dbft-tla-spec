---- MODULE MC ----
EXTENDS dBFTExtended, TLC

\* CONSTANT definitions @modelParameterConstants:0RMFault
const_167411521009074000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_167411521009075000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2MaxView
const_167411521009076000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3MaxUndeliveredMessages
const_167411521009077000 == 
6
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_167411521009078000 ==
ModelConstraint
----
=============================================================================
\* Modification History
\* Created Thu Jan 19 11:00:10 MSK 2023 by anna
