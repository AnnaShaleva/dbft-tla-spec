---- MODULE MC ----
EXTENDS dBFTExtended, TLC

\* CONSTANT definitions @modelParameterConstants:0RMFault
const_167401918460510000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_167401918460511000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2MaxView
const_167401918460512000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3MaxUndeliveredMessages
const_167401918460513000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_167401918460514000 ==
ModelConstraint
----
=============================================================================
\* Modification History
\* Created Wed Jan 18 08:19:44 MSK 2023 by anna
