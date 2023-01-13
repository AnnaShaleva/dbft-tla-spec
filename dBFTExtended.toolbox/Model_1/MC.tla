---- MODULE MC ----
EXTENDS dBFTExtended, TLC

\* CONSTANT definitions @modelParameterConstants:0RMFault
const_1673585561918138000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_1673585561918139000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2MaxView
const_1673585561918140000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3MaxUndeliveredMessages
const_1673585561918141000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1673585561918142000 ==
ModelConstraint
----
=============================================================================
\* Modification History
\* Created Fri Jan 13 07:52:41 MSK 2023 by anna
