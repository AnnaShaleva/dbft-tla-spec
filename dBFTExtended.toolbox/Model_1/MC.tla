---- MODULE MC ----
EXTENDS dBFTExtended, TLC

\* CONSTANT definitions @modelParameterConstants:0RMFault
const_16738528365242000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_16738528365243000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2MaxView
const_16738528365244000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3MaxUndeliveredMessages
const_16738528365245000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_16738528365246000 ==
ModelConstraint
----
=============================================================================
\* Modification History
\* Created Mon Jan 16 10:07:16 MSK 2023 by anna
