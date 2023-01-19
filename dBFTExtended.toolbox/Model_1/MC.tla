---- MODULE MC ----
EXTENDS dBFTExtended, TLC

\* CONSTANT definitions @modelParameterConstants:0RMFault
const_1674134537222186000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_1674134537222187000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2MaxView
const_1674134537222188000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3MaxUndeliveredMessages
const_1674134537222189000 == 
6
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1674134537222190000 ==
ModelConstraint
----
=============================================================================
\* Modification History
\* Created Thu Jan 19 16:22:17 MSK 2023 by anna
