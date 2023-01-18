---- MODULE MC ----
EXTENDS dBFTExtended, TLC

\* CONSTANT definitions @modelParameterConstants:0RMFault
const_167403320789358000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_167403320789359000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2MaxView
const_167403320789360000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3MaxUndeliveredMessages
const_167403320789361000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_167403320789362000 ==
ModelConstraint
----
=============================================================================
\* Modification History
\* Created Wed Jan 18 12:13:27 MSK 2023 by anna
