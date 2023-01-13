---- MODULE MC ----
EXTENDS dBFTExtended, TLC

\* CONSTANT definitions @modelParameterConstants:0RMFault
const_1673600982751243000 == 
{}
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_1673600982751244000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2MaxView
const_1673600982751245000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3MaxUndeliveredMessages
const_1673600982751246000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1673600982751247000 ==
ModelConstraint
----
=============================================================================
\* Modification History
\* Created Fri Jan 13 12:09:42 MSK 2023 by anna
