---- MODULE MC ----
EXTENDS dBFT, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxView
const_167203871990782000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1RM
const_167203871990783000 == 
{[name |-> "rm1", index |-> 1], [name |-> "rm2", index |-> 2], [name |-> "rm3", index |-> 3], [name |-> "rm4", index |-> 4]}
----

\* CONSTANT definitions @modelParameterConstants:2RMFault
const_167203871990784000 == 
{}
----

\* Constant expression definition @modelExpressionEval
const_expr_167203871990785000 == 
Cardinality(RM)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_167203871990785000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_167203871990786000 ==
FALSE/\msgs = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_167203871990787000 ==
FALSE/\msgs' = msgs
----
=============================================================================
\* Modification History
\* Created Mon Dec 26 10:11:59 MSK 2022 by anna
