-------------------------------- MODULE dBFT --------------------------------

EXTENDS
  \* Integers defines .. and \div operators.
  Integers,
  
  \* FinitSets defines Cardinality operator.
  FiniteSets
  
CONSTANTS
  \* The set of consensus nodes with their indexes. Each element is a record
  \* of the following form:
  \* [
  \*   name  |-> "rm1"
  \*   index |-> 1
  \* ]
  RM

VARIABLES
  \* rmState is a set of consensus node states, i.e. rmState[r] is the state
  \* of consensus node r.
  rmState,
  
 \* The set of messages sent to the network. Each message has the form of
 \* element of Messages.
  msgs 

\* N is the number of validators.
N == Cardinality(RM)

\* F is the number of validators that are allowed to be malicious.
F == (N - 1) \div 3

\* M is the number of validators that must function correctly.
M == N - F

\* RMStates is a set of records where each record holds the node state and
\* the node current view.
RMStates == [type: {"initialized", "prepareRequestSent", "prepareResponseSent", "commitSent", "blockAccepted"}, view : Nat \ {0}]

\* Messages is a set of records where each record holds the message type,
\* the message sender and sender's view by the moment when message was sent.
Messages == [type : {"PrepareRequest", "PrepareResponse", "Commit"}, rm : RM, view : Nat \ {0}]

\* The type-correctness invariant.
TypeOK ==
  /\ rmState \in [RM -> RMStates]
  /\ msgs \subseteq Messages

\* IsPrimary is an operator defining whether provided node r is primary
\* for the current round from the r's point of view. It is a mapping
\* from RM to the set of {TRUE, FALSE}.
IsPrimary(r) == rmState[r].view % N = r.index

\* GetPrimary is an operator difining mapping from round index to RM.
GetPrimary(view) == CHOOSE r \in RM : view % N = r.index

\* The initial predicate.
Init ==
  /\ rmState = [r \in RM |-> [type |-> "initialized", view |-> 1]]
  /\ msgs = {}
  
\* Primary node r broadcasts PrepareRequest.
RMSendPrepareRequest(r) ==
  /\ rmState[r].type = "initialized"
  /\ IsPrimary(r)
  /\ rmState' = [rmState EXCEPT ![r].type = "prepareRequestSent"]
  /\ msgs' = msgs \cup {[type |-> "PrepareRequest", rm |-> r, view |-> rmState[r].view]}
  /\ UNCHANGED <<>>
  
\* Node r (either primary or non-primary) receives PrepareRequest from the primary node
\* of the current round (view) and broadcasts PrepareResponse. This step assumes that
\* PrepareRequest always contains valid transactions and signatures.
RMSendPrepareResponse(r) ==
  /\
     \/ rmState[r].type = "initialized"
     \/ rmState[r].type = "prepareRequestSent"
  /\ [type |-> "PrepareRequest", rm |-> GetPrimary(rmState[r].view), view |-> rmState[r].view] \in msgs
  /\ rmState' = [rmState EXCEPT ![r].type = "prepareResponseSent"]
  /\ msgs' = msgs \cup {[type |-> "PrepareResponse", rm |-> r, view |-> rmState[r].view]}
  /\ UNCHANGED <<>>

\* Node r sends Commit if there's enough PrepareResponse messages.
RMSendCommit(r) ==
  /\ rmState[r].type = "prepareResponseSent"
  /\ Cardinality({msg \in msgs : (msg.type = "PrepareResponse" /\ msg.view = rmState[r].view)}) >= M
  /\ rmState' = [rmState EXCEPT ![r].type = "commitSent"]
  /\ msgs' = msgs \cup {[type |-> "Commit", rm |-> r, view |-> rmState[r].view]}
  /\ UNCHANGED <<>>
  
\* Node r collects enough Commit messages and accepts block.
RMAcceptBlock(r) ==
  /\ rmState[r].type = "commitSent"
  /\ Cardinality({msg \in msgs : (msg.type = "Commit" /\ msg.view = rmState[r].view)}) >= M
  /\ rmState' = [rmState EXCEPT ![r].type = "blockAccepted"]
  /\ UNCHANGED <<msgs>>

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating ==
  /\ \A rm \in RM: rmState[rm].type = "blockAccepted"
  /\ UNCHANGED <<msgs, rmState>>

\* The next-state action.
Next ==
  \/ Terminating
  \/ \E r \in RM : 
       RMSendPrepareRequest(r) \/ RMSendPrepareResponse(r) \/ RMSendCommit(r)
         \/ RMAcceptBlock(r)

\* A state predicate asserting that two RMs have not arrived at conflicting
\* decisions.  It is an invariant of the specification.
Consistent == \* TODO: need some more care.
  \/ TRUE
  \/ \A r1, r2 \in RM : ~ /\ rmState[r1].type = "blockAccepted"
                          /\ rmState[r2].type = "changeViewRequested"

\* The complete specification of the protocol written as a temporal  formula.  
Spec == Init /\ [][Next]_<<rmState, msgs>>

\* This theorem asserts the truth of the temporal formula whose meaning is that
\* the state predicate TypeOK /\ Consistent is an invariant of the
\* specification Spec.  Invariance of this conjunction is equivalent to
\* invariance of both of the formulas TypeOK and Consistent.     
THEOREM Spec => [](TypeOK /\ Consistent)

=============================================================================
\* Modification History
\* Last modified Mon Dec 19 18:53:30 MSK 2022 by anna
\* Created Thu Dec 15 16:06:17 MSK 2022 by anna
