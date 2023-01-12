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
  RM,
  RMFault,
  
  \* MaxView is the maximum view number from (from 1 to N)
  MaxView

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

ASSUME
  /\ N >= 4
  /\ RMFault \subseteq RM
  /\ Cardinality(RMFault) <= F
  
  
Views == 1..MaxView

ViewOK(view) == view \in Views

\* RMStates is a set of records where each record holds the node state and
\* the node current view.
RMStates == [
              type: {"initialized", "prepareSent", "commitSent", "blockAccepted"},
              view : Views
            ]

\* Messages is a set of records where each record holds the message type,
\* the message sender and sender's view by the moment when message was sent.
Messages == [type : {"PrepareRequest", "PrepareResponse", "Commit", "ChangeView"}, rm : RM, view : Views]

\* The type-correctness invariant.
TypeOK ==
  /\ rmState \in [RM -> RMStates]
  /\ msgs \subseteq Messages
  /\ \A r \in RM : ViewOK(rmState[r].view)
  /\ \A msg \in msgs : ViewOK(msg.view)
  

\* IsPrimary is an operator defining whether provided node r is primary
\* for the current round from the r's point of view. It is a mapping
\* from RM to the set of {TRUE, FALSE}.
IsPrimary(r) == (rmState[r].view % N) + 1 = r.index

\* GetPrimary is an operator difining mapping from round index to RM.
GetPrimary(view) == CHOOSE r \in RM : (view % N) + 1 = r.index

\* GetNewView returns new view number based on the previous node view value.
GetNewView(oldView) == oldView + 1

\* IsViewChanging denotes whether node r have sent ChangeView message for the
\* current round.
IsViewChanging(r) == \E msg \in [type : {"ChangeView"}, rm : {r}, view : {v \in Views : v >= rmState[r].view}] : msg \in msgs

CountCommitted(r) == Cardinality({rm \in RM : Cardinality({msg \in msgs : msg.rm = rm /\ msg.type = "Commit"}) /= 0})  \* TODO: in dbft.go we take into account commits from (potentially) ANY view (not only from the current's node view).
CountFailed(r) == Cardinality({rm \in RM : Cardinality({msg \in msgs : msg.rm = rm /\ msg.view < rmState[r].view}) /= 0 })
MoreThanFNodesCommittedOrLost(r) == CountCommitted(r) + CountFailed(r) > F
NotAcceptingPayloadsDueToViewChanging(r) ==
  /\ IsViewChanging(r)
  /\ \neg MoreThanFNodesCommittedOrLost(r)

\* PrepareRequestSentOrReceived denotes whether there's a PrepareRequest
\* message received from the current round's speaker (as the node r sees it).
PrepareRequestSentOrReceived(r) == [type |-> "PrepareRequest", rm |-> GetPrimary(rmState[r].view), view |-> rmState[r].view] \in msgs

\* The initial predicate.
Init ==
  /\ rmState = [r \in RM |-> [type |-> "initialized", view |-> 1]]
  /\ msgs = {}
  
\* Primary node r broadcasts PrepareRequest.
RMSendPrepareRequest(r) ==
  /\ rmState[r].type = "initialized"
  /\ IsPrimary(r)
  /\ rmState' = [rmState EXCEPT ![r].type = "prepareSent"]
  /\ msgs' = msgs \cup {[type |-> "PrepareRequest", rm |-> r, view |-> rmState[r].view]}
  /\ UNCHANGED <<>>
  
\* Non-primary node r receives PrepareRequest from the primary node
\* of the current round (view) and broadcasts PrepareResponse.
\* This step assumes that PrepareRequest always contains valid transactions and signatures.
RMSendPrepareResponse(r) ==
  /\ rmState[r].type = "initialized" \* dbft.go -L151-L155
  /\ \neg IsPrimary(r)
  /\ PrepareRequestSentOrReceived(r)
  /\ rmState' = [rmState EXCEPT ![r].type = "prepareSent"]
  /\ msgs' = msgs \cup {[type |-> "PrepareResponse", rm |-> r, view |-> rmState[r].view]}
  /\ UNCHANGED <<>>

\* Node r sends Commit if there's enough PrepareResponse messages.
RMSendCommit(r) ==
  /\ rmState[r].type = "prepareSent"
  /\
     \/ IsPrimary(r) \* dbft.go -L196 (if primary, on timeout, then commit may be sent immediately after PrepareRequest)
     \/ \neg NotAcceptingPayloadsDueToViewChanging(r) \* dbft.go -L 151, -L300 // TODO: diff in code with C# node
  /\ Cardinality({msg \in msgs : ((msg.type = "PrepareResponse" \/ msg.type = "PrepareRequest") /\ msg.view = rmState[r].view)}) >= M
  /\ PrepareRequestSentOrReceived(r)
  /\ rmState' = [rmState EXCEPT ![r].type = "commitSent"]
  /\ msgs' = msgs \cup {[type |-> "Commit", rm |-> r, view |-> rmState[r].view]}
  /\ UNCHANGED <<>>

\* Node r collects enough Commit messages and accepts block.
RMAcceptBlock(r) ==
  /\ rmState[r].type = "commitSent"
  /\ Cardinality({msg \in msgs : (msg.type = "Commit" /\ msg.view = rmState[r].view)}) >= M
  /\ rmState' = [rmState EXCEPT ![r].type = "blockAccepted"]
  /\ UNCHANGED <<msgs>>

RMSendChangeView(r) ==
  /\
     \/ rmState[r].type = "initialized" \* if there's no PrepareRequest for a long time.
     \/ rmState[r].type = "prepareSent" \* if there's a PrepareRequest from leader and r have sent PrepareResponse, but there's not enough of them.
     \/ r \in RMFault
  /\ msgs' = msgs \cup {[type |-> "ChangeView", rm |-> r, view |-> rmState[r].view]}
  /\ UNCHANGED <<rmState>>

RMReceiveChangeView(r) ==
  /\ rmState[r].type /= "commitSent" \* dbft.go -L470
  /\ rmState[r].type /= "blockAccepted"
  /\ Cardinality({msg \in msgs : (msg.type = "ChangeView" /\ GetNewView(msg.view) >= GetNewView(rmState[r].view))}) >= M
  /\
     LET newView == GetNewView(rmState[r].view)
     IN
        /\ newView <= MaxView \* TODO: get rid of MaxView and set the model constraint.
        /\ rmState' = [rmState EXCEPT ![r].type = "initialized", ![r].view = newView]
  /\ UNCHANGED <<msgs>>

\* Allow infinite stuttering to prevent deadlock on termination. We consider
\* termination to be valid if M nodes have the block being accepted.
Terminating ==
  /\ Cardinality({rm \in RM : rmState[rm].type = "blockAccepted"}) >= M
  /\ UNCHANGED <<msgs, rmState>>

\* The next-state action.
Next ==
  \/ Terminating
  \/ \E r \in RM : 
       RMSendPrepareRequest(r) \/ RMSendPrepareResponse(r) \/ RMSendCommit(r)
         \/ RMAcceptBlock(r) \/ RMSendChangeView(r) \/ RMReceiveChangeView(r)

\* Invariat for 4 nodes setup.
Inv ==
  \/ Cardinality({r \in RM : rmState[r].type = "blockAccepted"}) /= 2
  \/ Cardinality({r \in RM : (rmState[r].type /= "blockAccepted" /\ rmState[r].type /= "commitSent" /\ IsViewChanging(r))}) /= 2

\* Invariant for ChangeView-absent setup.
Inv1 == \A r \in RM : IsViewChanging(r) = FALSE

\* A state predicate asserting that two RMs have not arrived at conflicting
\* decisions.  It is an invariant of the specification.
Consistent == \* TODO: need some more care.
  \/ TRUE
  \*\/ \A r1, r2 \in RM : ~ /\ rmState[r1].type = "blockAccepted"
  \*                        /\ rmState[r2].type = "changeViewRequested"

\* The complete specification of the protocol written as a temporal  formula.  
Spec == Init /\ [][Next]_<<rmState, msgs>>

\* This theorem asserts the truth of the temporal formula whose meaning is that
\* the state predicate TypeOK /\ Consistent is an invariant of the
\* specification Spec.  Invariance of this conjunction is equivalent to
\* invariance of both of the formulas TypeOK and Consistent.     
THEOREM Spec => [](TypeOK /\ Consistent)

=============================================================================
\* Modification History
\* Last modified Thu Dec 22 17:30:41 MSK 2022 by anna
\* Created Thu Dec 15 16:06:17 MSK 2022 by anna
