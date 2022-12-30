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
  RMFault

VARIABLES
  \* rmState is a set of consensus node states, i.e. rmState[r] is the state
  \* of consensus node r.
  rmState,
  
 \* The set of messages sent to the network. Each message has the form of
 \* element of Messages.
  msgs

\* A tuple of all variables used for simplisity of fairness conditions.
vars == << rmState, msgs >>

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

\* RMStates is a set of records where each record holds the node state and
\* the node current view.
RMStates == [
              type: {"initialized", "prepareSent", "commitSent", "blockAccepted"},
              view : Nat
            ]

\* Messages is a set of records where each record holds the message type,
\* the message sender and sender's view by the moment when message was sent.
Messages == [type : {"PrepareRequest", "PrepareResponse", "Commit", "ChangeView"}, rm : RM, view : Nat]

\* The type-correctness invariant.
TypeOK ==
  /\ rmState \in [RM -> RMStates]
  /\ msgs \subseteq Messages
  

\* IsPrimary is an operator defining whether provided node r is primary
\* for the current round from the r's point of view. It is a mapping
\* from RM to the set of {TRUE, FALSE}.
IsPrimary(r) == (rmState[r].view % N) + 1 = r.index

\* GetPrimary is an operator difining mapping from round index to RM.
GetPrimary(view) == CHOOSE r \in RM : (view % N) + 1 = r.index

IsFault(r) == r \in RMFault

\* GetNewView returns new view number based on the previous node view value.
GetNewView(oldView) == oldView + 1

\* IsViewChanging denotes whether node r have sent ChangeView message for the
\* current round.
IsViewChanging(r) == Cardinality({msg \in msgs : msg.type = "ChangeView" /\ msg.rm = r /\ msg.view >= rmState[r].view}) /= 0

\* IsBlockAccepted returns whether at least one node has the block being accepted.
IsBlockAccepted == Cardinality({r \in RM : rmState[r].type = "blockAccepted"}) > 0

CountCommitted(r) == Cardinality({rm \in RM : Cardinality({msg \in msgs : msg.rm = rm /\ msg.type = "Commit"}) /= 0})  \* TODO: in dbft.go we take into account commits from (potentially) ANY view (not only from the current's node view).
CountFailed(r) == Cardinality({rm \in RM : Cardinality({msg \in msgs : msg.rm = rm /\ msg.view < rmState[r].view}) /= 0 })
MoreThanFNodesCommittedOrLost(r) == CountCommitted(r) + CountFailed(r) > F
NotAcceptingPayloadsDueToViewChanging(r) ==
  /\ IsViewChanging(r)
  /\ \neg MoreThanFNodesCommittedOrLost(r)

\* PrepareRequestSentOrReceived denotes whether there's a PrepareRequest
\* message received from the current round's speaker (as the node r sees it).
PrepareRequestSentOrReceived(r) == [type |-> "PrepareRequest", rm |-> GetPrimary(rmState[r].view), view |-> rmState[r].view] \in msgs

\* -------------- Safety temporal formula --------------

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
  \* /\ \neg NotAcceptingPayloadsDueToViewChanging(r) \* dbft.go -L300, in C# node, but not in ours
  /\ PrepareRequestSentOrReceived(r)
  /\ rmState' = [rmState EXCEPT ![r].type = "prepareSent"]
  /\ msgs' = msgs \cup {[type |-> "PrepareResponse", rm |-> r, view |-> rmState[r].view]}
  /\ UNCHANGED <<>>

\* Node r sends Commit if there's enough PrepareResponse messages.
RMSendCommit(r) ==
  /\ rmState[r].type = "prepareSent"
  /\ \neg NotAcceptingPayloadsDueToViewChanging(r)
     \* (IsPrimary(r) \/) -- INVALID; dbft.go -L196 (if primary, on timeout, then commit may be sent immediately after PrepareRequest)
     \* dbft.go -L 151, -L300 // TODO: diff in code with C# node    
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

\* RMFetchBlock sets the node state to "blockAccepted" in case if there's at least one node
\* that has the block being accepted.
RMFetchBlock(r) ==
  /\ rmState[r].type /= "blockAccepted"
  /\ IsBlockAccepted
  /\ rmState' = [rmState EXCEPT ![r].type = "blockAccepted"]
  /\ UNCHANGED <<msgs>>

RMSendChangeView(r) ==
  \* if there's no PrepareRequest for a long time.
  \* if there's a PrepareRequest from leader and r have sent PrepareResponse, but there's not enough of them.
  /\ (rmState[r].type = "initialized" \/ rmState[r].type = "prepareSent" \/ IsFault(r))
  /\ msgs' = msgs \cup {[type |-> "ChangeView", rm |-> r, view |-> rmState[r].view]}
  /\ UNCHANGED <<rmState>>

RMReceiveChangeView(r) ==
  /\ (IsFault(r) \/ (rmState[r].type /= "commitSent" /\ rmState[r].type /= "blockAccepted" /\ Cardinality({msg \in msgs : (msg.type = "ChangeView" /\ GetNewView(msg.view) >= GetNewView(rmState[r].view))}) >= M))\* dbft.go -L470 
  /\ rmState' = [rmState EXCEPT ![r].type = "initialized", ![r].view = GetNewView(rmState[r].view)]
  /\ UNCHANGED <<msgs>>

\* Allow infinite stuttering to prevent deadlock on termination. We consider
\* termination to be valid if at least one node has the block being accepted.
Terminating ==
  /\ Cardinality({rm \in RM : rmState[rm].type = "blockAccepted"}) >=1
  /\ UNCHANGED <<msgs, rmState>>

\* The next-state action.
Next ==
  \/ Terminating
  \/ \E r \in RM : 
       RMSendPrepareRequest(r) \/ RMSendPrepareResponse(r) \/ RMSendCommit(r)
         \/ RMAcceptBlock(r) \/ RMFetchBlock(r) \/ RMSendChangeView(r) \/ RMReceiveChangeView(r)

\* A safety temporal formula specifies only what the system MAY do (i.e. the set of possible
\* allowed behaviours for the system). It asserts only what may happen; any behaviour
\* that violates it does so at some point and nothing past that point makes difference.
\*
\* E.g. this safety formula (applied standalone) allows the behaviour to end with an
\* infinite set of stuttering steps (those steps that DO NOT change neither msgs nor rmState)
\* and never reach the state where at least one node is committed or accepted the
\* block.
\*
\* To forbid such behaviours we must specify what the system MUST
\* do. It will be specified below with the help of liveness and fairness
\* conditions in the Liveness formula.
Safety == Init /\ [][Next]_<<msgs, rmState>>

\* -------------- Liveness temporal formula --------------

\* For every possible behaviour it's true that there's at least one PrepareRequest message from the speaker.
PrepareResponseSentRequirement == <>(\E msg \in msgs : msg.type = "PrepareResponse")

\* For every possible behaviour it's true that eventually (i.e. at least once through the behaviour)
\* block will be accepted. It is something that dBFT must guarantee (an in practice this
\* condition is violated).
TerminationRequirement == <>(\E r \in RM : rmState[r].type = "blockAccepted")

\* For every possible behaviour if there's a non-fault node that have sent the commit message,
\* then there's a node that has the block being accepted at this step or at any subsequent step.
DeadlockFreeRequirement == (\E r \in RM \ RMFault : rmState[r].type = "commitSent") ~> (\E r \in RM : rmState[r].type = "blockAccepted")

\* For every possible behaviour it's true that for any non-fault node that has sent the commit message
\* the block will be accepted by this node in this step or in one of the subsequent steps of the behaviour.
BlockAcceptanceRequirement == \A r \in RM \ RMFault : (rmState[r].type = "commitSent") ~> (rmState[r].type = "blockAccepted")

\* A liveness temporal formula asserts only what must happen (i.e. specifies what
\* the system MUST do). Any behaviour can NOT violate it at ANY point; there's always
\* the rest of the behaviour that can always make the liveness formula true; if there's
\* no such behaviour than the liveness formula is violated. The liveness formula is supposed
\* to be checked as a property by TLC model checker.
Liveness == PrepareResponseSentRequirement /\ TerminationRequirement /\ BlockAcceptanceRequirement \* /\ DeadlockFreeRequirement

\* -------------- Fairness temporal formula --------------

\* If continiously at least one of the node is able to send PrepareResponse, then
\* it must send it eventually.
SendPrepareRequestFairness == WF_vars(\E r \in RM : RMSendPrepareRequest(r))

\* This requirement requires PrepareResponse message to be sent once PrepareRequest
\* message is received by the node, but allows stop sending PrepareRequests as far (and
\* disable RMSendPrepareResponse enabling condition). 
SendPrepareResponseFairness == WF_vars(\E r \in RM : RMSendPrepareResponse(r))

\* If repeatedly at least one of the node is able to send the commit message, then it
\* must send it. Even if the node is able to send the ChangeView message after PrepareResponse,
\* then the node is still must be able to send the Commit in the next view.
SendCommitFairness == SF_vars(\E r \in RM : RMSendCommit(r))

\* This requirement requires each proper subset of the Commit messages to be accepted
\* once the set is completed. This results into block submission. At the same time,
\* SF allows to stop sending Commit messages.
SubmitBlockFairness == SF_vars(\E r \in RM : RMAcceptBlock(r))

\* If continiously at least one node has accepted the block, then the node r must fetch
\* it eventually.
FetchBlockFairness == WF_vars(\E r \in RM : RMFetchBlock(r))

\* This requirement is needed to avoid situations when one node is committed in the
\* previous view, and three another nodes have changed their view so that the next
\* speaker is the committed node. It's a deadlock, and this situation requires
\* the rest of three nodes to change their view.
SendChangeViewFairness == WF_vars(\E r \in RM : RMSendChangeView(r))

\* If ChangeView message has ever been repeatedly received by any of the node, then it must
\* be properly handled.
ReceiveChangeViewFairness == SF_vars(\E r \in RM : RMReceiveChangeView(r))

\* Fairness is a temporal assumptions under which the model is working.
Fairness == SendCommitFairness /\ SubmitBlockFairness /\ SendPrepareResponseFairness  /\ SendPrepareRequestFairness
            /\ ReceiveChangeViewFairness /\ SendChangeViewFairness /\ FetchBlockFairness

\* -------------- Specification --------------

\* The complete specification of the protocol written as a temporal formula.  
Spec == Safety /\ Fairness

\* -------------- ModelConstraints --------------

MaxViewConstraint == \A r \in RM : rmState[r].view <= 3

\* -------------- Invariants of the specification --------------

\* This theorem asserts the truth of the temporal formula whose meaning is that
\* the state predicate TypeOK is an invariant of the specification Spec.
THEOREM Spec => []TypeOK

=============================================================================
\* Modification History
\* Last modified Mon Jan 09 14:44:50 MSK 2023 by anna
\* Created Thu Dec 15 16:06:17 MSK 2022 by anna
