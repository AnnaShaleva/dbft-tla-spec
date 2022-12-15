-------------------------------- MODULE dBFT --------------------------------

EXTENDS
  \* Integers defines .. operator.
  Integers,
  
  \* FinitSets defines Cardinality operator.
  FiniteSets
  
CONSTANTS
  RM \* The set of consensus nodes.

VARIABLES
  \* rmState is a set of consensus node states, i.e. rmState[r] is the state
  \* of consensus node r.
  rmState,
  
  \* primaryI is a single number representing the index of the primary node
  \* in the current round (view).
  \* TODO: replace it with rmState[r].view, as it's the property of each node,
  \* and some of them may have an old view?
  primaryI,
  
 \* The set of messages sent to the network. Each message has the form of
 \* element of Messages.
  msgs 
  
\* Messages is a set of records where each record holds the message type and
\* the sender.
Messages == [type : {"PrepareRequest", "PrepareResponse", "Commit"}, rm : RM]

\* The type-correctness invariant.
TypeOK ==
  /\ rmState \in [RM -> {"initialized", "prepareRequestSent", "prepareResponseSent", "commitSent", "blockAccepted"}]
  \*/\ {primaryI} \in {1..Cardinality(RM)}
  /\ msgs \subseteq Messages

\* IsPrimary is an operator defining whether provided node is primary for the
\* current round. It is a mapping from RM to the set of {TRUE, FALSE}.
\* TODO
IsPrimary(r) == r = "rm1"

\* GetPrimary is an operator difining mapping from round index to RM.
\* TODO
GetPrimary(round) == "rm1"

\* The initial predicate.
Init ==
  /\ rmState = [r \in RM |-> "initialized"]
  /\ primaryI = 1
  /\ msgs = {}
  
\* Primary node r broadcasts PrepareRequest.
RMSendPrepareRequest(r) ==
  /\ rmState[r] = "initialized"
  /\ IsPrimary(r)
  /\ rmState' = [rmState EXCEPT ![r] = "prepareRequestSent"]
  /\ msgs' = msgs \cup {[type |-> "PrepareRequest", rm |-> r]}
  /\ UNCHANGED <<primaryI>>
  
\* Node r (either primary or non-primary) receives PrepareRequest from the primary node
\* of the current round (view) and broadcasts PrepareResponse. This step assumes that
\* PrepareRequest always contains valid transactions and signatures.
RMSendPrepareResponse(r) ==
  /\
     \/ rmState[r] = "initialized"
     \/ rmState[r] = "prepareRequestSent" \* TODO: check PrepareRequest sent for the CURRENT view only!
  /\ [type |-> "PrepareRequest", rm |-> GetPrimary(primaryI)] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "prepareResponseSent"]
  /\ msgs' = msgs \cup {[type |-> "PrepareResponse", rm |-> r]}
  /\ UNCHANGED <<primaryI>>

\* Node r sends Commit if there's enough PrepareResponse messages.
RMSendCommit(r) ==
  /\ rmState[r] = "prepareResponseSent"
  /\ Cardinality({msg \in msgs : (msg.type = "PrepareResponse")})        \* TODO: check PrepareResponses for the CURRENT view only!
                                                                  >= 3 \* TODO: add a separate formulae for M, N and F
  /\ rmState' = [rmState EXCEPT ![r] = "commitSent"]
  /\ msgs' = msgs \cup {[type |-> "Commit", rm |-> r]}
  /\ UNCHANGED <<primaryI>>
  
\* Node r sends ChangeView if there's not enough PrepareResponse messages.
\* TODO: not finished yet, may be some other cases.
RMSendChangeView(r) ==
  /\ FALSE \* TODO: enable this condition in the next spec version.
  /\
     \/ rmState[r] = "initialized" \* if there's no PrepareRequest for a long time.
    \* \/ rmState[r] = "prepareRequestSent" \* Q2: if it's a leader, but it can't broadcast its PrepareResponse for some reason (bad network connection, etc.)
     \/
        /\ rmState[r] = "prepareResponseSent" \* there's a PrepareRequest from leader and r have sent PrepareResponse, but there's not enough of them.
        /\ Cardinality({msg \in msgs : (msg.type = "PrepareResponse")}) < 3
  /\ UNCHANGED <<primaryI>> \* TODO: properly fill unchange VARs
  
\* Node r collects enough Commit messages and accepts block.
RMAcceptBlock(r) ==
  /\ rmState[r] = "commitSent"
  /\ Cardinality({msg \in msgs : (msg.type = "Commit")})  \* TODO: check Commits for the CURRENT view only!
                                                         >= 3 \* TODO: add a separate formulae for M, N and F
  /\ rmState' = [rmState EXCEPT ![r] = "blockAccepted"]
  /\ UNCHANGED <<primaryI, msgs>>

\* The next-state action.
Next ==
  \/ \E r \in RM : 
       RMSendPrepareRequest(r) \/ RMSendPrepareResponse(r) \/ RMSendCommit(r)
         \/ RMAcceptBlock(r)

\* A state predicate asserting that two RMs have not arrived at conflicting
\* decisions.  It is an invariant of the specification.
Consistent == \* TODO: need some more care.
  \/ TRUE
  \/ \A r1, r2 \in RM : ~ /\ rmState[r1] = "blockAccepted"
                          /\ rmState[r2] = "changeViewRequested"

\* The complete specification of the protocol written as a temporal  formula.  
Spec == Init /\ [][Next]_<<rmState, primaryI, msgs>>

\* This theorem asserts the truth of the temporal formula whose meaning is that
\* the state predicate TypeOK /\ Consistent is an invariant of the
\* specification Spec.  Invariance of this conjunction is equivalent to
\* invariance of both of the formulas TypeOK and Consistent.     
THEOREM Spec => [](TypeOK /\ Consistent)

=============================================================================
\* Modification History
\* Last modified Thu Dec 15 16:06:24 MSK 2022 by anna
\* Created Thu Dec 15 16:06:17 MSK 2022 by anna
