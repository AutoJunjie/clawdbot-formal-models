---------------------- MODULE IngressRetryDedupeHarness_BadNoDedupe ----------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* Negative model:
* BUG: retry success can emit the same event multiple times because the event
* is not removed from pending on success.
******************************************************************************)

CONSTANTS
  Events,
  MaxAttempts

ASSUME
  /\ Events /= {}
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1

VARIABLES
  pending,
  emittedCount,     \* [Events -> Nat]
  attempts

Init ==
  /\ pending = Events
  /\ emittedCount = [e \in Events |-> 0]
  /\ attempts = [e \in Events |-> 0]

CanTry(e) == attempts[e] < MaxAttempts

ProcessFail(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending
  /\ emittedCount' = emittedCount
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]

\* BUG: does not remove from pending
ProcessSuccess(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending
  /\ emittedCount' = [emittedCount EXCEPT ![e] = @ + 1]
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]

Drop(e) ==
  /\ e \in pending
  /\ ~CanTry(e)
  /\ pending' = pending \ {e}
  /\ emittedCount' = emittedCount
  /\ attempts' = attempts

Next ==
  \E e \in Events:
    ProcessFail(e) \/ ProcessSuccess(e) \/ Drop(e)

Inv_NoDuplicateEmits ==
  \A e \in Events: emittedCount[e] <= 1

Spec == Init /\ [][Next]_<<pending, emittedCount, attempts>>

=============================================================================
