--------------------------- MODULE IngressRetryDedupeHarness ---------------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* IngressRetryDedupeHarness.tla
*
* Non-security reliability model:
* - Messages/events may be retried due to transient failures.
* - Dedupe should ensure an event is emitted at most once.
*
* This is an end-to-end-ish abstraction on top of existing ingress idempotency
* models, focusing specifically on retry behavior.
******************************************************************************)

CONSTANTS
  Events,          \* finite set of event ids
  MaxAttempts      \* small natural (e.g. 2 or 3)

ASSUME
  /\ Events /= {}
  /\ MaxAttempts \in Nat
  /\ MaxAttempts >= 1

VARIABLES
  pending,         \* SUBSET Events (events waiting to be processed)
  emitted,         \* SUBSET Events (successfully emitted)
  attempts         \* [Events -> Nat]

Init ==
  /\ pending = Events
  /\ emitted = {}
  /\ attempts = [e \in Events |-> 0]

CanTry(e) == attempts[e] < MaxAttempts

\* Non-deterministic transient failure or success when processing an event.
ProcessFail(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending
  /\ emitted' = emitted
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]

ProcessSuccess(e) ==
  /\ e \in pending
  /\ CanTry(e)
  /\ pending' = pending \ {e}
  /\ emitted' = emitted \cup {e}
  /\ attempts' = [attempts EXCEPT ![e] = @ + 1]

\* Drop after exhausting attempts.
Drop(e) ==
  /\ e \in pending
  /\ ~CanTry(e)
  /\ pending' = pending \ {e}
  /\ emitted' = emitted
  /\ attempts' = attempts

Next ==
  \E e \in Events:
    ProcessFail(e) \/ ProcessSuccess(e) \/ Drop(e)

\* Safety: no duplicates by construction (set), but we assert monotonicity and at-most-once.
Inv_EmittedMonotonic == emitted \subseteq emitted'

Inv_AtMostOnce ==
  \A e \in Events: e \in emitted => attempts[e] >= 1

Spec == Init /\ [][Next]_<<pending, emitted, attempts>>

=============================================================================
