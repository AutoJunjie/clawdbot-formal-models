------------------------------ MODULE IngressEventIdempotencyHarness_BadNoDedupe ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* IngressEventIdempotencyHarness_BadNoDedupe.tla
*
* "Red" variant: no de-dupe; every delivery emits a message even if the eventId
* was seen before.
******************************************************************************)

CONSTANTS
  Events,
  MaxSteps

ASSUME
  /\ Events /= {}
  /\ MaxSteps \in 1..20

MsgId(e, n) == <<e, n>>

VARIABLES seen, emitted, step
vars == << seen, emitted, step >>

Init ==
  /\ seen = {}
  /\ emitted = {}
  /\ step = 0

Deliver(e) ==
  /\ step < MaxSteps
  /\ e \in Events
  /\ seen' = seen \cup {e}
  /\ emitted' = emitted \cup { MsgId(e, step) }
  /\ step' = step + 1

Next == \E e \in Events: Deliver(e)

Spec == Init /\ [][Next]_vars

\* If the same event is delivered twice, we will have two emits for that event.
Inv_NoDuplicateEmit ==
  \A e \in Events: Cardinality({ m \in emitted : m[1] = e }) <= 1

=============================================================================
