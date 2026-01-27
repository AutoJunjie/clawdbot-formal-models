------------------------------ MODULE IngressEventIdempotencyHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* IngressEventIdempotencyHarness.tla
*
* Roadmap R2++++: ingress provider-event idempotency / de-dupe.
*
* Motivation:
*   Many providers retry webhook deliveries. If we key idempotency on provider
*   event id, then re-deliveries of the same event must not produce duplicate
*   internal messages / effects.
*
* Model:
*   - Seen: set of provider event ids already processed
*   - Emitted: set of internal message ids emitted (we simplify: one msg per event)
*   - Deliver(e): webhook delivery of event e
*
* Green behavior:
*   Deliver(e) emits exactly once and records e in Seen; repeats are no-ops.
*
* Safety:
*   For any event e, at most one emitted message is associated with e.
******************************************************************************)

CONSTANTS
  Events,
  MaxSteps

ASSUME
  /\ Events /= {}
  /\ MaxSteps \in 1..20

MsgId(e) == "msg-" \o e

VARIABLES seen, emitted, step
vars == << seen, emitted, step >>

Init ==
  /\ seen = {}
  /\ emitted = {}
  /\ step = 0

Deliver(e) ==
  /\ step < MaxSteps
  /\ e \in Events
  /\ IF e \in seen THEN
       /\ UNCHANGED << seen, emitted >>
     ELSE
       /\ seen' = seen \cup {e}
       /\ emitted' = emitted \cup { MsgId(e) }
  /\ step' = step + 1

Next == \E e \in Events: Deliver(e)

Spec == Init /\ [][Next]_vars

Inv_NoDuplicateEmit ==
  \A e \in Events: Cardinality({ m \in emitted : m = MsgId(e) }) <= 1

=============================================================================
