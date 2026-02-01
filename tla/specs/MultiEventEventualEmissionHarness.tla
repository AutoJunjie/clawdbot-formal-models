----------------------- MODULE MultiEventEventualEmissionHarness -----------------------
EXTENDS Naturals

(******************************************************************************
* MultiEventEventualEmissionHarness.tla
*
* Liveness-lite model (2 events):
* - Both events start pending.
* - We can take Fail or Success steps for either event.
* - If Success for each pending event is weakly fair, then eventually both
*   events are emitted.
*
* This is intentionally tiny and uses 1-bit toggles to avoid unbounded growth.
******************************************************************************)

CONSTANTS
  Events

ASSUME
  Events = {"e1","e2"}

VARIABLES
  pending,   \* SUBSET Events
  emitted,   \* SUBSET Events
  togg       \* [Events -> {0,1}] progress bits

Init ==
  /\ pending = Events
  /\ emitted = {}
  /\ togg = [e \in Events |-> 0]

Fail(e) ==
  /\ e \in pending
  /\ pending' = pending
  /\ emitted' = emitted
  /\ togg' = [togg EXCEPT ![e] = 1 - @]

Success(e) ==
  /\ e \in pending
  /\ pending' = pending \ {e}
  /\ emitted' = emitted \cup {e}
  /\ togg' = togg

Stutter ==
  /\ pending' = pending
  /\ emitted' = emitted
  /\ togg' = togg

Next ==
  (\E e \in Events: Fail(e) \/ Success(e)) \/ Stutter

AllEmitted == emitted = Events

\* Fairness: if Success(e) stays enabled (i.e. e remains pending), it will occur.
Spec ==
  Init /\ [][Next]_<<pending, emitted, togg>>
    /\ WF_<<pending, emitted, togg>>(Success("e1"))
    /\ WF_<<pending, emitted, togg>>(Success("e2"))

Live_AllEmitted == <>AllEmitted

=============================================================================
