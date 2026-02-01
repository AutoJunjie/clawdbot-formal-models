------------------- MODULE MultiEventEventualEmissionHarness_BadNoE2 -------------------
EXTENDS Naturals

(******************************************************************************
* Negative model:
* BUG: Success for e2 is impossible, so even with fairness assumptions,
* we cannot reach AllEmitted.
******************************************************************************)

CONSTANTS
  Events

ASSUME
  Events = {"e1","e2"}

VARIABLES
  pending,
  emitted,
  togg

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
  /\ e /= "e2" \* BUG: e2 can never succeed
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

Spec ==
  Init /\ [][Next]_<<pending, emitted, togg>>
    /\ WF_<<pending, emitted, togg>>(Success("e1"))
    /\ WF_<<pending, emitted, togg>>(Success("e2"))

Live_AllEmitted == <>AllEmitted

=============================================================================
