------------------------------ MODULE PairingStoreRefreshRaceHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* PairingStoreRefreshRaceHarness.tla
*
* Pairing-store concurrency nuance (R1++++): two concurrent refreshes for the
* same (channel, sender) must not create duplicate live pending rows.
*
* Motivation:
*   Even if refresh is intended to be idempotent, a non-atomic implementation
*   can race:
*     - T1 reads existing row R
*     - T2 reads existing row R
*     - T1 writes new row R1 (removing R)
*     - T2 writes new row R2 (removing R)
*   Result: both R1 and R2 live => duplicates.
*
* This harness models the "good" locked/atomic refresh.
******************************************************************************)

CONSTANTS
  Threads,
  Channels,
  Senders,
  TTL,
  MaxTime,
  MaxSteps

ASSUME
  /\ Threads /= {} /\ Channels /= {} /\ Senders /= {}
  /\ TTL \in 1..MaxTime
  /\ MaxTime \in 1..10
  /\ MaxSteps \in 1..30

Req(ch, sender, createdAt, rid) ==
  [ ch |-> ch, sender |-> sender, createdAt |-> createdAt, rid |-> rid ]

VARIABLES now, pending, step
vars == << now, pending, step >>

IsExpiredAt(req, t) == (t - req.createdAt) >= TTL
LiveFor(ch, s, t) == { r \in pending : r.ch = ch /\ r.sender = s /\ ~IsExpiredAt(r, t) }

Init ==
  /\ now = 0
  /\ step = 0
  /\ pending = { Req(CHOOSE ch \in Channels: TRUE,
                    CHOOSE s \in Senders: TRUE,
                    0,
                    0) }

\* Atomic refresh: remove ALL live rows for (ch,s), then add exactly one new row.
AtomicRefresh(tid, ch, s) ==
  /\ step < MaxSteps
  /\ tid \in Threads /\ ch \in Channels /\ s \in Senders
  /\ LiveFor(ch, s, now) /= {}
  /\ pending' = (pending \ LiveFor(ch, s, now)) \cup { Req(ch, s, now, step) }
  /\ step' = step + 1
  /\ UNCHANGED now

Tick ==
  /\ step < MaxSteps
  /\ now < MaxTime
  /\ now' = now + 1
  /\ step' = step + 1
  /\ UNCHANGED pending

Next ==
  (\E tid \in Threads, ch \in Channels, s \in Senders: AtomicRefresh(tid, ch, s))
  \/ Tick

Spec == Init /\ [][Next]_vars

Inv_NoDuplicateLive ==
  \A ch \in Channels, s \in Senders:
    Cardinality(LiveFor(ch, s, now)) <= 1

=============================================================================
