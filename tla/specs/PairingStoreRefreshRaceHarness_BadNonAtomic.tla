------------------------------ MODULE PairingStoreRefreshRaceHarness_BadNonAtomic ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* PairingStoreRefreshRaceHarness_BadNonAtomic.tla
*
* "Red" variant: refresh is non-atomic (two-phase read+commit) and can create
* duplicate live rows for the same (channel,sender).
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

VARIABLES now, pending, inflight, step
vars == << now, pending, inflight, step >>

IsExpiredAt(req, t) == (t - req.createdAt) >= TTL
LiveFor(ch, s, t) == { r \in pending : r.ch = ch /\ r.sender = s /\ ~IsExpiredAt(r, t) }

Init ==
  /\ now = 0
  /\ step = 0
  /\ pending = { Req(CHOOSE ch \in Channels: TRUE,
                    CHOOSE s \in Senders: TRUE,
                    0,
                    0) }
  /\ inflight = [t \in Threads |-> [active |-> FALSE,
                                   ch |-> CHOOSE c \in Channels: TRUE,
                                   s |-> CHOOSE s \in Senders: TRUE,
                                   snapshot |-> CHOOSE r \in pending: TRUE,
                                   createdAt |-> 0]]

\* Begin refresh: snapshot ONE existing live row (stale read possible).
BeginRefresh(tid, ch, s) ==
  /\ step < MaxSteps
  /\ tid \in Threads /\ ch \in Channels /\ s \in Senders
  /\ ~inflight[tid].active
  /\ LiveFor(ch, s, now) /= {}
  /\ LET snap == CHOOSE r \in LiveFor(ch, s, now): TRUE IN
       inflight' = [inflight EXCEPT ![tid] = [active |-> TRUE,
                                             ch |-> ch,
                                             s |-> s,
                                             snapshot |-> snap,
                                             createdAt |-> now]]
  /\ step' = step + 1
  /\ UNCHANGED << now, pending >>

\* Commit refresh: remove only the snapshotted row, then add a new one.
CommitRefresh(tid) ==
  /\ step < MaxSteps
  /\ tid \in Threads
  /\ inflight[tid].active
  /\ pending' = (pending \ { inflight[tid].snapshot })
                \cup { Req(inflight[tid].ch, inflight[tid].s, inflight[tid].createdAt, step) }
  /\ inflight' = [inflight EXCEPT ![tid] = [@ EXCEPT !.active = FALSE]]
  /\ step' = step + 1
  /\ UNCHANGED now

Tick ==
  /\ step < MaxSteps
  /\ now < MaxTime
  /\ now' = now + 1
  /\ step' = step + 1
  /\ UNCHANGED << pending, inflight >>

Next ==
  (\E tid \in Threads, ch \in Channels, s \in Senders: BeginRefresh(tid, ch, s))
  \/ (\E tid \in Threads: CommitRefresh(tid))
  \/ Tick

Spec == Init /\ [][Next]_vars

Inv_NoDuplicateLive ==
  \A ch \in Channels, s \in Senders:
    Cardinality(LiveFor(ch, s, now)) <= 1

=============================================================================
