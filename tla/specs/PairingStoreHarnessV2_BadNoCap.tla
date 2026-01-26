------------------------------ MODULE PairingStoreHarnessV2_BadNoCap ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* Negative test: BUGGY pairing store where RequestPair ignores MaxPending cap.
* This is a standalone copy of PairingStoreHarnessV2 with a modified RequestPair.
******************************************************************************)

CONSTANTS
  Channels,
  Senders,
  TTL,
  MaxPending,
  MaxTime,
  MaxEvents

ASSUME
  /\ Channels /= {} /\ Senders /= {}
  /\ TTL \in 1..MaxTime
  /\ MaxPending \in 1..5
  /\ MaxTime \in 1..20
  /\ MaxEvents \in 1..10

Req(ch, sender, createdAt) == [ch |-> ch, sender |-> sender, createdAt |-> createdAt]
Approval(ch, sender, at) == [ch |-> ch, sender |-> sender, at |-> at]

VARIABLES now, pending, allowFrom, requestLog, approveLog
vars == << now, pending, allowFrom, requestLog, approveLog >>

IsExpiredAt(req, t) == (t - req.createdAt) >= TTL
LivePendingAt(ch, t) == { r \in pending : r.ch = ch /\ ~IsExpiredAt(r, t) }

Init ==
  /\ now = 0
  /\ pending = {}
  /\ allowFrom \in [Channels -> SUBSET Senders]
  /\ \A ch \in Channels: allowFrom[ch] = {}
  /\ requestLog = << >>
  /\ approveLog = << >>

EventCount == Len(requestLog) + Len(approveLog)

\* BUG: ignores MaxPending
RequestPair(ch, s) ==
  /\ ch \in Channels /\ s \in Senders
  /\ EventCount < MaxEvents
  /\ pending' = pending \cup { Req(ch, s, now) }
  /\ requestLog' = Append(requestLog, Req(ch, s, now))
  /\ UNCHANGED << now, allowFrom, approveLog >>

Approve(ch, s) ==
  /\ ch \in Channels /\ s \in Senders
  /\ EventCount < MaxEvents
  /\ \E r \in pending: r.ch = ch /\ r.sender = s /\ ~IsExpiredAt(r, now)
  /\ allowFrom' = [allowFrom EXCEPT ![ch] = @ \cup {s}]
  /\ pending' = { r \in pending : ~(r.ch = ch /\ r.sender = s) }
  /\ approveLog' = Append(approveLog, Approval(ch, s, now))
  /\ UNCHANGED << now, requestLog >>

Tick ==
  /\ now < MaxTime
  /\ now' = now + 1
  /\ UNCHANGED << pending, allowFrom, requestLog, approveLog >>

Next ==
  (\E ch \in Channels, s \in Senders: RequestPair(ch, s))
  \/ (\E ch \in Channels, s \in Senders: Approve(ch, s))
  \/ Tick

Spec == Init /\ [][Next]_vars

Inv_PendingCap ==
  \A ch \in Channels: Cardinality(LivePendingAt(ch, now)) <= MaxPending

=============================================================================
