------------------------------ MODULE IngressMultiMessageTraceHarness_BadMissingTrace ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* IngressMultiMessageTraceHarness_BadMissingTrace.tla
*
* "Red" variant: the ingest expansion forgets to attach the traceId to all
* produced parts (e.g., only the first part gets a trace id).
******************************************************************************)

CONSTANTS
  Provider,
  EventId,
  TraceId,
  NumParts

ASSUME
  /\ Provider \in STRING
  /\ EventId \in STRING
  /\ TraceId \in STRING
  /\ NumParts \in 1..5

Msg(trace, provider, eventId, idx) ==
  [ traceId |-> trace,
    provider |-> provider,
    eventId  |-> eventId,
    partIdx  |-> idx ]

VARIABLES produced
vars == << produced >>

Init == produced = << >>

\* BUG: only the first part carries TraceId; later parts use "".
Ingest ==
  /\ produced' = [i \in 1..NumParts |->
        IF i = 1 THEN Msg(TraceId, Provider, EventId, i)
        ELSE Msg("", Provider, EventId, i)]

Spec == Init /\ [][Ingest]_vars

Inv_AllPartsCorrelated ==
  (Len(produced) = NumParts) =>
    (NumParts <= 1 \/
      (\A i \in 1..NumParts:
         /\ produced[i].traceId = TraceId
         /\ produced[i].eventId = EventId
         /\ produced[i].provider = Provider))

=============================================================================
