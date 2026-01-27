------------------------------ MODULE IngressMultiMessageTraceHarness ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* IngressMultiMessageTraceHarness.tla
*
* Roadmap R2++: richer ingress multi-message traces / provider nuances.
*
* Motivation:
*   Some providers deliver a single user action as multiple webhook messages
*   (e.g. text + attachment, or multipart payloads). Internally, we may emit
*   multiple ingress messages for a single external event.
*
* We want a simple traceability invariant:
*   If one external event is expanded into multiple internal messages,
*   all produced messages MUST carry the same correlation id (traceId) and the
*   same provider event id.
*
* This harness models a single ingest step that produces N parts.
******************************************************************************)

CONSTANTS
  Provider,         \* provider name/string
  EventId,          \* external provider event id/string
  TraceId,          \* correlation id/string
  NumParts          \* number of internal messages emitted for this event

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

\* "Green" ingest: all parts share same traceId + eventId.
Ingest ==
  /\ produced' = [i \in 1..NumParts |-> Msg(TraceId, Provider, EventId, i)]

Spec == Init /\ [][Ingest]_vars

Inv_AllPartsCorrelated ==
  (Len(produced) = NumParts) =>
    (NumParts <= 1 \/
      (\A i \in 1..NumParts:
         /\ produced[i].traceId = TraceId
         /\ produced[i].eventId = EventId
         /\ produced[i].provider = Provider))

=============================================================================
