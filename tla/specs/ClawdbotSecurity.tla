------------------------------ MODULE ClawdbotSecurity ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

(******************************************************************************
* ClawdbotSecurity.tla
*
* Purpose
*   A high-level, *reproducible* model of Clawdbot's security control plane.
*
* We model:
*   - sessions (main vs shared)
*   - tools (memory reads, external side effects, elevated execution)
*   - approval gates for risky actions
*
* We do NOT model implementation details; we model permissions + information flow.
*
* This spec is designed to be instantiated by a TLC config (.cfg) with small,
* finite sets so we can model-check invariants.
******************************************************************************)

CONSTANTS
  Users, Sessions, Providers, Tools,

  \* Distinguished sessions for the small TLC model
  MainSession, SharedSession,

  \* Tool categories (subsets of Tools)
  MemTools,        \* reading agent memory / private context
  ExternalTools,   \* sends messages / changes config / browser actions
  ElevatedTools    \* running commands with elevated privileges

SessionTypes == {"main", "shared"}

VARIABLES
  owner,           \* the "owner" principal
  sessionType,     \* Sessions -> SessionTypes
  sessionProvider, \* Sessions -> Providers

  \* approval gate: sessions currently awaiting explicit approval
  pendingApproval, \* SUBSET Sessions

  \* audit/trace (for TLC counterexamples)
  lastAction       \* [s \in Sessions |-> [tool: Tools \cup {"none"}]]

vars == << owner, sessionType, sessionProvider, pendingApproval, lastAction >>

(******************************************************************************
* Sanity assumptions about constants
******************************************************************************)
ASSUME
  /\ Users /= {} /\ Sessions /= {} /\ Providers /= {} /\ Tools /= {}
  /\ MainSession \in Sessions
  /\ SharedSession \in Sessions
  /\ MainSession /= SharedSession
  /\ MemTools \subseteq Tools
  /\ ExternalTools \subseteq Tools
  /\ ElevatedTools \subseteq Tools

(******************************************************************************
* Helper predicates
******************************************************************************)
IsMain(s) == sessionType[s] = "main"
IsShared(s) == sessionType[s] = "shared"

NeedsApproval(t) == t \in ExternalTools \/ t \in ElevatedTools

\* Policy: which tools are allowed to run (ignoring the approval gate)
AllowedByPolicy(s, t) ==
  IF IsShared(s) THEN
    \* shared contexts must never access memory tools;
    \* risky actions can be allowed but must be approved
    t \notin MemTools
  ELSE
    \* main context can use all tools; approval still required for risky ones
    TRUE

\* Full permission check, including approval gate
MayRun(s, t) ==
  /\ AllowedByPolicy(s, t)
  /\ IF NeedsApproval(t) THEN s \notin pendingApproval ELSE TRUE

(******************************************************************************
* Init
******************************************************************************)
Init ==
  /\ owner \in Users
  /\ sessionType \in [Sessions -> SessionTypes]
  /\ sessionProvider \in [Sessions -> Providers]
  /\ pendingApproval = {}
  /\ lastAction \in [Sessions -> [tool: Tools \cup {"none"}]]
  /\ \A s \in Sessions: lastAction[s].tool = "none"

(******************************************************************************
* Actions
******************************************************************************)
RunTool(s, t) ==
  /\ s \in Sessions
  /\ t \in Tools
  /\ MayRun(s, t)
  /\ lastAction' = [lastAction EXCEPT ![s].tool = t]
  /\ UNCHANGED << owner, sessionType, sessionProvider, pendingApproval >>

RequestApproval(s) ==
  /\ s \in Sessions
  /\ pendingApproval' = pendingApproval \cup {s}
  /\ UNCHANGED << owner, sessionType, sessionProvider, lastAction >>

GrantApproval(s) ==
  /\ s \in pendingApproval
  /\ pendingApproval' = pendingApproval \ {s}
  /\ UNCHANGED << owner, sessionType, sessionProvider, lastAction >>

Next ==
  (\E s \in Sessions, t \in Tools: RunTool(s, t))
  \/ (\E s \in Sessions: RequestApproval(s))
  \/ (\E s \in Sessions: GrantApproval(s))

Spec == Init /\ [][Next]_vars

(******************************************************************************
* Safety properties (invariants)
******************************************************************************)

\* Core non-leakage rule: in shared contexts, memory tools are never runnable: 
Inv_NoMemoryToolInShared ==
  \A t \in MemTools: \A s \in Sessions:
    IsShared(s) => ~MayRun(s, t)

\* If a tool needs approval, it cannot be run while approval is pending.
Inv_ApprovalGate ==
  \A s \in Sessions:
    s \in pendingApproval => (\A t \in Tools: NeedsApproval(t) => ~MayRun(s, t))

THEOREM Spec => []Inv_NoMemoryToolInShared
THEOREM Spec => []Inv_ApprovalGate

=============================================================================
