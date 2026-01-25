------------------------------ MODULE ToolGroupExpansion ------------------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* ToolGroupExpansion.tla
*
* Claim (from docs): tool groups expand to specific tool sets.
* For security, we care that group:memory expands to {memory_search, memory_get}
* (and not less / not more).
*
* We'll model a small universe Tools and a constant GroupMemory representing
* the implementation's expansion of group:memory.
******************************************************************************)

CONSTANTS
  Tools,
  memory_search, memory_get,
  GroupMemory

ASSUME
  /\ Tools /= {}
  /\ memory_search \in Tools
  /\ memory_get \in Tools
  /\ GroupMemory \subseteq Tools

Inv_GroupMemoryExact == GroupMemory = {memory_search, memory_get}

\* Trivial TLC behavior
VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
