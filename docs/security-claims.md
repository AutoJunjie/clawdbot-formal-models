# Security Claims (to model-check)

This doc enumerates **concrete security claims** we want to be able to say about
Clawdbot, and links each claim to:

- a TLA+ invariant (or temporal property)
- one or more TLC scenario models (`tla/models/*.cfg`)

The intent is to provide *auditable assurance*: each claim should be backed by a
reproducible model run.

## Claims (draft)

### C1 — Shared contexts cannot access memory tools

**Statement:** In any `shared` session (public channel / group chat context), the
agent must not be able to execute `memory_search` or `memory_get`.

**TLA+ invariant:** `Inv_NoMemoryToolInShared`

**Scenarios:**
- `tla/models/discord_shared.cfg`

---

### C2 — Approval gate blocks risky tools while pending

**Statement:** For tools requiring explicit approval (external side effects or
privileged execution), if a session is currently awaiting approval, those tools
cannot run.

**TLA+ invariant:** `Inv_ApprovalGate`

**Scenarios:**
- `tla/models/basic.cfg`

---

### C3 — Tool policy precedence is monotone (deny wins)

**Statement:** Tool filtering is monotone: once a tool is denied by an earlier
policy layer, later layers cannot re-enable it.

**Source:** `clawdbot/docs/multi-agent-sandbox-tools.md` (Tool Restrictions order)

**TLA+ invariant:** `Inv_DenyWins` in `tla/specs/ToolPolicyPrecedence.tla`

**Scenarios:**
- `tla/models/precedence_min.cfg`

**Negative test (should FAIL):**
- `tla/models/precedence_negative_bad_allow_overrides.cfg` with `tla/specs/ToolPolicyPrecedence_BadAllowOverrides.tla`

---

### C4 — Tool groups expand to the documented tool sets

**Statement:** Shorthand entries like `group:memory` expand to exactly the set
of tools documented in `multi-agent-sandbox-tools.md`.

**Status:** TODO (encode and model-check)

---

### C5 — Elevated execution requires both global and agent allowlists

**Statement:** Elevated mode requires BOTH the global baseline (`tools.elevated`)
AND the agent-specific elevated gate (`agents.list[].tools.elevated`) to allow.

**Status:** TODO (encode and model-check)
