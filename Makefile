TLC=./bin/tlc
MODEL?=tla/models/basic.cfg

.PHONY: tlc precedence precedence-negative groups groups-negative

# Run TLC with a pinned, in-repo model config

tlc:
	$(TLC) -workers auto -deadlock -config $(MODEL) tla/specs/ClawdbotSecurity.tla

# Prove monotonic "deny wins" for tool policy precedence
precedence:
	$(TLC) -workers auto -config tla/models/precedence_min.cfg tla/specs/ToolPolicyPrecedence.tla

# Negative test: demonstrate TLC catches a precedence bug where allow overrides deny
precedence-negative:
	$(TLC) -workers auto -config tla/models/precedence_negative_bad_allow_overrides.cfg tla/specs/ToolPolicyPrecedence_BadAllowOverrides.tla

# Tool group expansion checks

groups:
	$(TLC) -workers auto -config tla/models/group_memory_ok.cfg tla/specs/ToolGroupExpansion.tla

groups-negative:
	$(TLC) -workers auto -config tla/models/group_memory_bad_missing.cfg tla/specs/ToolGroupExpansion.tla
