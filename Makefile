TLC=./bin/tlc
MODEL?=tla/models/basic.cfg

.PHONY: tlc

# Run TLC with a pinned, in-repo model config

tlc:
	$(TLC) -workers auto -deadlock -config $(MODEL) tla/specs/ClawdbotSecurity.tla
