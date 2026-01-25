------------------------------ MODULE ToolPolicyPrecedence_BadAllowOverrides ------------------------------
EXTENDS Naturals, FiniteSets

(******************************************************************************
* Negative test: an intentionally WRONG precedence rule.
*
* Here we model a bug where later allows can re-enable previously denied tools.
* We expect the deny-wins invariant to FAIL and TLC to produce a counterexample.
******************************************************************************)

CONSTANTS
  Tools,
  N,
  Allow1, Allow2, Allow3, Allow4, Allow5, Allow6, Allow7, Allow8,
  Deny1,  Deny2,  Deny3,  Deny4,  Deny5,  Deny6,  Deny7,  Deny8

ASSUME /\ Tools /= {} /\ N \in 1..8

Allow(i) == CASE i=1 -> Allow1 [] i=2 -> Allow2 [] i=3 -> Allow3 [] i=4 -> Allow4 []
                  i=5 -> Allow5 [] i=6 -> Allow6 [] i=7 -> Allow7 [] i=8 -> Allow8

Deny(i)  == CASE i=1 -> Deny1  [] i=2 -> Deny2  [] i=3 -> Deny3  [] i=4 -> Deny4  []
                  i=5 -> Deny5  [] i=6 -> Deny6  [] i=7 -> Deny7  [] i=8 -> Deny8

\* BUG: allow overrides deny by unioning allowed tools back in
ApplyLayerBad(allowed, i) == ((allowed \ Deny(i)) \cup Allow(i))

RECURSIVE FoldBad(_)
FoldBad(i) == IF i = 0 THEN Tools ELSE ApplyLayerBad(FoldBad(i-1), i)

FinalAllowedBad == FoldBad(N)

Inv_DenyWins ==
  \A i \in 1..N: \A t \in Deny(i): t \notin FinalAllowedBad

VARIABLE dummy
Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
