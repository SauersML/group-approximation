# audit-nm-3: fidelity audit, non-MF tex 797–1337 (One-sided inverses and elementary groups)

Lane: wave-3 audit lane, session nonsofic-existence-49 (brief `ct/ROSTER-wave3.md`).

## CLAIM

CLAIM audit of census rows graded `formalized` or `definition` for non_mf_groups_exist.tex 797–1337
(sections "One-sided inverses and elementary groups", "The binary example", "MF quotients of unit groups").
Report path only; this lane writes no Lean unless a fix is trivial and unowned.

## Scope and method

- Census: merge 3 at 3f3f4c5c3 (tex md5 4c3bbe4cd565d9463d46a4d5a1c69310, unchanged at origin 61a292171).
  140 rows in range: 127 `formalized`, 13 `definition`.
- Root: GroupApproximation.lean at a1f1820bd (wave 19).
- For each row: printed sentence against each carrier's displayed statement (generality, quantifiers,
  hypotheses, constants); printed route; closed (`#audit_closed_axioms`, no Prop binder standing for a cited
  or unproved result); root-reachable. Subsumption: a stronger carrier must imply the printed sentence.
- Verdicts: PASS, FALSE-GREEN, ROUTE-DIFF, GENERALITY-GAP. Every non-PASS verdict carries evidence.

## Verdicts

(in progress)
