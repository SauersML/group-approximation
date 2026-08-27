---
rg: 2
id: connell-group-ring-primality-citation
kind: route
title: Import Connell's Theorem 8
target: connell-group-ring-primality
requires: []
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

Citation import.  I. G. Connell, *On the Group Ring*, Canadian Journal of
Mathematics **15** (1963), 650--685, DOI 10.4153/CJM-1963-067-0, Theorem 8.

**Trust surface.**  One refereed journal paper from 1963, not re-derived here
and not read in the original during this ingestion — it is quoted through the
source document audited in
`research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md`.  The
statement is standard and appears with the same numbering in Passman's
*The Algebraic Structure of Group Rings* as part of the Delta-method chapter,
which is where the `Delta(G) = 1` form used here comes from.

**Why the trust surface is thin in practice.**  This graph consumes the
criterion once, at `leavitt-unit-group-algebra-is-prime`, and there the group
hypothesis holds in the strongest possible way: the group has no proper
finite-index subgroup whatsoever, by a theorem formalized in this repository
(`elementaryGroup_finite_quotient_trivial`).  A reader who distrusts the
import can replace it with the elementary Delta-method argument for
`Delta(G) = 1`, which is a page and is not conditional on anything here.

This is a **LITERATURE_INPUT** premise.  Anything resting on it — currently
`leavitt-unit-group-algebra-is-prime` and, through it,
`leavitt-evaluation-does-not-split-as-module-map` — is established modulo a
transcription that no gate in this repository checks.
