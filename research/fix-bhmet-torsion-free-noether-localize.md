---
rg: 2
id: fix-bhmet-torsion-free-noether-localize
kind: route
target: fp-metabelian-groups-satisfy-boone-higman
title: "Fix GroupApproximation.BooneHigman.Metabelian.TorsionFreeNoetherLocalize: unexpected token ':='; expected '}'"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/TorsionFreeNoetherLocalize.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 5 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/TorsionFreeNoetherLocalize.lean:129:16: unexpected token ':='; expected '}'
error: GroupApproximation/BooneHigman/Metabelian/TorsionFreeNoetherLocalize.lean:120:4: Insufficient number of fields for `⟨...⟩` constructor: Constructor `Exists.intro` has 2 explicit field, but only 1 was provided
error: GroupApproximation/BooneHigman/Metabelian/TorsionFreeNoetherLocalize.lean:120:5: Fields missing: `map_one'`, `map_mul'`
error: GroupApproximation/BooneHigman/Metabelian/TorsionFreeNoetherLocalize.lean:121:10: invalid {...} notation, expected type is not known
```

**Kind.** mechanical (Lean/Mathlib drift) (classification merged from the parallel node `fix-bh-met-torsion-free-noether-localize`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.TorsionFreeNoetherLocalize` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
