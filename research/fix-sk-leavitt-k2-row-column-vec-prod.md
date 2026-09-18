---
rg: 2
id: fix-sk-leavitt-k2-row-column-vec-prod
kind: route
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.VecProd: automatically included section variable(s) unused in theorem ..."
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/RowColumn/VecProd.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 2 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: ms-green-sk.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/RowColumn/VecProd.lean:35:0: automatically included section variable(s) unused in theorem `GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowC
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/RowColumn/VecProd.lean:60:0: automatically included section variable(s) unused in theorem `GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowC
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.VecProd` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
