---
rg: 2
id: fix-sk-leavitt-k2-padded-central-vectors
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.Vectors: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/PaddedCentral/Vectors.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 2 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: ms-green-sk.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/PaddedCentral/Vectors.lean:117:48: Application type mismatch: The argument
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/PaddedCentral/Vectors.lean:125:48: Application type mismatch: The argument
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.Vectors` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
