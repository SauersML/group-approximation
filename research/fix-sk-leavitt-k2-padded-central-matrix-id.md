---
rg: 2
id: fix-sk-leavitt-k2-padded-central-matrix-id
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.MatrixId: Tactic rewrite failed: Did not find an occurrence of the pattern"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/PaddedCentral/MatrixId.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 1 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: ms-green-sk.
Source changed on main since that build: yes.


**First errors (verbatim; from probe job direct-b1789834028 on main a39af618f3).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/PaddedCentral/MatrixId.lean:40:48: Type mismatch
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/PaddedCentral/MatrixId.lean:43:14: 'GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.one_add_single_mulVec_single_of_ne' depends on axioms outside the
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.MatrixId` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
