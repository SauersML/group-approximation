---
rg: 2
id: fix-sk-leavitt-k2-field-two-action
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoAction: automatically included section variable(s) unused in theorem ..."
---

**RESOLVED (a39af618f3, trusted batched probe job direct-b1789834028).** Previously OPEN. Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/FieldTwoAction.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 1 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: ms-green-sk.
Source changed on main since that build: yes.


**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittK2/FieldTwoAction.lean:59:0: automatically included section variable(s) unused in theorem `GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTw
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoAction` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
