---
rg: 2
id: fix-sk-sk-rows-steinberg-weyl-diagonal
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Diagonal: Tactic simp failed with a nested error:"
---

**RESOLVED (9add2d485e, trusted batched probe job direct-b1789839564).** Previously OPEN. Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/SkRows/SteinbergWeyl/Diagonal.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 1 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: ms-green-sk.
Source changed on main since that build: yes.



**First errors (verbatim; from probe job direct-b1789837230 on main 296aff5838).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/SkRows/SteinbergWeyl/Diagonal.lean:83:0: automatically included section variable(s) unused in theorem `GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl.diagonal_weyl_eq`:
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Diagonal` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
