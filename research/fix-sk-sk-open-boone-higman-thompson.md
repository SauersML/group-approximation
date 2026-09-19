---
rg: 2
id: fix-sk-sk-open-boone-higman-thompson
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.BooneHigmanThompson: fails through red imports"
---

**RESOLVED (13d4765e1b, trusted batched probe job direct-b1789850259).** Previously OPEN. Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/SkOpen/BooneHigmanThompson.lean` is red on main at 463f140e0d (trusted batched probe, Slurm job 1398755). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-sk-open.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-sk-halfline-b-represent`, `fix-sk-simple-hosts-host`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.BooneHigmanThompson` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
