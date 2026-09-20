---
rg: 2
id: fix-sk-full-sktfg-site-rep
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.SiteRep: simp does not unfold a set variable"
---

**RESOLVED (e7cefdce2b; trusted batched probe job direct-b1789878900, rc 0, no sorry, classical axioms only).** Was: Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/SiteRep.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job direct-b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: sk-tfg-b.


**Repair (green).** e7cefdce2b: the hsum simp call in siteRep_towerTable unfolds the set variable T, so rho_monoEval matches. Built green by request 1789863648.40826.sk-tfg-b (job direct-b1789878900).

**First errors (verbatim).** From the union log of batch b1789856358, after its red imports went green:

```
SiteRep.lean:158:13: typeclass instance problem is stuck
  AddCommMonoid ?m.329
SiteRep.lean:161:10: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (cylInd (Subshift.carrier ?S) (cylShift (-?l) ?cB)) ((subshiftHomeo ?S ^ ?s) ?x)
SiteRep.lean:155:6: This simp argument is unused:
```

The unused simp arguments are `rho_monoEval`, `add_zero`, `cylInd_nil`, `LocallyConstant.one_apply` and `one_mul`. The goal still had `SiteAction.rho T` with `T := subshiftHomeo S`, and `simp` does not unfold local definitions, so `rho_monoEval` never fired and the other two errors followed from it.

**Inputs.** None red: Cylinders is built green in batch b1789856358.

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.SiteRep` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
