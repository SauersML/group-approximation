---
rg: 2
id: fix-sk-simple-hosts-host
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleHosts.Host: failed to synthesize instance of type class"
---

**RESOLVED (eae37b23a2, trusted batched probe job direct-b1789842431).** Previously OPEN. Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/SimpleHosts/Host.lean` is red on main at 463f140e0d (trusted batched probe, Slurm job 1398755). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.


**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/SimpleHosts/Host.lean:55:24: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/SimpleHosts/Host.lean:55:9: Tactic `rcases` failed: `x✝ : ?m.109` is not an inductive datatype
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/SimpleHosts/Host.lean:75:14: 'GroupApproximation.SimpleKazhdanSofic.SimpleHosts.simpleKazhdanHost' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/SimpleHosts/Host.lean:76:14: 'GroupApproximation.SimpleKazhdanSofic.SimpleHosts.exists_simpleKazhdan_commutator_embedding' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleHosts.Host` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
