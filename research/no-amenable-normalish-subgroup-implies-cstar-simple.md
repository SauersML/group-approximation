---
rg: 2
id: no-amenable-normalish-subgroup-implies-cstar-simple
kind: claim
title: "Breuillard–Kalantar–Kennedy–Ozawa: a group with no non-trivial finite normal subgroup and no amenable normalish subgroup is C*-simple"
distinct_from:
  cstar-simple-iff-amenable-subgroups-not-confined: that is Kennedy's characterization through confined subgroups (an iff); this is the earlier sufficient condition through normalish subgroups, which is not necessary
---

**ESTABLISHED (import).**

**Definition.** A subgroup `H ≤ G` is *normalish* if, for every `n ≥ 1` and `t_1,…,t_n ∈ G`, the intersection `⋂_i t_iHt_i^{-1}`
is infinite.

**Theorem (BKKO).** A discrete group with no non-trivial finite normal subgroups and no amenable normalish subgroups is
C*-simple.

**The converse fails**, in the same source: `BS(m,n)` is C*-simple, and `⟨a⟩` is amenable, normalish and commensurated.

**Use for `G_X`.** The criterion does not apply, because `G_X` has an amenable normalish subgroup
(`cut-stabilizers-of-el-n-are-locally-finite-normalish`).

**Proof:** `no-amenable-normalish-subgroup-implies-cstar-simple-citation`.
