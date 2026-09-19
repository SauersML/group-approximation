---
rg: 2
id: mf-relation-closure
kind: claim
title: The MF radical of relations is an idempotent closure operator
distinct_from:
  universal-mf-quotient: That claim constructs the universal MF quotient of one group; this one organizes the same radical as a closure operator on the normal-subgroup lattice of a fixed ambient group, whose fixed points are exactly the normal subgroups with MF quotient.
  mf-universal-horn-obstruction: That claim exhibits one finite quasi-identity valid in every MF group; this one names the full semantic consequence operation of which any such Horn sentence is a finite fragment.
---

Let `G` be countable and `N <= G` normal.  Define the **MF radical of the
relations `N`**

```text
mfroot(N)  =  intersection of  ker(phi)
              over homomorphisms  phi : G -> M,  M countable MF,  N <= ker(phi).
```

Then:

1. `mfroot` is extensive, monotone, and idempotent — a closure operator on
   the normal-subgroup lattice of `G`;
2. `mfroot(N)` is the preimage of `Rad_MF(G/N)` under `G -> G/N`, so
   `mfroot(N)/N = Rad_MF(G/N)`;
3. `G/mfroot(N)` is MF;
4. `N = mfroot(N)`  if and only if  `G/N` is MF.

**Semantic reading.**  Take `G = F` free on `X` and `N = <<R>>`.  Then
`w in mfroot(N)` says exactly: every solution of the relations `R` in every
countable MF group also satisfies `w = 1`.  So `<X | R>` is non-MF precisely
when the MF-semantic consequences of `R` strictly exceed its group-theoretic
consequences, and every non-MF argument in this program exhibits an element
of `mfroot(N) \ N` — the marked witnesses (`u`, the central sign, the
Reynolds corner) are elements of this difference, never the theory.
`mf-universal-horn-obstruction` is one visible finite fragment of the
closure.  The program-level reformulation this claim licenses: **compute the
closure of the defining relations, not a preferred witness.**
