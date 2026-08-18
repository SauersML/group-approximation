---
rg: 2
id: diracization-gap-equals-nonhyperlinear-group-proof
kind: route
title: Forward by continuity of a finite-word functional, backward by Hahn--Banach at an idempotent
target: diracization-gap-equals-nonhyperlinear-group
requires:
  - character-diracization-limit
  - ce-characters-closed-multiplicative-semigroup
  - hyperlinear-quotient-permanence-equivalence
---

**Forward.**  A finitely supported `L` is continuous for pointwise
convergence, so by `character-diracization-limit`

```text
Re L(1_{K_tau}) = lim_k Re L(|tau|^{2k}) >= sup_{CE} Re L + delta,
```

which puts `1_{K_tau}` outside `CE(Gamma)`.  By the dictionary in
`ce-characters-closed-multiplicative-semigroup` (item 4) that says exactly
that `Gamma/K_tau` is not hyperlinear.

**Backward.**  Let `G` be nonhyperlinear; by
`hyperlinear-quotient-permanence-equivalence` it may be taken finitely
generated, say `G = F_r/N`.  Take `Gamma = F_r` and `tau = 1_N`, which is a
character with `|tau|^{2k} = tau` for every `k` and `K_tau = N`.  The same
dictionary gives `tau not in CE(F_r)`.  `Ch(F_r)` sits in the locally convex
space `C^{F_r}` with the product topology, whose continuous real-linear
functionals are exactly `xi |-> Re L(xi)` for finitely supported `L`;
`CE(F_r)` is closed and convex there.  Hahn--Banach separation of the point
`tau` from `CE(F_r)` supplies such an `L` and a `delta > 0`, and the infimum
over `k` is taken over a constant sequence.  Hence `(D)`.

**Degeneracies.**  (1) `K_tau = {e}` gives limit `delta_e`, which lies in
`CE(Gamma)` whenever `Gamma` is hyperlinear -- in particular for `Gamma` free
-- so no `L` can separate it, and `(D)` fails.  (2) If `|tau|^2 in CE` then
all its powers and their limit lie in `CE` by the sub-semigroup and closure
properties, and again nothing separates.
