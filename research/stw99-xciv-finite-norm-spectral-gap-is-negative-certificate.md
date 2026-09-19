---
rg: 2
id: stw99-xciv-finite-norm-spectral-gap-is-negative-certificate
kind: claim
title: A finite norm-spectral-gap set is a quantitative negative certificate for XCIV
distinct_from:
  stw99-xciv-two-norm-centrality-does-not-control-norm-centrality: that gives bad representatives of one tracial sequence class but no negative criterion; this claim gives a sufficient operator-norm hypothesis for failure of separable Z-stability.
---

Let `B` be a unital C\*-algebra.  Suppose there are a finite set `F subset B`
and `kappa>0` such that

```text
dist(y,C 1_B) <= kappa max_{a in F} ||[y,a]||       (y in B).
```

Then `B` is not separably `Z`-stable.  Quantitatively, after fixing a
selfadjoint `h in Z` whose spectral diameter is `1`, every unital
homomorphism `phi:Z->B` satisfies

```text
max_{a in F} ||[phi(h),a]|| >= 1/(2 kappa).
```

In particular, finding such a finite norm-spectral-gap set in `R` would give
a negative answer to Problem XCIV.  No such set is asserted to exist here.
