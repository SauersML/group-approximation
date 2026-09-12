---
rg: 2
id: finite-torsion-carrier-criterion-proof
kind: route
title: Separate the finite torsion carrier and intersect the kernels
target: finite-torsion-carrier-virtual-torsionfree-criterion
requires: []
artifacts:
  - research/artifacts/luck-2008-section-11-status-and-finite-torsion-test-2026-08-30.md
---

Let `R=R_f(G)`.

`(1) => (5)`: if `H<=G` is torsion-free and has finite index, its normal core

```text
N = intersection { gHg^(-1) : g in G }
```

is normal and finite-index.  Since `N<=H`, it is torsion-free.

`(5) => (4)`: for the finite quotient `Phi:G -> G/N`, the kernel meets every
finite subgroup trivially.  Hence `Phi|F_i` is injective for every `i`.

`(4) => (1)`: put `N=ker(Phi)`.  If `1!=x in N` had finite order, then the
finite cyclic group `<x>` would be conjugate into some `F_i`.  Thus
`gxg^(-1) in F_i` for a suitable `g`.  Normality of `N` puts this nonidentity
element in `N intersect F_i`, contradicting injectivity of `Phi|F_i`.
Therefore `N` is a torsion-free finite-index subgroup.

`(2) <=> (3)`: one implication is immediate.  Conversely, if `R` contained a
nonidentity finite-order element `x`, then `<x>` would be conjugate into some
`F_i`.  The subgroup `R` is characteristic, hence normal, so a nonidentity
conjugate of `x` would lie in `R intersect F_i`.

Finally `(4) => (3)` because `R<=ker(Phi)`.  For `(3) => (4)`, the set

```text
T = union_i (F_i minus {1})
```

is finite.  For every `t in T`, the condition `t notin R` supplies a
homomorphism `phi_t:G -> Q_t` to a finite group with `phi_t(t)!=1`.  The
diagonal product

```text
Phi = product_(t in T) phi_t : G -> product_(t in T) Q_t
```

has finite target and kills no nonidentity element of any `F_i`; its
restriction to every `F_i` is therefore injective.  This closes the cycle of
implications.
