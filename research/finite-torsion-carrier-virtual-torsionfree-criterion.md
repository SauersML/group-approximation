---
rg: 2
id: finite-torsion-carrier-virtual-torsionfree-criterion
kind: claim
title: A finite torsion carrier makes virtual torsion-freeness a single finite-quotient test
distinct_from:
  non-residually-finite-hyperbolic-group: that open claim asks finite quotients to detect every nonidentity element of a hyperbolic group; this theorem only detects the finitely many finite subgroups carrying torsion and applies to any group with such a carrier
  finite-central-extension-rf-iff-virtually-splits: that criterion detects residual finiteness of a finite central extension through persistence of a degree-two class; this criterion detects virtual torsion-freeness through injectivity of one finite quotient on finitely many finite subgroups
artifacts:
  - research/artifacts/luck-2008-section-11-status-and-finite-torsion-test-2026-08-30.md
---

Let `G` be a group for which there are finite subgroups
`F_1,...,F_r <= G` such that every finite subgroup of `G` is conjugate into
one of the `F_i`.  Write

```text
R_f(G) = intersection { ker(phi) : phi:G -> Q, Q finite }.
```

Then the following are equivalent:

1. `G` is virtually torsion-free;
2. `R_f(G)` is torsion-free;
3. `R_f(G) intersect F_i = {1}` for every `i`;
4. there is one homomorphism `Phi:G -> Q` to a finite group whose restriction
   to every `F_i` is injective;
5. `G` has a finite-index normal torsion-free subgroup.

Thus virtual torsion-freeness is controlled by finitely many elements, even
when `G` is very far from residually finite.
