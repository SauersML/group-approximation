---
rg: 2
id: hyperbolic-prime-torsion-residual-dichotomy
kind: claim
title: Prime torsion in a hyperbolic finite residual is central-finite or normally non-elementary
distinct_from:
  finite-torsion-carrier-virtual-torsionfree-criterion: that tests every nonidentity element in finitely many finite carrier subgroups; this reduces the test to prime-order cyclic subgroups and determines the hyperbolic geometry of every failure.
  hyperbolic-finite-residual-is-torsion-free: that is the open unrestricted assertion; this is an unconditional dichotomy and a sufficient criterion which does not claim that either obstruction is always absent.
  non-residually-finite-hyperbolic-group: that asks whether the entire finite residual can be nontrivial; this shows that a torsion obstruction is either central in the finite radical or generates a non-elementary normal subgroup.
artifacts:
  - research/artifacts/luck-2008-section-11-status-and-finite-torsion-test-2026-08-30.md
---

Let `G` be a non-elementary word-hyperbolic group, let

```text
R=R_f(G)
```

be its finite residual, and let `E=E(G)` be its maximal finite normal
subgroup.  Choose representatives `P_1,...,P_s` of the finitely many
conjugacy classes of subgroups of prime order.  Then the following are
equivalent:

1. `G` is virtually torsion-free;
2. `R` has no nonidentity element of prime order;
3. `R intersect P_j={1}` for every `j`;
4. one homomorphism from `G` to a finite group is injective on every `P_j`.

If these conditions fail, there are a prime `p` and `x in R` of order `p`.
For every such `x`, its normal closure `N=normal_closure_G(x)` satisfies
exactly one of the following:

1. `N` is finite, in which case `x in R intersect Z(E)`;
2. `N` is non-elementary, has limit set `boundary(G)`, and contains a
   nonabelian free subgroup.  In this case `N subset R`, so the finite
   residual itself is non-elementary.

Consequently:

- if `E(G)={1}`, every counterexample to virtual torsion-freeness has a
  non-elementary finite residual with full limit set;
- if `E(G)={1}` and `R_f(G)` is elementary, contains no nonabelian free
  subgroup, or is amenable, then `R_f(G)={1}`.  Thus `G` is residually finite
  and in particular virtually torsion-free.

This does not settle the unrestricted problem: a torsion element can still
lie in `R intersect Z(E)`, or can normally generate the non-elementary
alternative.
