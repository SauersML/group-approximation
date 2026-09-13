---
rg: 2
id: vtf-iff-chern-quillen-class-dies-on-finite-index
kind: claim
title: Virtual torsion-freeness is exactly the non-persistence of the Chern–Quillen classes
distinct_from:
  finite-hyperbolic-residual-iff-persistent-class: that concerns degree-two classes on a residually finite hyperbolic base and captures only counterexamples with finite nontrivial residual; this concerns a class of degree at least 2(p-1) on the group itself and captures every failure of virtual torsion-freeness
  persistent-degree-two-class-on-hyperbolic-group: that is an open degree-two existence target on a residually finite base; this is a proved equivalence for one explicit class on any group with a finite proper contractible complex
  finite-torsion-carrier-virtual-torsionfree-criterion: that phrases virtual torsion-freeness through one finite quotient injective on the torsion carriers; this phrases it through the vanishing of one cohomology class on a finite-index subgroup
artifacts:
  - research/artifacts/hyperbolic-vtf-chern-quillen-persistence-2026-09-12.md
---

Let `G` satisfy the hypotheses of `chern-quillen-class-detects-all-prime-order-torsion`.
For example `G` can be any word-hyperbolic group. Let `M` be the lcm of the orders of
its finite subgroups. The following are equivalent.

1. `G` is virtually torsion-free.
2. For every prime `p | M`, some Chern–Quillen class of `G` at `p` vanishes on some
   finite-index subgroup.
3. For every prime `p | M`, every Chern–Quillen class at `p` vanishes on some
   finite-index subgroup.

**Persistence.** If the finite residual `R_f(G)` contains an element of order `p`,
then every Chern–Quillen class `c` at `p`, and every power `c^(p^k)`, is nonzero on
**every** finite-index subgroup.

**Lück 11.1(i) as a persistence question.** Some word-hyperbolic group is not
virtually torsion-free if and only if some word-hyperbolic group carries a persistent
Chern–Quillen class. Unlike the degree-two persistent classes of
`finite-hyperbolic-residual-iff-persistent-class`, this class lives on the
counterexample itself, and it captures every counterexample, not only those with
finite residual.

**Calibration.** `Z/p x F_2` is virtually torsion-free, and its classes die on `F_2`.
A non-hyperbolic real object with persistent classes is sketched in artifact §5: a
torsion-free simple lattice in a product of trees amalgamated with `Z/p x| Z`.

Proof: `vtf-iff-chern-quillen-class-dies-on-finite-index-proof`. Unreviewed; not
Lean-verified.
