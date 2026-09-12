---
rg: 2
id: nonhyperlinear-from-fractional-pauli-pressure
kind: route
title: A supercritical fractional return network forbids atlas microstates
target: non-hyperlinear-group
requires:
  - atlas-steinberg-rank-five-translation
  - fractional-source-branch-pressure
  - soft-block-mass-yields-fractional-branch
  - atlas-fractional-pauli-return-network
---

This route is deliberately parallel to
`nonhyperlinear-from-supercritical-pauli-branching` and is **not** a second
proof of it.  That route consumes an *integer* branch matrix whose edges have
whole state projections as sources, supplied by
`atlas-supercritical-pauli-branching-cycle`.  This route consumes a *rational*
coverage matrix whose edges may capture any positive fraction of their state,
supplied by `atlas-fractional-pauli-return-network`.  Neither premise implies
the other: an integer network is the special case where every coverage is one,
and a fractional network can be supercritical with no edge of coverage one
outside the exact Pauli cell.  Both are kept because the searches are different
and only one of them has to succeed.

`atlas-steinberg-rank-five-translation` fixes the explicit finite atlas group
`Gamma_St` and its canonical trace target.  Suppose `Gamma_St` were
hyperlinear.  Then there are trace-preserving finite-dimensional microstates
whose fixed atlas relator defect `delta_n` tends to zero.

Apply `atlas-fractional-pauli-return-network` in the microstate `n`.  For each
edge of its fixed word menu, `soft-block-mass-yields-fractional-branch` converts
the measured block moment `m_e = ||P_j w_e P_i||_2^2` into a partial isometry
`T_e` whose source `E_e <= P_i` has

```text
tau(E_e) >= c_e tau(P_i),         c_e = [ (m_e/tau(P_i) - t^2)/(1-t^2) ]_+,
```

whose leakage out of `P_j` is identically zero by `(SBM3)`, and whose
ordered-pair Gram energy against a competing incoming branch is at most
`t^(-4) g_(ef)` by `(SBM4)`.  This is exactly the hypothesis `(FSB0)` of
`fractional-source-branch-pressure` with `a_e = 0`.

That node's `(FSB1)` gives the coordinate inequality

```text
x^(n) >= B x^(n) - eta^(n),      eta_j^(n) = 2 l_j^(n) + o_j^(n),
```

with `B` the rational coverage matrix.  Clause 3 of the network gives
`y . eta^(n) <= C delta_n^c`, and clause 2 gives the rational certificate
`B^T y >= (1+kappa)y`.  Then `(FSB3)` reads

```text
kappa (y . x^(n)) <= y . eta^(n) <= C delta_n^c -> 0,
```

while clause 4 gives `y . x^(n) >= c_0 > 0`.  Since `kappa` and `c_0` are fixed
and independent of `n`, this is a contradiction for large `n`.  Hence
`Gamma_St` is not hyperlinear.

Two soundness remarks that the route depends on.

- The exact Pauli edges of clause 1 have coverage one and supply the branching;
  by `(FSB4)` the only additional requirement in the two-child configuration is
  that the two return coverages sum above one.
- `supercritical-network-needs-noncanonical-cuts` is a mandatory check, not a
  decoration: if the network of `atlas-fractional-pauli-return-network` were
  built entirely from canonical states, words and thresholds, `(NCC1)` shows the
  premise is false, and this route would be vacuous rather than wrong.  The
  premise is stated so that finite-multiplicity refinement is permitted.
