---
rg: 2
id: inverse-conjugacy-padding-equals-multiplicity-defect
kind: claim
title: The least padding making a unitary inverse-conjugate by an involution is its eigenvalue multiplicity defect
distinct_from:
  flexible-hs-metric-controls-words-and-padding: that compares distances to a class over all dimensions and gives the sharp factor two between free and upward-only comparison; this counts the exact number of dimensions one algebraic relation forces, for a fixed unitary.
  bs14-trivial-boundary-inversion-forces-r-fixed-source: that solves the block equations of an exact dilation and identifies which source columns may couple; this ignores the boundary structure and counts spectrum.
artifacts:
  - research/artifacts/retained-core-and-rank-countertests-2026-09-08.md
---

**ESTABLISHED.**  Let `R in U(d)` with eigenvalue multiplicities `m_R`.  The
least `k >= 0` for which there is `R_new in U(k)` and a self-adjoint unitary
`X^` on `C^(d+k)` with

```text
X^ (R (+) R_new) X^ = (R (+) R_new)^(-1)                                (IC1)
```

is

```text
k_min(R) = sum_({lambda, lambda^(-1)}, lambda != +-1)
              | m_R(lambda) - m_R(lambda^(-1)) |,                       (IC2)
```

the sum running over unordered pairs of distinct mutually inverse spectral
values.  The eigenvalues `+-1` are self-paired and cost nothing.

**Necessity** is multiplicity matching: `(IC1)` makes `R (+) R_new` unitarily
equivalent to its inverse, so every pair `{lambda, lambda^(-1)}` must carry
equal multiplicities, and the added block must supply the difference on the
deficient side of each pair.  **Sufficiency** adds exactly the missing
eigenvalues and takes for `X^` the involution that swaps each paired
eigenspace by a unitary and its adjoint, acting as the identity on the `+-1`
eigenspaces.

The relation `(IC1)` is the involution-plus-inversion fragment `x^2 = (xr)^2 = 1`
of the Iwahori presentation, so `(IC2)` is a lower bound on the dimensions any
*core-retaining* completion must add, before any cubic relation is imposed.  It
is a spectral count, not an energy bound: nothing in the approximate data
controls it, and it can be as large as `d`, which is the content of
`scalar-phase-core-retention-forces-full-padding`.
