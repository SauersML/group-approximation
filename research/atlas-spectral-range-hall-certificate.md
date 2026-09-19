---
rg: 2
id: atlas-spectral-range-hall-certificate
kind: claim
title: Atlas low-energy block ranges have a linear Hall deficit
distinct_from:
  atlas-wedderburn-hall-deficient-support-certificate: that uses only a hard zero/nonzero graph of whole Wedderburn blocks; this target keeps the actual low-energy range subspace inside every nonzero rectangular block.
  atlas-spectral-shrunk-intertwiner-certificate: that allows an arbitrary non-coordinate shrunk input subspace; this target asks for the stronger but algorithmically cheaper certificate obtained from a union of source Fourier blocks.
  atlas-paired-operator-scaling-no-go: that rules out fixed two-term paired equations; this target must use genuinely mixed atlas information, microstate-dependent spectral selection, or both.
---

There are constants `C,p,gamma>0` and a threshold rule `a(delta)>0` with

```text
C delta^p / a(delta) -> 0,                            (ARH1)
```

such that every sufficiently accurate finite-dimensional regular-`A_8` atlas
microstate has a positive quadratic form

```text
E_delta(T)=<T,L_delta T>
```

built from a fixed finite mixed atlas packet and satisfying

```text
E_delta(U) <= C delta^p                              (ARH2)
```

for its relative chart unitary `U`.

Let `K_delta` be the spectral subspace of `L_delta` for eigenvalues in
`[0,a(delta)]`.  Decompose source and target coefficient spaces by the fixed
finite `A_8` Wedderburn/Fourier blocks `H_i` and `H'_j`.  For each rectangular
block define its collective low-energy range

```text
R_(j,i)=span{p'_j T x : T in K_delta, x in H_i} <= H'_j.
```

Then for some source-block subset `A=A(delta)` one has

```text
sum_(i in A) dim(H_i)
  - sum_j dim(sum_(i in A) R_(j,i)) >= gamma d.        (ARH3)
```

The subset and the low-energy range spaces may depend on the finite
multiplicity data; the relator menu and constants are uniform.

## Why this is a high-leverage finite certificate

By `block-range-hall-implies-shrunk-subspace`, `(ARH3)` directly supplies the
shrunk subspace required by `atlas-spectral-shrunk-intertwiner-certificate`.
Unlike hard support Hall, a nonzero rectangular block may contribute only a
small spectral range and therefore need not be deleted completely.

By `block-range-hall-search-is-submodular`, the best subset `A` is found by
minimizing an explicit submodular function of the source Fourier blocks.  Thus
once a candidate mixed quadratic form is written down, the combinatorial
separator is exact finite linear algebra rather than a heuristic operator-
scaling search.

## Attempts

- **Interior-first Laplacian.** Include collision `19243` or another genuinely
  mixed interior relation before taking the spectral cutoff.  The established
  paired-equation no-go shows that boundary alignment plus the transverse
  bridge alone has a unitary-rich zero-energy space and cannot satisfy
  `(ARH3)`.
- **Range spans before singular values.** For every low-energy rectangular
  block, compute only the span of all output columns.  This loses information
  compared with full noncommutative rank but is much cheaper and already
  strictly finer than zero/nonzero block support.
- **Only eigenvalue cutoffs matter.** By
  `spectral-range-hall-deficit-is-cutoff-monotone`, enlarging the low-energy
  spectral window can only decrease every block-range Hall deficit.  For one
  candidate Laplacian, search the discrete eigenvalue cutoffs starting at the
  smallest threshold compatible with `(ARH1)`; once the objective is
  nonpositive it can never revive at a larger cutoff.
- **Exact finite falsification.** Replay the range-rank objective on archived
  finite boundary and natural-overgroup countermodels.  A candidate packet or
  cutoff which has no positive normalized deficit there should not be promoted.
- **Failure is informative.** If the minimum range-Hall objective stays
  nonnegative for every threshold compatible with `(ARH1)`, this route is
  dead but the full spectral shrunk-space target remains open at genuinely
  non-coordinate input subspaces.
