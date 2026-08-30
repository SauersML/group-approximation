---
rg: 2
id: stw87-finite-positive-lower-bound
kind: claim
title: Finite asymptotic dimension at least two lower-bounds uniform Roe nuclear dimension
artifacts:
  - research/artifacts/stw87-lxxxvii-uniform-roe-nuclear-dimension-audit-2026-08-30.md
---

For every countable discrete bounded-geometry metric space `X` with
`2 ≤ asdim(X) < ∞`, prove

```text
asdim(X) ≤ dim_nuc(C*_u(X)).
```

## Attempts

The coarse-embedding corner theorem propagates any known lower-bound seed:
it is enough that `X` coarsely contain a space `Y` of the same asymptotic
dimension for which equality is known, rather than contain `Y` literally as a
subspace.  No seed of value at least two is produced here; `X=ℤ²` is
already an unresolved seed.
Li--Liao--Winter identify asymptotic dimension with diagonal dimension, but
their comparison has the opposite direction.  Postcomposing arbitrary
nuclear-dimension return maps with the diagonal expectation cannot repair the
direction because that expectation destroys order zero in a two-point matrix
corner.  A solution therefore needs either a new nuclear lower-bound invariant
or a structured diagonal-recovery theorem, not raw expectation averaging.
Property-A Schur localization does not supply that structure: every normalized
diagonal-bimodular localization `S` satisfies `E_X S=E_X`, so localization
leaves both exact diagonal order-zero gaps unchanged
(`stw87-diagonal-bimodular-localization-no-go`).  A remaining support-extraction
route would have to use genuinely non-diagonal information before applying the
expectation or incur a macroscopic diagonal-fixing/bimodularity defect.
Quantitatively, any diagonal-valued c.p.c. recovery that keeps
the two-point packet order zero must have combined diagonal-fixing and
singleton-corner bimodularity defect at least `1/2`; a retained matrix packet
forces defect at least `1`
(`stw87-approximate-diagonal-bimodularity-order-zero-threshold`).
A literal metric-sparsification cutdown `a->E_X(chi_Omega a chi_Omega)` has
diagonal-fixing defect exactly one whenever `Omega` is proper, so one sparse
corner cannot give the missing global recovery either.  Any viable
sparsification argument must at least recombine several corners; the present
obstruction does not decide whether diagonal data could suffice after that
recombination.
