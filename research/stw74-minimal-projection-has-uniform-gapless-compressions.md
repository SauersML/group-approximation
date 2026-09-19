---
rg: 2
id: stw74-minimal-projection-has-uniform-gapless-compressions
kind: claim
title: A minimal matrix projection over a counterexample has a uniformly gapless compression projective space
distinct_from:
  stw74-counterexamples-have-stationary-matrix-thresholds: that freezes the first matrix level at which projections occur; this extracts one fixed projection at that level and determines every scalar rank-one compression of it.
  stw74-projectionless-corner-forces-gapless-compressions: that says a nonzero scalar compression is gapless; this proves that no scalar compression of a minimal-level projection vanishes and obtains one uniform positive norm floor over all directions.
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

Let `A` be a counterexample to Problem LXXIV, let `D` be its full
projectionless hereditary corner, and fix `0!=a in D_+`.  There are a
strictly decreasing sequence `epsilon_k` tending to zero, an integer
`m>=2`, hereditary algebras

```text
H_k=Her_A((a-epsilon_k)_+),             H_k subset H_(k+1),
```

one nonzero properly infinite projection `p in M_m(H_1)`, and a number
`delta>0` such that

```text
M_j(H_k) has no nonzero projection       (1<=j<m, k>=1),
```

and every unit vector `xi in C^m` has scalar compression

```text
b_xi=(xi* tensor 1)p(xi tensor 1) in (H_1)_+
```

satisfying

```text
||b_xi||>=delta,
0 is an accumulation point of sigma(b_xi)\{0}.
```

Thus `xi mapsto b_xi` descends to a continuous map from
`CP^(m-1)` into the nonzero positive elements of `H_1`, uniformly bounded
away from zero in norm, while every image element has arbitrarily small
nonzero spectrum.  This is a forced diagonal obstruction: descent cannot
fail because a scalar direction misses the projective module, nor can it be
repaired by choosing a favourable direction with a spectral gap.
