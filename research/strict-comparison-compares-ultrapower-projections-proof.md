---
rg: 2
id: strict-comparison-compares-ultrapower-projections-proof
kind: route
title: Glimm witness, Rordam cut-down and diagonalization in the tracial ultrapower
target: strict-comparison-compares-ultrapower-projections
requires: []
artifacts:
  - research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md
---

Proof in Section 1 of the artifact.  Lift `p, q` to positive contractions
`a_n, b_n`; the defects `tau(a_n - a_n^2)`, `tau(b_n - b_n^2)` and the excess
`tau(a_n) - tau(b_n)` tend to zero uniformly along `omega`, the last by a
limit-trace compactness argument.  Glimm's lemma gives `c_l in A_+` with
`d_tau(c_l) <= 1/l` and `m_l = inf_tau tau(c_l) > 0`.  The spectral inequalities
`1_(1/2,1](t) <= t + 2t(1-t)`, `t <= 1_(1/2,1](t) + 2t(1-t)` and
`t <= 1_(delta,1](t) + delta` give, once the defects are below `m_l/8`,

```text
d_tau((a_n-1/2)_+) < d_tau((b_n-1/2)_+ (+) (c_l-m_l/4)_+)   for all tau.
```

Strict comparison and Rordam's lemma give `x` with `x*x = (a_n-3/4)_+ (+) 0`
and `xx*` in the hereditary subalgebra of the right side.  Compressing to the
first corner removes at most trace `1/(4l)`, and a continuous `g` equal to `1`
on `[1/2,1]` and `0` on `[0,1/4]` keeps the range under `g(b_n)`, which tends to
`q`.  Diagonalizing `l -> infinity` along `omega` gives `w` with `w*w = p/4` and
`ww* = q ww* q`, so `v = 2w`.  Standard inputs used without re-reading: Glimm's
lemma for non-type-I algebras, Rordam's cut-down lemma, Haagerup's theorem
identifying quasitraces with traces on exact algebras.
