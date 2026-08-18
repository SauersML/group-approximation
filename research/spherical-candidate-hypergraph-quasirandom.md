---
rg: 2
id: spherical-candidate-hypergraph-quasirandom
kind: claim
title: Trace separation makes the candidate transition hypergraph quasirandom
distinct_from:
  hypergraph-absorption-schreier-matching: that is a purely combinatorial implication — quasirandomness in, simultaneous matchings out — with no spheres and no unitaries in it; this is the probabilistic input, an estimate about a random point cloud and a given trace-separated unitary table, with no matching in its conclusion.
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Target (GSD-1 of the source dossier).**  Let `{U_s}` be a finite unitary
table with normalized-HS multiplicative defect `< delta` and regular-trace
separation `< delta`, and let `X` be `N` independent uniform points of
`S^{2d-1}`.  Form the coloured candidate hypergraph whose vertices are the
generator-input and generator-output slots on `X` and whose edges record
locally compatible transition choices — for a relation `gh = k`, the
quadruples `(i,j,l,m)` with `‖U_h x_i - x_j‖ ≤ r`, `‖U_g x_j - x_l‖ ≤ r`,
`‖U_k x_i - x_m‖ ≤ r`.  Then with high probability, and with all constants
independent of `d`:

- vertex degrees are almost uniform in each colour class;
- codegrees for *distinct* group words are controlled — this is where trace
  separation should enter, since `tau(U_{w^{-1}w'}) ≈ 0` says two words send a
  typical point to nearly orthogonal images, so their candidate neighbourhoods
  should overlap only by the amount two independent random caps would;
- the divisibility conditions required by a simultaneous matching theorem hold.

**Why this is the tractable half.**  It is a finite high-dimensional
probability calculation about caps on a sphere, not a statement about groups:
the quantities involved are `Pr[‖U x - y‖ ≤ r]` for independent uniform `x,y`
and its joint versions along a word, and the input from the algebra is only
the second-moment data of
`hs-defect-is-mean-square-sphere-displacement`.  It is the natural first
target of the whole design programme, and its failure would kill
`geometric-schreier-design` without any combinatorics being attempted.

## Attempts

- **Bound codegrees by independence of the caps.**  The obstruction is that
  the caps are *not* independent: `U_w x` and `U_{w'} x` are two deterministic
  functions of the same `x`, so what is needed is a concentration statement
  for the pair, driven by `E‖U_wx - U_{w'}x‖^2 = 2 - 2Re tau(U_w^*U_{w'})`.
  Trace separation gives the mean; the missing step is concentration of the
  distance around it uniformly in `d`, which is plausible in high dimension
  (measure concentration on `S^{2d-1}`) but is exactly what has to be proved,
  and it is a claim about a *fixed* unitary pair, not a random one.
- **Assume the table is Haar-random.**  Illegitimate here — the microstate is
  handed to us by hyperlinearity and may be highly structured; the estimate
  must hold for any trace-separated table.  Recorded because it is the version
  a first draft will accidentally prove.
- **Choose `r` after `d`.**  Tempting and fatal: any threshold tuned to the
  ambient dimension re-introduces the dimension dependence the whole programme
  exists to avoid.  `r` must be chosen from the table and `eps` only, and the
  cap probabilities must be handled at whatever `d` arrives.
