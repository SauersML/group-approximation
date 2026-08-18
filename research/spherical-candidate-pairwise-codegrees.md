---
rg: 2
id: spherical-candidate-pairwise-codegrees
kind: claim
title: Trace-separated spherical candidates have asymptotically vanishing pairwise relative codegrees
artifacts:
  - research/trace-separation-sphere-distance-concentration.md
---

Fix a finite tested word set `W`.  After harmless block-diagonal amplification,
let the unitary microstate dimension `d` tend to infinity and sample
independent uniform points `x_1,...,x_N` from the unit sphere of `C^d`.  For
radius `1`, define the candidate neighborhood

```text
N_w(i) = { j : ||U_w x_i - x_j|| <= 1 }.
```

Assume distinct tested words have regular-character separation

```text
|tau(U_w^* U_w')| = o(1)   (w != w').
```

There is a choice of `N=N(d)` with `N p_d -> infinity` sufficiently fast,
where `p_d` is the measure of a radius-one spherical cap, such that with
probability tending to one:

- for every tested `w`, all but `o(N)` input vertices satisfy
  `|N_w(i)|=(1+o(1)) N p_d`; and
- for every distinct tested pair `w != w'`, all but `o(N)` input vertices
  satisfy

```text
|N_w(i) cap N_w'(i)| = o(|N_w(i)|).
```

Thus the pairwise degree/codegree probability subproblem in
`spherical-candidate-hypergraph-quasirandom` is closed.  What remains there is
higher-order compatibility for the multiplication hyperedges and the
associated divisibility/design conditions; this claim does not supply the
simultaneous matching/absorption theorem.
