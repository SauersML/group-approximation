---
rg: 2
id: fpbs-rigid-f2xz-certified-strict-thresholds
kind: claim
title: The smallest rigidly decorated Cayley graph of F_2 x Z has p_c <= 0.091 < 0.0914 <= p_u, by exact computer-assisted certificates
distinct_from:
  fpbs-tree-projected-rigid-decorations-strict-thresholds: that asks for strict thresholds for every rigid decoration of every rank; this settles the one recorded rank-two example S_rig by a finite certificate and says nothing about other decorations.
  fpbs-tree-projected-large-rank-strict-thresholds: that uses the adjacency-norm criterion p_c < 1/||A||, which needs n >= 19 for rigid sets and fails for S_rig (1/||A|| = 0.0807, while Monte Carlo gives p_c close to 0.080); this replaces 1/||A|| by a Busemann-weighted Schur bound on cycle-avoiding walks and replaces the trivial p_c bound by a multitype Galton-Watson lower bound on theta.
  fpbs-tree-projected-sphere-bubble-l2-equivalence: that is an exact criterion at p_c with no numerical input; this avoids critical quantities altogether and brackets both thresholds by a p_c upper bound and a p_{2->2} lower bound at two explicit rationals.
artifacts:
  - experiments/fpbs-rigid-certificates-2026-09-17/star.c
  - experiments/fpbs-rigid-certificates-2026-09-17/certgw.py
  - experiments/fpbs-rigid-certificates-2026-09-17/rho2v.py
  - experiments/fpbs-rigid-certificates-2026-09-17/certschur.py
  - experiments/fpbs-rigid-certificates-2026-09-17/mc.c
  - experiments/fpbs-rigid-certificates-2026-09-17/outputs.txt
---

**ESTABLISHED (2026-09-17, computer-assisted, unreviewed)** through
`fpbs-rigid-f2xz-certified-strict-thresholds-proof`.

Let `S_rig = {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}^{±1}` in `F_2 x Z`. It is
the smallest recorded rigid decoration of
`fpbs-tree-projected-rigid-decorations-strict-thresholds`, and `Cay(F_2 x Z, S_rig)`
is 14-regular. For Bernoulli bond percolation on this graph,

```text
p_c  <=  91/1000  <  100/1093  <=  p_{2->2}  <=  p_u .
```

So `p_c < p_u`. The graph has discrete automorphism group
(`fpbs-tree-projected-rigid-decorations-discrete-automorphisms`), so Hutchcroft's
nonunimodular theorem does not apply. Rank two is far below the large-rank range
(`n >= 19`).

**The two certificates.** Both are finite, and both are checked in exact rational
or integer arithmetic. Floating point is used only to find the candidate vectors.
1. **Upper bound on `p_c`.**
   * *Construction.* A 64-type Galton-Watson process lives inside the open cluster.
     Its individuals are fibres `{w} x Z`, typed by the entry letter and a capped
     set of entry heights.
   * *Enumeration.* One "star stage" of an individual reveals three kinds of edge:
     * the vertical edges of its fibre in a window of heights;
     * the ladder edges to its three child fibres;
     * the back ladder edges from newly reached child vertices.

     A stage stops once the revealed configuration has probability below `1e-6`.
     Stages of different fibres own disjoint edge sets.
   * *Check.* At `p = 91/1000` the exact mean matrix (entries in `Q`) is
     irreducible. The Collatz-Wielandt check `Mv >= (101/100) v` holds exactly for
     a positive rational `v`, so `theta(91/1000) > 0`.
2. **Lower bound on `p_{2->2}`.**
   * *Walk bound.* `tau_p(x,y)` is at most `sum_n p^n W_n(x,y)`, where `W_n`
     counts walks with no cycle of length `<= 5`. This walk count is symmetric.
   * *Schur weight.* The weight is `h = c(sigma, t) u^(-beta)`.
     * `beta` is the Busemann function of a fixed end of the 4-regular tree.
     * `t` is the letter pointing toward that end.
     * `sigma` is the last four steps.
     * `u = 1732/1000`.
   * *Check.* An exact integer check over 29974 step-states times 4 letters gives
     the transfer inequality `F(c) <= (1093/100) c`. The Schur test then bounds
     `||T_p||_{2->2}` for `p < 100/1093`.
   * *Nonuniqueness.* By Harris-FKG, `tau_p` in `l^2` together with
     `theta_p > 0` rules out uniqueness.

**Calibration.**
* The Schur program with cycle-avoidance length 1 reproduces `||A|| = 2 + 6 sqrt 3`.
* With length 2 it reproduces the non-backtracking root of `lambda + 13/lambda = ||A||`.
* Monte Carlo (`mc.c`, 3000 clusters per p) puts `p_c` near `0.080`: `P(|C| >= 10^5)` is `0.020`, `0.112`, `0.204`
  and `0.267` at `p = 0.082, 0.085, 0.088, 0.091`.
* The certified window `[0.091, 0.0914]` therefore sits about 14% above `p_c`.
  `p_{2->2}` itself is not estimated.

**Why it works where the recorded attempts stopped.**
* The adjacency-norm route loses because `p_c ||A|| > 1` at rank two.
* The non-backtracking bound (cycle-avoidance length 2) gives only `p < 0.0890`.
  Length 3 gives `p < 0.0904`. Both are below the `p_c` upper bound we can
  certify.
* The Busemann weight exploits that at most one of the four letters at a vertex
  moves toward the end. Forbidding cycles up to length 5 removes the height-mixing
  short loops `(a,0)(1,1)(a,1)^{-1}`. Together they raise the certified `l^2`
  threshold to `0.09149`.
* On the other side, the star stage lets child vertices feed new vertices back into
  the parent fibre before the fibre is closed. A sequential ladder exploration,
  which closes the parent fibre first, did not certify any `p` near `0.091` in
  our runs. The star stage does, with a 1.6% margin in the Perron root.
* No symmetry, nonunimodularity or rank condition is used.
