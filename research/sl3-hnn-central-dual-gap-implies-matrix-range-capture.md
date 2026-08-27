---
rg: 2
id: sl3-hnn-central-dual-gap-implies-matrix-range-capture
kind: route
title: Centralize a Hahn-Banach separator under the HNN letter
target: sl3-large-prime-hnn-matrix-range-capture
requires:
  - central-letter-averages-matrix-range-separators
  - sl3-hnn-central-dual-gap-vanishes
---

If the selected lattice tuple failed `(HMR1)` by a fixed amount along a
subsequence, `central-letter-averages-matrix-range-separators` would produce
uniformly operator-bounded normalized tuples `B_n` satisfying `(LCG2)` and
having separation gap at least half that amount.  This contradicts
`(LCG3)`.  Hence the distance to the full ucp matrix range tends to zero.

This route remains valid but is superseded quantitatively by
`hnn-central-dual-gap-is-equivalent-to-matrix-range-capture`: the explicit
choice `B_s=X_s/sqrt(|S|)` already has centrality defect inherited from the
HNN relators and gap at least the squared primal distance divided by
`2sqrt(|S|)`, so neither separation nor averaging is needed for this
implication.
