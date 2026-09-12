---
rg: 2
id: radu-commutator-collapse
kind: claim
title: Along every almost action of Radu's BMW lattice the commutator [y(xz)^2y, xz] vanishes asymptotically
distinct_from:
  radu-mark-is-controlled-by-one-commutator: that proves collapse of this commutator forces collapse of the mark; this asserts the collapse itself, the robust form of Radu's Proposition 5.4.
  radu-bmw-lattice-nonsofic: that is nonsoficity of the lattice; this is a stronger and more specific statement about one commutator in every almost action.
artifacts:
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
---

**OPEN.**  Let `(a_n,b_n,c_n,x_n,y_n,z_n)` be involutions on finite sets such
that the normalized Hamming defects of `axax, ayay, azbz, bxbx, bycy, cxcz`
tend to zero.  The claim is that

```text
d_H([y_n (x_n z_n)^2 y_n, x_n z_n], 1) -> 0.
```

For exact finite quotients this is Titz Mite--Witzel Proposition 3.4(4),
citing [Rad20, Proposition 5.4].  With `radu-mark-is-controlled-by-one-commutator`
it forces `(xz)^4` into the sofic radical, hence `radu-bmw-lattice-nonsofic`
and, through the embedding, `titz-witzel-kernel-nonsofic`.  The commutator
lies in the free normal subgroup acting trivially on the horizontal tree
(`radu-horizontal-projection-kills-delta-squared`), so no information about
the horizontal quotient can decide it.

## Attempts

* **Exact case.**  True, by Proposition 3.4(4) together with the exact
  equivalence of its two alternatives
  (`radu-mark-is-controlled-by-one-commutator`, `(RL2)` at zero defect).
* **Robustness of the published proof.**  Unread.  Proposition 3.4(3), that
  `xz` lies in the profinite closure of `<a,b,c>`, is a statement about finite
  quotients and has no direct metric analogue.  The next step is to read
  [Rad20, Section 5] and locate where finiteness of the quotient is used.
