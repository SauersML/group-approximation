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
* **Robustness of the published proof: does not transfer literally.**  The
  journal version [Rad20] (Canad. J. Math. 72 (2020)) was not read.  Its
  arXiv v1 (1712.01091v1, pp. 40--42, Proposition 5.1, the analogous result
  for the `(4,4)`-group `Gamma_(4,4)`) runs as follows.
  * Caprace's inclusion `[C_G(H), overline(H)] <= G^(infinity)`, with
    `overline(H)` the profinite closure, reduces the problem to putting a
    power of a generator in the profinite closure of a vertex-fixator subgroup.
  * That membership is proved one finite quotient `phi` at a time.
    Irreducibility makes the projection of `Fix(B(v,1)) cap B^(2) cap ker phi`
    infinite.  This produces an element of `ker phi` fixing a path but moving
    a neighbour, and the geometric squares turn it into `phi(gamma') = phi(x^2)`.
  * The argument ends by combining two quotients into their product.

  Every step uses the kernel of an exact homomorphism: a finite-index
  subgroup whose projection is infinite, and exact membership in images.
  Almost actions have no kernel, so this proof yields no metric inequality.
  A proof of this claim needs a different mechanism, for instance a
  quantitative replacement for "infinite projection of a finite-index
  subgroup".
