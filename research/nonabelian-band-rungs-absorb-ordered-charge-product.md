---
rg: 2
id: nonabelian-band-rungs-absorb-ordered-charge-product
kind: claim
title: For any fibre group, charges within one step of an essential band of m faces cancel by m plus |Q \ B| edge changes, while no change supported in a disk can alter the ordered charge product
distinct_from:
  torus-dipole-covers-rank-distance-linear-in-profile: that cancels abelian seam charges along a spanning tree of the band, which needs the ordered product of the charges to be trivial; this closes the band with all m rungs, which works for every fibre group, and proves that the tree (disk-supported) version is impossible whenever the ordered product is nontrivial.
  centralizer-rounding-cannot-bound-rank-distance-by-profile: that kills one-sided rounding with a kept word; this is a two-sided local surgery on a band of the shortest direction, which that obstruction does not cover.
  torus-abelian-covers-rectangle-profile-near-commute: that uses Stokes (charges sum to 0) on each band; the non-abelian replacement of Stokes is the flat-annulus argument here.
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement; this answers the non-abelian band-cancellation step recorded in its Attempts.
artifacts:
  - research/nonabelian-band-rungs-absorb-ordered-charge-product-proof.md
  - experiments/nonabelian-rectangle-profile-2026-09-17/rungs.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/rungs-summary.txt
---

**ESTABLISHED (unreviewed)** (`nonabelian-band-rungs-absorb-ordered-charge-product-proof`). Elementary topology of
flat bundles on a grid torus. It answers the step "can the ordered charge product around a band be made trivial on
`S_3`, `Q_8`, `A_4` fibres with `O(lambda_1)` changes": it cannot be made trivial by any local change, but it
does not need to be. One essential band of rungs absorbs it, for every fibre group, and the cost `lambda_1` is
forced.

**Setting.** `T = Z^2/Lambda'` is a grid torus and `F` is any group. A connection gives each edge
`x -> x+e1` a value `beta(x)` in `F` and each edge `x -> x+e2` a value `gamma(x)`. The face at `x` has holonomy
`hol(x) = gamma(x)^-1 beta(x+e2)^-1 gamma(x+e1) beta(x)`. A face is *charged* if `hol(x) != 1`. For the permutation
pair `b(x,a) = (x+e1, beta(x) a)`, `c(x,a) = (x+e2, gamma(x) a)` on `T x F`, the pair commutes iff no face is
charged. Changing one edge value changes `b` or `c` on one fibre only, so the rank cost is at most `|F|`.

A **band** is a cyclic sequence of distinct faces `f_0, ..., f_(m-1)` together with distinct edges `e_i`, where
`e_i` is a side of both `f_i` and `f_(i+1)` (indices mod `m`), and the dual closed curve through the `f_i` and
the `e_i` is homotopic to a primitive vector of `Lambda'`. The `e_i` are its *rungs*. The digital band
`{sigma <= det(v,.) < sigma + |v|_1}` of `torus-dipole-covers-rank-distance-linear-in-profile-proof`
(Lemma 3) is a band with `m = lambda_1`.

**Theorem 1 (rung lemma).** Suppose every charged face lies in a band `B`. Then some choice of values on the
`m` rungs makes every face flat. All other edges keep their values.

**Corollary.** Suppose every charged face lies in `B` or shares an edge with a face of `B`. Then the connection
can be made flat by changing at most `m + |Q \ B|` edges.

**Theorem 2 (disk supports cannot cancel a nontrivial product).** Let a flat connection agree with the given one
off an edge set `S`. Let `K` be a connected component of the dual graph `Gamma`: its vertices are the charged
faces and the faces with a side in `S`, and its edges are the edges of `S`, each joining the two faces it borders.
- **Inessential components.** Suppose every closed walk in `K` has class 0 in `Lambda'`. Then `K` lifts to `R^2`.
  Filling the holes of the lift gives a closed disk `D`, where:
  - `∂D` avoids the lifted `S`;
  - `D` contains no second lift of any face of `K`;
  - `hol(∂D) = 1`, so the ordered (van Kampen) product of the charges in `D` is trivial.
- **Few changes.** If `|S| < lambda_1(Lambda')`, every component is inessential. So fewer than `lambda_1` changes
  can only cancel charges in disk clusters whose ordered product is 1.
- **A single charge.** For a single charged face, every cancellation changes at least `lambda_1` edges, and
  Theorem 1 achieves exactly `lambda_1`.

**Why this answers the band step.** In each piece of the abelian strip cut, the tree cancellation keeps one rung of
the band. The dual support of the tree lies in a disk, so by Theorem 2 it works iff the ordered product of the piece's
charges is trivial. In the non-abelian case that product is a commutator of the piece's global holonomies, which is
generally nontrivial and cannot be changed locally. Changing the last rung as well turns the disk into an annulus.
The complement of the band is then a flat annulus. Its two boundary holonomies are conjugate, and that is exactly
what is needed to close the band (Theorem 1). The added cost is one edge per piece.

**Computation** (`rungs.py`, `rungs-summary.txt`). 6900 regular covers with fibre `S_3`, `Q_8` or `A_4` and at
most two charged faces, on random HNF tori (`N <= 24`) and on thin tori (`N <= 48`). They include 5056 closed bands.
- **Tree-only fails.** On 3641 of those bands the tree-only cancellation fails, that is, the ordered product is
  nontrivial. It fails on every single-charge cover.
- **The rung lemma holds.** On every band some closing value exists.
- **Outcome.** In every case the final pair commutes and the change count is within the stated bound.

## Attempts
