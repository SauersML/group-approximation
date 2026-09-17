---
rg: 2
id: quasiconvex-hierarchy-piece-nonsingular-extremes-sofic
kind: claim
title: A one-relator group is sofic when its top Magnus step has nonsingular extremes and its piece has a quasi-convex one-relator hierarchy
distinct_from:
  nonsingular-magnus-extremes-separable-piece-sofic: that assumes residual finiteness of the piece and profinite closedness of both Magnus subgroups; this verifies those hypotheses from the geometry of the piece's one-relator hierarchy, so the hypothesis becomes one about hierarchies and no longer about finite quotients.
  linton-z-stable-one-relator-hierarchy-theorem: that makes a one-relator group with a quasi-convex hierarchy at every level hyperbolic and virtually special; this asks for quasi-convexity only below the top level, allows the top splitting to be non-Z-stable or to create Baumslag--Solitar subgroups, and concludes only soficity.
  no-magnus-envelope-one-relator-groups-sofic: that is the open rigid remainder, whose model case is a hyperbolic virtually special piece with quasi-convex Magnus subgroups; this closes that model case whenever both extremes have nonzero exponent sum.
  length15-16-free-piece-residue-classes-hyperbolic-special: that certifies explicit finite lists of relators by a computation; this is a theorem about all relator lengths and makes no hyperbolicity claim about the group itself.
---

ESTABLISHED (written proof, unreviewed). Proof:
[[quasiconvex-hierarchy-piece-nonsingular-extremes-sofic-proof]].

**Setting.** `G = <a,t | w>`, `t` of exponent sum zero in `w`,
`a_i = t^(-i) a t^i`, a cyclic permutation of `w` rewritten as
`W_0(a_0,...,a_n)` with `n >= 1` and both `a_0`, `a_n` occurring. The piece is
`B_0 = <a_0,...,a_n | W_0>` and `F_- = <a_0,...,a_(n-1)>`,
`F_+ = <a_1,...,a_n>` are its Magnus subgroups. `eps_0`, `eps_n` are the
exponent sums of `a_0`, `a_n` in `W_0`.

**Theorem.** Suppose:

* **(N)** `eps_0 != 0` and `eps_n != 0`;
* **(QC)** the presentation complex `X` of `B_0` has a one-relator hierarchy
  `X_N -> ... -> X_1 -> X_0 = X` that is Z-stable, and `B_0` contains no
  Baumslag--Solitar subgroup. By Linton's Theorem 7.1 this is the same as: the
  hierarchy is quasi-convex and `B_0` is hyperbolic.

Then `G` is sofic.

**Special case (negative immersions).** If `X` has negative immersions
(Louder--Wilton; for a one-relator complex this is primitivity rank
`pi(W_0) >= 3` in `F(a_0,...,a_n)`), then every one-relator hierarchy of `X`
is quasi-convex and `B_0` is hyperbolic (Linton, Theorem 7.2), so (QC) holds.
Together with the free-piece case of
[[nonsingular-magnus-extremes-separable-piece-sofic]], the only pieces not
covered have primitivity rank exactly `2` or a non-quasi-convex hierarchy.

## Proof in one paragraph

Linton's Theorem 7.1 (Moreover clause), read at source, gives that `B_0` is
virtually special and that the image of `pi_1(A)` is quasi-convex for every
connected subcomplex `A` of `X`. The roses on `a_0..a_(n-1)` and on
`a_1..a_n` are such subcomplexes, so `F_-` and `F_+` are quasi-convex. The
virtual specialness comes from Wise's Theorem 13.3, which gives a finite-index
subgroup that is the fundamental group of a compact special cube complex. So
`B_0` is linear over `Z`, hence residually finite. By Haglund--Wise, quasi-convex
subgroups of hyperbolic compact special groups are separable, and separability
passes to finite-index overgroups. That is hypothesis (S) of
[[nonsingular-magnus-extremes-separable-piece-sofic]], and (N) is shared.

## What this reaches, and what it does not

* **Closes the model case of the rigid remainder under (N).** Attempt 2 of
  [[no-magnus-envelope-one-relator-groups-sofic]] records that for
  hyperbolic virtually special pieces with quasi-convex, hence separable, Magnus
  subgroups, residual finiteness of the gluing needs compatible finite quotients
  of the previous window, and no permanence theorem supplies them. The shift
  dictionary does not glue finite quotients. It extends one finite quotient of
  `B_0` along the shift through a growing locally finite alphabet, so no
  compatibility with other windows is needed.
* **No claim about `G` itself.** `G` may contain Baumslag--Solitar subgroups,
  the top splitting may fail to be Z-stable, and `G` need not be residually
  finite. We have not checked the literature for whether every group in this
  class is already known to be residually finite or linear.
* **Where it stops.**
  - A singular extreme (`eps_0 = 0` or `eps_n = 0`) is the exact break of the
    torsion-alphabet dictionary; see section 9 of
    [[nonsingular-magnus-extremes-separable-piece-sofic-proof]].
  - A piece that is not residually finite with separable Magnus subgroups is
    out of reach of *any* locally finite alphabet. A separation
    `rho(b) not in D` is witnessed on finitely many coordinates, and the image
    of `B_0` there is a finite group. So the dictionary would produce exactly
    the finite quotients that (S) asks for. The induction therefore cannot be
    run one level down: a piece that is sofic but not residually finite, such
    as `BS(2,3)` or any output of this theorem, is not an admissible piece.
