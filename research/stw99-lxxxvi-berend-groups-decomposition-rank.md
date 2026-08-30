---
rg: 2
id: stw99-lxxxvi-berend-groups-decomposition-rank
kind: claim
title: The strongly quasidiagonal Berend groups Z^3 x| Z^2 have infinite decomposition rank
root: true
distinct_from:
  berend-torus-actions-give-strongly-qd-polycyclic-groups: that is the established literature fact that these groups are strongly quasidiagonal; this is the open assertion that their group C*-algebras nevertheless have infinite decomposition rank, a concrete case of Eckhardt--Wu Conjecture II.
  stw99-eckhardt-wu-decomposition-rank-conjecture: that quantifies over all finitely generated elementary amenable groups; this is one specific unresolved instance where the strong-quasidiagonality obstruction is provably silent.
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Let `G = Z^3 ⋊ Z^2` be a Berend-type group
(`berend-torus-actions-give-strongly-qd-polycyclic-groups`).  Then
`dr(C*(G)) = ∞`.

This is a concrete open subproblem of STW Problem LXXXVI (Eckhardt--Wu
Conjecture II): `G` is finitely generated, elementary amenable (polycyclic),
not virtually nilpotent, so Conjecture II predicts infinite decomposition
rank.  It is linked to the numbered STW root by
`stw99-lxxxvi-berend-case-from-conjecture`.  The `root: true` marker here
means that Cairn tracks this as a standalone program target; it does not
mean that STW states it as a separate numbered problem.  Without that
marker the open parent conjecture cannot supply a live graph path to this
open consequence.

Two immediate necessary conditions for finite decomposition rank do not
decide this case.  First, Kirchberg--Winter, Theorem 5.3, says finite
decomposition rank implies strong quasidiagonality, and Eckhardt proved
that `C*(G)` is strongly quasidiagonal.  More precisely, Eckhardt's Lemma
2.2 shows that any representation faithful on `C*(Z^3)` is faithful on
`C*(G)`, while the image of a representation not faithful there is
subhomogeneous.  Thus every proper quotient is subhomogeneous; this does
not assert that every quotient is a single algebra
`M_{|O|}(C(T^2))`.  Second, finite nuclear dimension holds by
Eckhardt--Wu, Theorem 5.4, since `G` is polycyclic (of Hirsch length five).
Their theorem supplies a recursive bound depending on Hirsch length, not
the numerical bound `53` occurring for a different example in their
Section 5.2.  Decomposition rank is not known to pass to arbitrary
subalgebras, so the non-strongly-QD subgroups `Z^3 ⋊ Z` do not settle
the ambient group.  There is nevertheless a sharp quotient reduction:
`berend-proper-quotients-have-decomposition-rank-at-most-two` proves that
every proper quotient has decomposition rank at most two.  Any infinite
decomposition rank must therefore be an essential phenomenon in the full
crossed product, not one detected by a quotient.

## Attempts

* **Strong quasidiagonality.**  This necessary condition is exhausted for
  this example: every representation is quasidiagonal.  This statement,
  unlike a classification of every quotient or trace, is exactly what
  Eckhardt's Lemma 2.2 proves.
* **Proper quotients.**  The finite-orbit reduction does more than give
  quasidiagonality: every proper quotient has decomposition rank at most
  two.  Quotient monotonicity therefore cannot prove the desired infinite
  lower bound.  Moreover,
  `berend-finite-orbit-quotients-are-asymptotically-isometric` arranges
  these quotients into a sequence which norms every element of the full
  algebra.  This still does not give a decomposition-rank upper bound:
  dense finite restrictions give the same phenomenon with
  zero-dimensional targets for commutative algebras of arbitrary covering
  dimension.
* **Primitive spectrum.**
  `berend-primitive-spectrum-has-one-faithful-generic-point` identifies the
  only non-closed primitive point as the faithful zero kernel; every other
  primitive quotient is a matrix algebra and lies on a closed two-torus
  stratum.  Thus a primitive-space obstruction would have to measure the
  accumulation of all finite-orbit strata at that generic point, rather
  than the dimension or representation theory of any one stratum.
  `berend-locally-closed-primitive-dimension-is-two` makes this sharp:
  every locally closed Hausdorff primitive subspace has dimension at most
  two, and orbit tori attain two.  Hence the usual Hausdorff-stratum
  dimension is finite and cannot force infinite decomposition rank.
* **Entropy (speculative).**  Every nonidentity element of the torsion-free
  unit subgroup has positive entropy: an infinite-order algebraic unit
  cannot have all conjugates on the unit circle, and the entropy of its
  toral automorphism is the sum of the logarithms of the expanding
  eigenvalue moduli.  The unrestricted implication from finite
  decomposition rank to zero entropy is false:
  `minimal-cantor-crossed-products-have-decomposition-rank-one` gives
  free minimal uniquely ergodic positive-entropy systems whose crossed
  products have decomposition rank one.  Thus an entropy theorem capable
  of settling the Berend instance would have to use its rank-two algebraic
  action or its nonminimal finite-orbit structure, not merely positivity
  of the entropy of an acting automorphism.  Finite nuclear dimension
  cannot provide such a distinction, because Eckhardt--Wu already prove
  finite nuclear dimension here.
* **Positive direction (refuting Conjecture II).**  A finite decomposition
  rank bound would require additional control beyond the finite-nuclear-
  dimension theorem.  Finite invariant torsion sets give the
  quasidiagonal representations used in the established argument, but no
  cited result upgrades these approximations to bounded-colour,
  contractive order-zero approximations inside `A`.  The quotient models
  are already asymptotically isometric, so improving norm separation is
  not the issue.  The exact unresolved step is to lift their coloured
  approximations back to `A` with order zero on each colour and a
  contractive total sum; claims about shrinking multiplicative domains
  are only heuristic and are not used as established input.
