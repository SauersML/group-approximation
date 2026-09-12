---
rg: 2
id: sp21-lattice-few-alternating-and-large-rank-quotients
kind: claim
title: Some cocompact arithmetic Sp(2,1) lattice has only finitely many alternating and large-rank simple quotients
distinct_from:
  sp21-lattice-has-congruence-subgroup-property: that asks for a finite congruence kernel, which controls every finite quotient; this constrains only simple quotients that are alternating or of Lie rank above a bound, is implied by it, and is not known to imply it
  sp21-bounded-rank-simple-quotients-almost-all-congruence: that is the established theorem that bounded-rank simple quotients are almost all congruence; this is the open assertion about the complementary families, alternating groups and unbounded rank
  sp21-lattice-hyperbolic-quotient-without-finite-quotients: that asks directly for a finite-quotient-free hyperbolic quotient; this is a hypothesis on the finite simple images of the lattice that produces one
---

Let `Γ` be a torsion-free cocompact arithmetic lattice in `Sp(2,1)`, set up as in
`sp21-bounded-rank-simple-quotients-almost-all-congruence`. Assert that for
some `r >= 1`, only finitely many normal subgroups `N ⊴ Γ` have `Γ/N`
isomorphic to either:
- an alternating group; or
- a finite simple group of Lie type of Lie rank `> r`.

**Equivalent form.** By `sp21-bounded-rank-simple-quotients-almost-all-congruence`,
the assertion is equivalent to: `Γ` has only finitely many **non-congruence**
finite simple quotients.
- Congruence simple quotients are `Sp_6(F_q)/Z` of rank `3`, plus finitely many
  at bad primes.
- There are only finitely many sporadic images.

**Payoff.** Route `quotientless-hyperbolic-via-sp21-simple-quotient-bound`
turns the assertion into an infinite hyperbolic group without finite
quotients. So a positive answer to Gromov's question forces **every** such
lattice to surject onto infinitely many alternating groups, or onto simple
groups of unbounded Lie rank.

## Attempts

- **From the congruence subgroup property.**
  `sp21-simple-quotient-bound-from-congruence-property` derives this claim.
  That route is only as strong as the open property itself.
- **Where the difficulty sits.** Both families are invisible to superrigidity.
  An ultraproduct of alternating quotients, or of quotients of unbounded rank,
  is a metric approximation (Hamming, or normalized rank), not a linear
  representation. So `sp21-lattice-positive-characteristic-images-finite` and
  the Galois-conjugate step have no purchase on them.
- **Omnipotence calibration.** Suppose every hyperbolic group is residually finite.
  Then every independent pair `g, h` of `Γ` is omnipotent in Wise's sense:
  - by `hyperbolic-group-relative-to-maximal-elementary-subgroup`, `Γ` is
    hyperbolic relative to `{E(g), E(h)}`;
  - by `relatively-hyperbolic-dehn-filling`, deep fillings `<g^(Kn_1)>, <h^(Kn_2)>`
    are hyperbolic and keep both orders exact;
  - residual finiteness of the filling then detects those orders.

  Compare Sisto's Theorem 2.8 in Wilton, arXiv:2410.00556, for mapping class
  groups. No quotient that factors through the congruence completion `Γ̄`
  realizes this:
  - if `ord(g) = K`, the quotient kills `closure(<<g^K>>)`, which is open by
    `normal-subgroups-of-arithmetic-lattices-are-congruence-open`;
  - so the order of `h` there is bounded independently of `n_2`.

  So under universal residual finiteness, omnipotence of `Γ` lives entirely in
  non-congruence finite quotients of the fillings `Γ/<<g^K>>`.
- **(T) and hyperbolicity are not enough.**
  `caprace-kassabov-hyperbolic-kazhdan-alternating-quotients` gives explicit
  hyperbolic Kazhdan groups that surject onto infinitely many alternating groups.
  Any proof of this claim has to use arithmeticity, not only property (T) and
  hyperbolicity.
- **A weaker hypothesis suffices.** `sp21-noncongruence-simple-kernels-separate-points`
  asks only that each nontrivial element lie in finitely many kernels of
  alternating or large-rank simple quotients. This claim implies it, and route
  `quotientless-hyperbolic-via-sp21-noncongruence-separation` gets a hyperbolic
  group without finite quotients from it. That route replaces the
  congruence-density step with one preliminary Olshanskii quotient.
- **Torsion-freeness is not enough either.**
  `tf-kazhdan-hyperbolic-alternating-kernels-not-separating` gives a torsion-free
  hyperbolic Kazhdan group with infinitely many alternating quotients whose
  kernels share an infinite normal subgroup. The fence therefore covers
  torsion-free groups and the separation form as well.
- **Transferring the only known mechanism.** Every known alternating family of a
  hyperbolic Kazhdan group comes from a polynomial transvection group
  `G_(F_p,e) <= Aut(F_p[x_1..x_n])` with `max e_i >= 2`, acting on affine spaces
  over finite fields (Caprace–Kassabov, arXiv:2210.00730v3, Theorem 1.2 and
  Corollary 1.3).
  - **What a surjection would give.** A surjection `Γ ->> G_(F_p,e)` would give
    `Γ` infinitely many alternating quotients, so this claim would fail.
    Contrapositively to `sp21-simple-quotient-bound-from-congruence-property`,
    the congruence kernel of `Γ` would be infinite.
  - **Necessary condition.** `G_(F_p,e)` is residually-p (their Proposition 7.2)
    and contains elementary abelian p-groups of infinite rank (their
    Corollary 6.3). So its pro-p completion has infinite rank, and such a
    surjection needs the pro-p completion of `Γ` to have infinite rank, i.e. to
    be not p-adic analytic. The congruence pro-p images of `Γ` are analytic, so
    this needs non-congruence p-quotients. Whether the pro-p completion of a
    cocompact arithmetic `Sp(2,1)` lattice has finite rank is not recorded here.
  - **Status.** No homomorphism from such a lattice onto a transvection group is
    known or attempted.
- **Random relators.** `random-relators-kill-small-simple-quotients-of-kazhdan-groups`
  kills the alternating quotients of order at most `λ^(-L)`. The large ones
  survive exactly when their kernels contain every relator.
- **Status boundary.** No source deciding whether a cocompact `Sp(n,1)`
  lattice has infinitely many alternating quotients was found. lit-scout-2 ran a
  bounded 2025–26 search on 2026-09-12. No construction of such quotients is
  recorded here.
