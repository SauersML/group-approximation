---
rg: 2
id: titz-witzel-residual-is-mf
kind: claim
title: Some Titz Mite--Witzel simple Kazhdan residual is operator MF
distinct_from:
  titz-witzel-exact-kazhdan-mf-radical-over-z: that needs a residual K that is not MF, since Rad_MF(K x Z) is K or trivial according as K is not MF or MF; this asserts the MF alternative for some residual, which would make that residual hyperlinear.
  simple-kazhdan-groups-have-full-mf-radical: that was the general non-MF assertion for infinite simple Kazhdan groups, now refuted by an LEF group; this is the MF question for the finitely presented residuals, where LEF is impossible and the question is open.
  kazhdan-mf-hyperlinear-fragment: that proves simple Kazhdan MF groups are hyperlinear; this is the premise that fragment would need for a finitely presented group.
---

**OPEN.** Some Titz Mite--Witzel residual `K` embeds in the unitary group of
`prod_n M_(k_n)(C) / directSum_n M_(k_n)(C)`. Equivalently, there are unitary matrices on the
generators whose relator defects tend to zero in operator norm while every nonidentity word stays
a fixed operator-norm distance from `1`.

If true, `K` is hyperlinear and answers `hyperlinear-fp-infinite-simple-kazhdan-group`
(`hyperlinear-fp-kazhdan-via-mf-titz-witzel`). If false for
all five residuals, `titz-witzel-exact-kazhdan-mf-radical-over-z` holds.

## Attempts

- **Exact local models.** Dead. A unitary model exact on the relators is a genuine
  finite-dimensional representation of `K`. Its image is a finitely generated linear group, hence
  residually finite (Malcev), hence trivial because `K` is infinite and simple. So every MF model
  has nonzero relator defect.
- **Permutation models with sparse defects.** Useless here. A permutation that is wrong on even
  one point has operator-norm defect at least `sqrt 2`, so sofic approximations never produce
  MF models.
- **Projective representations with small cocycle.** Dead. A finite-dimensional projective
  unitary representation of `K` has image in `PU(n)`, which embeds in `GL_(n^2)(C)`. So the image
  is residually finite and trivial, and the representation is scalar. The standard
  clock-and-shift construction of almost-commuting models has no analogue.
- **Spectral shape of any model (necessary condition).** Ozawa's characterization of (T),
  quoted as Theorem 4.17 of arXiv:2509.05054v2 and read there on 2026-09-13, writes
  `Delta^2 - eps Delta` as a sum of hermitian squares in `R[K]`. Titz Mite--Witzel (Section 4.6)
  compute such a certificate for `barGamma_1^2` on the generators of their Proposition 4.3, with
  Kazhdan radius at most 2 and Kazhdan constant at least 0.4147. Lifting to the free group adds a finite combination of relator
  terms. So along a model with relator defect `delta`, the Laplacian has spectrum in
  `[0, O(delta)] cup [eps - O(delta), infinity)`.
  - The almost-invariant spectral projection almost commutes with the generators.
  - Every separation happens on the gapped complement.

  This forces shape; it does not construct models.
- **Almost flat K-theory.** This would suffice. For a simple group, a sequence of
  quasi-representations with nonzero index pairing already gives MF. If the induced homomorphism
  into the corona unitary group were trivial, the generators would be norm-close to `1`, and a
  homotopy through quasi-representations of small defect would kill the pairing. So it is
  nontrivial, hence injective by simplicity.
  - There is room for such classes.
    - **Verified 2026-09-13 from the arXiv:2509.05054v2 PDF (Figures 4 and 5).** `Y_1^2` has
      45 triangles `t_1,...,t_45` and 45 edges (`e_1..e_15`, `f_1..f_15`, `g_1..g_15`). It has
      7 vertices: `v` and `w`, whose links have 30 vertices and 45 edges, and `u_1,...,u_5`,
      whose links are `K_(3,3)`.
    - So `chi(Y_1^2) = 7 - 45 + 45 = 7`. This matches the count `7F/45` from thickness three.
    - `K = Gamma_1^2` is simple, hence perfect, and aspherical of dimension two. So
      `dim_Q H^2(K;Q) = chi - 1 = 6` and `b_2^(2)(K) = 7`. The same gives a second proof that
      `C*(K)` fails the LP: Ioana--Spaas--Wiersma Corollary E needs only `H^2(K;R) != 0`.
  - **Where it stops.** Every known construction of finite-dimensional almost flat bundles
    realizing a degree-two class uses finite covers of large injectivity radius. `K` has none.
