---
rg: 2
id: titz-witzel-residual-is-mf
kind: claim
title: Some Titz Mite--Witzel simple Kazhdan residual is operator MF
distinct_from:
  titz-witzel-exact-kazhdan-mf-radical-over-z: that needs a residual K that is not MF, since Rad_MF(K x Z) is K or trivial according as K is not MF or MF; this asserts the MF alternative for some residual, which would make that residual hyperlinear.
  simple-kazhdan-groups-have-full-mf-radical: that was the general non-MF assertion for infinite simple Kazhdan groups, now refuted by an LEF group; this is the MF question for the finitely presented residuals, where LEF is impossible and the question is open.
  kazhdan-mf-hyperlinear-fragment: that proves simple Kazhdan MF groups are hyperlinear; this is the premise that fragment would need for a finitely presented group.
artifacts:
  - experiments/tw-mf-norm-census-2026-09-17/norm_census.py
  - experiments/tw-mf-norm-census-2026-09-17/verify_witnesses.py
  - experiments/tw-mf-norm-census-2026-09-17/census_run1_output.txt
  - experiments/tw-mf-norm-census-2026-09-17/verify_witnesses_output.txt
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
- **Operator-norm defect census, `k <= 16` (2026-09-18, heuristic only).** Dead as a way to
  tell MF from non-MF.
  - **Setup.** Use the two-generator presentation `(TW2G2)` of `barGamma` (relators `c^2`,
    `r0`, `r1`, `r2` of lengths 18, 84, 108, 104, rebuilt from the free-word-check artifact).
    Here `e = V diag(+-1) V^*` is an exact involution and `u = diag(e^(i theta))` has one frozen
    eigenvalue at `theta_0`. That gives `||u^8 - 1||_op >= |e^(8i theta_0) - 1| =: c`, and `u^8`
    separates, since `K` is simple and `K` MF iff `barGamma` MF. We minimise the maximum
    operator-norm relator defect `delta_c(k)` by batched Riemannian CG on `U(k) x T^(k-1)`,
    using a smoothed maximum `(1/2q) log sum tr(H^q)` with `q = 1, 4, 16, 64`. Gradients are
    checked by finite differences.
  - **Certified upper bounds (explicit double-precision tuples).** An independent
    letter-by-letter recheck is in `verify_witnesses_output.txt`, with involution and unitarity
    errors `<= 1e-13`.

    | `c` | `k = 1` | `k = 2` | `k = 3..16` |
    |---|---|---|---|
    | 2 | 2.000 | 1.2355 | 1.2355 (padded) |
    | 1.414 | 1.848 | 1.444 | 1.362 (`k = 3`), 1.272 (`k = 4..12`), 1.128 (`k = 16`) |
    | 0.765 | 1.191 | 0.650 | 0.6291 to 0.6293 |

    At `c = 0.765`, three relators equalise near 0.625, 0.627 and 0.629, and this recurs from
    independent random starts at every `k` from 3 to 16.
  - **What it shows.** `delta_c(k)` is non-increasing in `k`: pad with the exact trivial
    representation `(1,1)` or the sign representation `(-1,-1)` of `barGamma`. In dimensions up to
    16, local search never beats a 2- or 3-dimensional witness padded this way, and no decay in
    `k` is visible. The ratio `delta/c` stays around 0.6 to 0.8.
  - **Where it dies.** The optimiser is not global: the `k = 2`, `c = 2` value was 1.4139 in one
    run and 1.2355 in a wider run. There is no lower-bound mechanism: Tarski-type certificates
    are out of reach at `k >= 3`, and Kazhdan gives no operator-norm stability. By the
    gap-localisation node, any MF witness must separate `u^8` on the gapped complement of an
    almost-invariant projection, and nothing suggests that happens at `k <= 16`. So a plateau at
    small `k` is compatible with both alternatives and changes no belief. Upgrading this needs a
    structured ansatz with dimension growing in a controlled way, not a denser search.
