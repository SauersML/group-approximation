---
rg: 2
id: integral-matrices-norm-below-2-019-serre-proof
kind: route
title: Grow a noncyclotomic ball inside an infinite component to nineteen vertices to contradict McKee--Smyth, then split off finite components with finite spectrum
target: integral-matrices-of-norm-below-2-019-obey-serre
requires:
  - small-spectral-radius-integer-matrices-classified
  - norm-two-integral-matrices-reduce-to-virtually-cyclic-groups
  - finite-spectrum-integral-elements-obey-determinant
artifacts:
  - research/artifacts/determinant-norm-room-2026-09-16.md
---

Full proof in the artifact, Section 4.

**1. Infinite components.** Let `C` be an infinite component and `S subset C`
finite and connected. The principal submatrix `M_S` of `r_A` is an
indecomposable integer symmetric matrix with `rho(M_S) <= ||r_A|| < 2.019`.

Suppose `rho(M_S) > 2`.
- Since `C` is infinite and connected, add neighbours to get a connected
  `S' supset S` with `|S'| >= 19`.
- By interlacing `rho(M_(S')) > 2`, and by compression `rho(M_(S')) < 2.019`.
- This contradicts `small-spectral-radius-integer-matrices-classified`: every
  noncyclotomic indecomposable example has at most `18` rows.

So `rho(M_S) <= 2` for all finite `S`. Every finitely supported vector lies in
such an `S`, hence `||r_A|_(l^2(C))|| <= 2`.

**2. Splitting.** Adjacent vertices lie in one component, and translates of a
component have the same cardinality. So entries of `A` vanish between finite
and infinite indices, and `r_A = r_(A_fin) (+) r_(A_inf)`.
- Components of `Gamma_(A_fin)` are finite and fall into finitely many
  `G`-orbits carrying identical finite matrices. So `r_(A_fin)` has finite
  spectrum.
- `||r_(A_inf)|| <= 2` by 1.

**3. Serre.**
- `finite-spectrum-integral-elements-obey-determinant` handles `A_fin`.
- `norm-two-integral-matrices-reduce-to-virtually-cyclic-groups` handles
  `A_inf`.
- Masses and Serre integrals add.

**4. Quantization.** `||r_A||` is the maximum of `||r_(A_inf)|| <= 2` and the
radii of finitely many finite component matrices. If `||r_A|| > 2`, it is the
radius of a noncyclotomic indecomposable integer symmetric matrix below
`2.019`. Apply the classification.
