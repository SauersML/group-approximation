---
rg: 2
id: semisimple-trace-charts-cannot-authenticate-proper-fullness
kind: claim
title: Fixed semisimple trace charts cannot authenticate proper source fullness only in matrices
artifacts:
  - research/artifacts/fanizza-finite-chart-trace-reflection-criterion-2026-08-21.md
distinct_from:
  local-steinberg-heisenberg-packets-are-coefficient-rank-blind: that varies an idempotent rank while preserving one characteristic-two D8 root packet; this classifies trace reflection for every fixed finite-dimensional characteristic-zero chart.
  hecke-dilations-do-not-lock-capacity-gram: that shows two concrete names fail to lock one capacity Gram; this gives the exact irreducible-sector criterion for any finite semisimple chart.
  carrier-not-decoder: that gives one finite UT4 packet countermodel without a classical decoder; this identifies the full multiplicity simplex and the exceptional constant-rank case.
  rectangular-wedderburn-block-isometry-gap: that derives a rank obstruction between two unequal regular Fourier blocks; this classifies when any one finite chart has a multiplicity-independent projection trace and isolates algebra-factor localization.
---

Let `A=direct_sum_j M_(d_j)(C)` and let `e in A` have sector ranks `r_j`.
In a finite-dimensional representation with irreducible multiplicities
`m_j`,

```text
tr(pi(e))=(sum_j m_j r_j)/(sum_j m_j d_j).
```

Thus a fixed finite chart reflects one representation-independent relative
rank `c` exactly when `r_j/d_j=c` in every simple sector.

If the chart fixes one faithful irreducible multiplicity profile up to
common amplification, every nonzero projection in its algebra coordinate
has trace at least one constant `gamma_A>0`.  Thus `tr(e-g)<gamma_A` forces
`g=e`, provided `e-g` has first been localized in that algebra coordinate.

In particular, if `g<=e` are projections and every finite-dimensional
representation of the chart has `tr(pi(g))=tr(pi(e))`, then `g=e` in every
simple sector and hence in `A`.  The alleged fullness is then an algebraic
chart equality inherited by infinite representations, not a finite-matrix
multiplicity effect.  Otherwise the multiplicity vector gives exact
finite-dimensional escapes with different reflected ranks.

Therefore a fixed two-idempotent overlap/Grassmannian chart, four-root
Steinberg square, or finite shared-selector extension supplies at most this
rank-quantization gap.  By semisimple trace reflection alone it cannot
authenticate that the Gram deficiency lies in the algebra factor rather
than the freely amplified multiplicity commutant.  That coordinate
localization, a matrix-dependent growing family, or a genuinely finite-only
non-semisimple multiplicity law remains necessary.
