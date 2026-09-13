---
rg: 2
id: sft-tiling-module-dimensions-and-periods-must-diverge
kind: claim
title: For an infinite minimal Z^2 SFT, finite-dimensional tiling modules at scales D -> ∞ have diverging dimensions, and every period torus of a scale-D family has sup-diameter > 2D
distinct_from:
  periodic-quantum-tilings-refute-quantum-rigidity: that shows finite-dimensional tiling modules of aperiodic SFTs are noncommuting with no one-dimensional factor; this shows their dimensions and period tori must grow without bound with the scale.
  sfts-without-finite-orbits-are-not-residually-finite-actions: that excludes classical finite models of the action; this constrains operator-valued models quantitatively, through ranks and periods.
artifacts:
  - research/artifacts/un-labbe-ring-torus-tilings-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Ω ⊆ A^(Z^2)` be an infinite minimal SFT with forbidden patterns in `B_r` (sup
norm). Fields are arbitrary.

1. **Periods.** If `D >= r` and idempotents `E_a(z)` on a finite-dimensional `W != 0` satisfy (Q1)–(Q3) of
   `sft-crossed-product-fp-iff-quantum-rigid` at scale `D`, with `E_a(z + λ) = E_a(z)` for all `λ` in a
   finite-index `Λ`, then `Z^2/Λ` has sup-diameter `> 2D`.
2. **Dimensions.** If `D_j -> ∞` and `V_j != 0` are finite-dimensional modules of the local presentations
   `A_(D_j)(Ω, k_j)`, then `dim V_j -> ∞`.

**Mechanism** (artifact, §3).
- **Periods.** A small torus makes every pair of sites commute, and a common eigenvector reads off a legal periodic
  configuration.
- **Dimensions.**
  - Normalized ranks of pattern idempotents are translation-invariant, consistent and supported on the language.
    They take values in `(1/dim V_j) Z`.
  - A limit along a subsequence of bounded dimension is an invariant probability measure on `Ω`. It has full support
    and no atoms, so it gives some cylinder a weight strictly between `0` and `1/N`, which a bounded denominator
    cannot produce.

**Consequence for Labbé's shift.** Witnesses of `labbe-wang-shift-crossed-product-is-exactly-matricial`, or of
`labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`, need unbounded dimension and period tori of
sup-diameter `> 2D`. No fixed dimension, algebra or torus works at all large scales.

**Model test.**
- For an infinite minimal `Z`-subshift, a periodic point of period `p` of a Markov approximation at scale `D` is a
  one-dimensional *torus* module. As a module of the local presentation, which has translation operators, it induces
  the cyclic shift on `k^p`. Periods, and so these dimensions, grow with `D`, consistent with both items.
- A one-dimensional covariant module has scalar translations, so all its tile idempotents coincide and it reads off a
  constant configuration. Such modules exist only for SFTs with a fixed point.

Route: `sft-tiling-module-dimensions-and-periods-must-diverge-proof`.

**Definition (added at review).** The *sup-diameter* of `Z^2/Λ` is `max_(t ∈ Z^2/Λ) min { |w|_∞ : w ∈ t }`.

**Credit (review).** Item 1 is a quantitative form of item 1 of `periodic-quantum-tilings-refute-quantum-rigidity`: a small torus forces commutation, which that node forbids for aperiodic SFTs after induction to a covariant family.

**Model-test note (review).** The first model test concerns Markov approximations of infinite minimal `Z`-subshifts, which are not themselves SFTs. It is an analogue of the growth phenomenon, not an instance of the hypotheses.

**Review (un-verify-measure, 2026-09-13): PASS, with a display fix.** The common-eigenvector period bound and the rank-measure dimension argument re-derived; the missing definition of sup-diameter added. See `research/artifacts/un-review-measure-2026-09-13-part3.md` §L2.
