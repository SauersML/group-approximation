---
rg: 2
id: flip-codings-remove-the-sign-obstruction-for-iet-groups
kind: claim
title: Every real number field is Q(β) for a Pisot unit β with the negative finiteness property, so orientation-reversing (negative-base) codings face no sign obstruction; with the negative-base RSG theorem this gives Boone--Higman for every interval exchange group with algebraic parameters
distinct_from:
  f-unit-fields-are-characterized-by-isolated-sign-units: that shows positive-base (F) codings reach exactly the fields with an isolated-sign unit, excluding Q(√3); this shows the obstruction is an orientation artifact, since negative-base finiteness is available in every real field.
  pisot-stein-groups-are-contracting-rsgs: that is the positive-base RSG theorem; its negative-base analogue, the former open step here, is `negative-base-pisot-stein-groups-are-contracting-rsgs`.
  algebraic-interval-exchange-groups-satisfy-boone-higman: that is the payoff, proved.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (lane proofs, not reviewed). Items 1–3 are proved here. Item 4, the former open step, is proved in
`negative-base-pisot-stein-groups-are-contracting-rsgs`; the payoff is
`algebraic-interval-exchange-groups-satisfy-boone-higman`. Their inputs were read at source:
- Krčmáriková--Steiner--Vávra (arXiv:1701.04609, TeX in `gq/src/bh-near-actions/neg/`): Theorem `t:dominant` and
  the introduction's statement of the MPV necessary condition;
- Masáková--Pelantová--Vávra (arXiv:1002.1009): the Ito--Sadahiro admissibility theorem and the expansions
  `d_{−β}(ℓ_β)`.

## Items

1. **Every real field has a dominant totally positive Pisot unit.** For every real number field `K`, every `δ > 0`
   and every `φ > 0`, there is a unit `β > 1` with `Q(β) = K` such that every other conjugate `z` has `|z| ≤ δ` and
   `|arg z| ≤ φ`. In particular the real conjugates are positive.
   - **Unit.** By Dirichlet, choose a unit `u` with `|u_v| < 1` at every place `v ≠ v_0`. Choose it so that no power
     of `u` lies in a proper subfield. There are finitely many proper subfields, each with a unit lattice of lower
     rank, and a generic lattice point avoids them all.
   - **Arguments.** By Dirichlet's simultaneous approximation theorem, some `N ≥ 1` has `N·arg(u_v²)` within `φ` of
     0 (mod 2π) at every complex place `v`. This is homogeneous approximation, so it needs no independence
     hypothesis.
   - **Conclusion.** `β = u^{2N}`, with `N` large, has the stated conjugate configuration. Its conjugates are
     distinct, since no power of `u` lies in a proper subfield. So `Q(β) = K`.
2. **Such β have Ito--Sadahiro's (−F).** Write the minimal polynomial as `(x − β)∏(x − z_j)` and put
   `e_k = e_k(z) > 0`. These are positive reals because the `z_j` lie in a narrow sector around the positive axis.
   - Then `p(x) = x^d − a_1x^{d−1} + a_2x^{d−2} − … + (−1)^d a_d`, with `a_1 = β + e_1`,
     `a_k = βe_{k−1} + e_k` for `2 ≤ k ≤ d−1`, and `a_d = βe_{d−1} = N(β) = 1`.
   - For `Σ e_k ≤ 1/4` and `β ≥ 5`: `a_1 − Σ_{k≥2} a_k ≥ β(1 − Σe_k) − Σe_k − 1 ≥ 2`. This is KSV's dominant
     condition, so `β` has (−F): `Fin(−β) = Z[β]`.
3. **No sign obstruction.**
   - **Positive base.** The obstruction there is a second positive real conjugate (Akiyama, Proposition 1). It
     forces the isolated-sign condition of `f-unit-fields-are-characterized-by-isolated-sign-units`.
   - **Negative base.** The corresponding obstruction is a negative real conjugate (MPV, as quoted in KSV). It
     forces only that the other real conjugates be positive, which item 1 provides in every field.
   - **Parity.** The relative norm `N_{Q(β)/K}(β)` is then totally positive, which imposes nothing.
4. **The negative-base RSG theorem (formerly open; now proved).** A contracting-RSG theorem is needed for piecewise maps
   `y ↦ ±β^k y + c` with `c ∈ Z[β]`, coded by a negative-base shift.
   - **Where the positive-base proof transfers.** Pisot lattice finiteness of offsets and the conjugate-growth
     length lemma transfer verbatim.
   - **Where it does not.** In Ito--Sadahiro's normalization on `[ℓ_β, ℓ_β+1)`, with `ℓ_β = −β/(β+1)`, the
     finite-expansion points (the (−F) set `Z[β]`) are *interior* points of cylinders. The fixed point `0` is
     interior, and the cylinder boundaries lie in the other coset `ℓ_β + Z[β]`.
     - One checks `−βℓ_β − ℓ_β = β`, so the transformation preserves that coset.
     - Translating by `−ℓ_β` turns it into `S(y) = {β(1−y)}` on `[0,1)`, whose boundary set is `∪ S^{−n}(orbit of 0)`
       inside `Z[β]`.
   - **What is needed.** The finiteness property matching the boundary coset: every `z ∈ Z[β] ∩ [0,1)` reaches `0`
     under `T'(y) = {−βy}`. KSV's (−F) is the corresponding statement for the other coset.
   - **Resolution (2026-09-18).** `T'` is conjugate to the classical SRS `τ_r` of the cofactor of `x + β`, and
     `0 < r_0 < … < r_{d−2} < 1` puts `r` in `D^0` by an explicit set of witnesses. The units of item 1 satisfy this,
     and so does every norm `+1` quadratic unit, including `2+√3` (where `r_0 = 2−√3`). See
     `algebraic-interval-exchange-groups-satisfy-boone-higman`, item 1.
   - **Payoff.** The proof of `pisot-stein-groups-are-contracting-rsgs` goes through with slopes `±β^k`
     (`negative-base-pisot-stein-groups-are-contracting-rsgs`). So every finitely generated interval exchange group
     with algebraic parameters lies in a finitely presented simple group.

## Lesson for general BH

The field restriction in arithmetic full-group hosts is an orientation artifact, not an arithmetic one.
- Orientation-preserving (positive-base) codings impose a parity condition on unit signs.
- Orientation-reversing codings impose only total positivity, which every real field satisfies.
- The finiteness engine is Pisot lattice compactness of the renormalized offsets, and it is universal over real
  algebraic data.

What remained was a digit-system finiteness statement, not a group-theoretic obstruction. It is an SRS condition
with a one-line set of witnesses, so the contracting-RSG route reaches every real algebraic interval exchange
group.
