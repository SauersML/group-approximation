---
rg: 2
id: torus-quantum-tilings-decide-matriciality-of-sft-rings
kind: claim
title: Over a finite field, the crossed product of a free minimal Z^2 SFT is exactly matricial iff for every scale some finite torus carries a nonzero finite-dimensional module of the translation-free torus tiling algebra
distinct_from:
  matricial-z2-sft-crossed-products-give-quantum-tilings: that uses covariant families with translation operators over a fixed field; this removes the translations by induction from finite tori and pins the field to the ring's finite field.
  periodic-quantum-tilings-refute-quantum-rigidity: that identifies finite-dimensional modules of the local presentation with periodic families over finite fields; this adds the translation-free torus algebra and the exact matriciality equivalence.
  labbe-tiles-admit-periodic-quantum-tilings-at-every-scale: that asks for Labbé families over some field at each scale; this is the general characteristic-p torus form equivalent to exact matriciality of the F_q ring.
artifacts:
  - research/artifacts/un-labbe-ring-torus-tilings-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Ω ⊆ A^(Z^2)` be a free minimal SFT with forbidden patterns in `B_r` (sup norm),
`k` a finite field, and `R = LC(Ω,k) ⋊ Z^2`. For finite-index `Λ ≤ Z^2` and `D >= r`, let `𝒯_(D,Λ)(Ω,k)` be the
`k`-algebra on `e_a(t)` (`a ∈ A`, `t ∈ Z^2/Λ`) with:
- (T1) `sum_a e_a(t) = 1` and `e_a(t) e_b(t) = δ_ab e_a(t)`;
- (T2) `[e_a(t), e_b(t')] = 0` whenever `t' - t` has a representative in `B_(2D)`;
- (T3) `prod_(h ∈ B_D) e_(π(h))(t + h) = 0` for `π ∉ L_(B_D)(Ω)`.

Then `R` embeds unitally in an algebraic ultraproduct of matrix algebras over fields iff for every `D` there is
`Λ` such that `𝒯_(D,Λ)(Ω,k)` has a nonzero finite-dimensional module.

**Mechanism** (artifact, §2):
- A torus module `V` induces a covariant family on `⊕_(s ∈ Z^2/Λ) V`, with translations permuting summands.
- Covariant families over a finite field restrict to the torus of their period lattice.
- Any exact matricial model specializes to families in characteristic `p` over finite fields.

**Consequence.** Row 7 of the UN calibration table is exactly: do Labbé torus tiling algebras over `F_q` have
nonzero finite-dimensional modules at every scale?

Route: `torus-quantum-tilings-decide-matriciality-of-sft-rings-proof`.

**Review (un-verify-measure, 2026-09-13): PASS.** Induction, restriction, specialization (Łoś plus the Nullstellensatz over F_p) and the equivalence re-derived. Item 1 of `matricial-aperiodic-sft-rings-are-not-quantum-rigid` reviewed PASS as part of this; families-to-matricial is PASS (part 1 §M6). No conflict in the subsumption scan. See `research/artifacts/un-review-measure-2026-09-13-part3.md` §L1.
