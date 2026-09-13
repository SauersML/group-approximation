---
rg: 2
id: matricial-z2-sft-crossed-products-give-quantum-tilings
kind: claim
title: The crossed product of a free minimal Z^2 SFT is matricial exactly when its local tiling presentations have nonzero finite-dimensional covariant modules at every scale
distinct_from:
  periodic-quantum-tilings-refute-quantum-rigidity: that shows such modules are noncommuting for aperiodic SFTs; this identifies their existence at every scale with matricial embeddability of the crossed product.
  z2-sft-derived-full-group-lef-from-tiling-modules: that derives LEF of the derived full group from the same modules; this is the ring-level equivalence, via simplicity.
  lef-simple-rings-are-not-finitely-presented: that excludes finitely presented simple LEF rings; the rigid-SFT consequence here is consistent with it, by an independent route.
artifacts:
  - research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `Ω ⊆ A^(Z^2)` be a free minimal SFT with forbidden patterns in `B_r`,
`k` a field, and `R_Ω = LC(Ω,k) ⋊ Z^2`. For `D >= r`, a *covariant `D`-family* is:
- a nonzero `k`-space `W`;
- commuting invertibles `U_1, U_2 ∈ GL(W)`;
- idempotents `E_a(z) = U^z E_a(0) U^(-z)` satisfying (Q1)–(Q3) of `sft-crossed-product-fp-iff-quantum-rigid`.

Then `R_Ω` embeds unitally in `∏_ω M_(N_n)(k)` iff finite-dimensional covariant `D`-families exist for
every `D`.

**Consequences.**
- By `periodic-quantum-tilings-refute-quantum-rigidity`: for aperiodic `Ω` these families never
  commute. So if `Ω` is quantum rigid at some scale, `R_Ω` is not matricial.
- Invariant measures always exist (`Z^2` is amenable), and the action is not residually finite
  (`sfts-without-finite-orbits-are-not-residually-finite-actions`). Classical towers therefore stop,
  and only contextual periodic quantum tilings can make `R_Ω` matricial.

Route: `matricial-z2-sft-crossed-products-give-quantum-tilings-proof`.

**Review (un-verify-measure, 2026-09-13): PASS, both directions.** The colimit converse is re-derived: kernel elements of 𝒜_D → R_Ω die at finite stages, so finite-dimensional covariant families give window-exact maps, then Lemma S. The artifact bullet that still called the converse open is replaced. Only unreviewed input: item 1 of periodic-quantum-tilings-refute-quantum-rigidity (for the rigid-SFT consequence). See `research/artifacts/un-review-measure-2026-09-13-part1.md` §M6.
