---
rg: 2
title: "UN review, Labbé ring: torus quantum tilings and growth of tiling modules (2026-09-13)"
kind: artifact
---

Lane `un-verify-measure`, 2026-09-13. Part 3 (parts 1–2: `un-review-measure-2026-09-13-part1.md`, `part2.md`).
Reviewed: `un-labbe-ring` landing ccf79fa351 (artifact `research/artifacts/un-labbe-ring-torus-tilings-2026-09-13.md`),
and item 1 of `matricial-aperiodic-sft-rings-are-not-quantum-rigid` (un-converse), which it uses. Nodes read at tip
88fc580eb0 and rechecked unchanged at dce95b0050. No FAIL.

## L1 `torus-quantum-tilings-decide-matriciality-of-sft-rings`: PASS

- **(a) Induction.** Recomputed on W = ⊕_{s ∈ T_Λ} V with (U^g ξ)_s = ξ_{s+g}:
  (U^g E_a(0) U^{-g} ξ)_s = e_a(s + ḡ) ξ_s, which is how E_a(g) acts on summand s. So covariance holds, and U^g
  depends only on ḡ, so U_1 and U_2 commute and have finite order. (Q1) is (T1) summandwise. For |z − z'| ≤ 2D,
  the difference of classes has the representative z' − z ∈ B_{2D}, so (T2) gives (Q2). (Q3) at z is (T3) at z̄ + s.
  Only (T2) ⇒ (Q2) is used; (T2) may impose more commutations on small tori, which is harmless.
- **(b) Restriction.** Over finite k, GL(W) is finite, so Λ = ker(g ↦ U^g) has finite index and E_a(z + λ) = E_a(z).
  (T2): for t' − t ∋ w ∈ B_{2D}, choose z ∈ t and z' = z + w, then (Q2) applies. (T3) comes from (Q3) at any
  representative.
- **(c) Specialization.** The scale-D identities are finitely many polynomial identities with integer coefficients in
  ψ_n(χ[a]) and ψ_n(u_{e_i}^{±1}). By Łoś they hold exactly for ω-most n, the ultraproduct of algebraic identities
  being coordinatewise. The unital map kills p, so ω-most F_n have characteristic p. A nonempty F_p-scheme of
  finite type has an F̄_p-point (Nullstellensatz), hence a point over some finite F_{p^m} ⊇ k. Restricting scalars
  gives a family over k.
- **(d) Equivalence.** (⇒) is (c) then (b). (⇐) is (a) at every scale, then the families-to-matricial direction
  of `matricial-z2-sft-crossed-products-give-quantum-tilings` (PASS, part 1 §M6) with simplicity for free minimal Ω.
- **Item 1 of `matricial-aperiodic-sft-rings-are-not-quantum-rigid` (un-converse): PASS.**
  - The window holds u^v for ‖v‖_∞ ≤ 2D + 1 and pair products, so ψ(u^v) = U^v by induction.
  - The matrix entries generate a finitely generated commutative domain A: a Jacobson ring with finite residue
    fields and nilradical 0, so some maximal ideal avoids the product of the chosen nonzero entries.
  - π preserves every window identity, the U_i have finite order in GL_d(A/m), and (Q1)–(Q3) follow as displayed.
  - Item 1 needs no aperiodicity. Item 2 cites `periodic-quantum-tilings-refute-quantum-rigidity`, which is
    unreviewed; L1 uses item 1 only.
- **Subsumption scan** (untruncated: 31 claim or route files mention tori with tilings or subshifts; 26 mention
  quantum tilings or periodic families):
  - `labbe-tilings-from-exact-matricial-crossed-product` is the Labbé instance of (c);
  - `free-minimal-z2-sft-is-quantum-rigid` and `quantum-matricial-models-separate-full-groups-from-elementary` are OPEN
    and consistent;
  - `z2-sft-derived-full-group-lef-from-tiling-modules` concerns a different conclusion (LEF of the full group).
  - No conflict.
- **Display check.** The claim and route displays match the artifact and my recomputation.

## L2 `sft-tiling-module-dimensions-and-periods-must-diverge`: PASS, with a display GAP

- **(1) Periods.**
  - Sup-diameter ≤ 2D means every class of Z²/Λ has a representative in B_{2D}. With periodicity and (Q2), all
    E_a(z) commute, and there are finitely many distinct operators.
  - Idempotents are diagonalizable over any field, since x² − x splits with distinct roots, and commuting ones are
    simultaneously diagonalizable. So a common eigenvector v ≠ 0 exists, and by (Q1) exactly one a has E_a(z)v = v.
  - (Q3) puts every B_D-window of x in the language. r ≤ D and restriction of occurring patterns make x avoid the
    forbidden B_r-patterns, so x ∈ Ω.
  - x is Λ-periodic, so its orbit is finite, and a finite orbit is closed and invariant. Infinite minimality rules this out.
- **(2) Dimensions.**
  - Products of commuting idempotents over the patterns on B_m are orthogonal and sum to 1, and rank is additive on
    orthogonal idempotents. This gives total mass 1 and consistent marginals, with translation invariance from
    conjugation by U^z. Vanishing off the language comes from summing the (Q3)-killed extensions to B_{D_j}.
  - A diagonal subsequence converges. Kolmogorov gives a shift-invariant μ with μ(Ω) = 1, since the complement of Ω
    is a countable union of non-occurring cylinders.
  - Full support comes from minimality. There are no atoms, since invariance would give an infinite orbit infinite
    mass, and finite orbits are excluded.
  - The cylinders around a point decrease to its (null) singleton, so some ρ ∈ L(Ω) has 0 < μ([ρ]) < 1/N. Hence
    0 < w_j(ρ) < 1/N eventually, which is impossible with denominators ≤ N.
- **Overlap (credit).** (1) is a quantitative form of item 1 of `periodic-quantum-tilings-refute-quantum-rigidity`. A
  small torus forces commutation, and that node forbids a commuting family for aperiodic SFTs after induction
  (L1(a)). The node already lists it in `distinct_from`; a credit sentence is added.
- **GAP, display.** The claim node used "sup-diameter" without defining it. The definition is added at review:
  max over classes t ∈ Z²/Λ of min{|w|_∞ : w ∈ t}.
- **Model test note.** The first model test uses infinite minimal Z-subshifts, which are never SFTs. It illustrates
  growth for their Markov approximations as an analogue; it is not an instance of the hypotheses. This is noted on the
  node.
- **Subsumption.** Same scan as L1, no conflict.
