---
rg: 2
id: exactly-matricial-rings-have-lef-general-linear-groups-proof
kind: route
title: Pass a finite multiplication table to one ultraproduct coordinate, then to a finite quotient by Malcev
target: exactly-matricial-rings-have-lef-general-linear-groups
requires: []
artifacts:
  - research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md
---

1. **Units.** `M_N(∏_ω A_k) = ∏_ω M_N(A_k)` as rings, so the embedding induces an injective unital ring
   homomorphism `M_N(R) → ∏_ω M_(N d_k)(F_k)`. An ultraproduct element is invertible iff ω-almost all of its
   coordinates are, with the inverse taken coordinatewise. This gives an injective group homomorphism
   `GL_N(R) → ∏_ω GL_(N d_k)(F_k)`.
2. **One coordinate.** Fix a finite `F ⊆ GL_N(R)`. The finitely many identities `fg = h` and inequalities `f ≠ g`
   (for `f, g, h ∈ F`) hold in ω-almost every coordinate. Choose one, `k`, and let `ψ` be the coordinate map. It is
   injective on `F` and multiplicative on products that stay in `F`.
3. **A finite image.** `Λ = ⟨ψ(F)⟩ ≤ GL_(N d_k)(F_k)` is finitely generated and linear, so it is residually
   finite (Malcev). Take a finite-index normal `Δ ◁ Λ` avoiding the finitely many `ψ(f)ψ(g)^-1` with `f ≠ g`.
   Then `F → Λ/Δ` is injective and partially multiplicative, so `GL_N(R)` is LEF, and so are its subgroups.
4. **Consequences.**
   - LEF ⇒ sofic (Elek–Szabó), and sofic ⇒ hyperlinear.
   - LEF ⇒ MF: take partial embeddings `ψ_n` of growing windows into finite groups `Q_n`, and set
     `V_n(g) = λ_(Q_n)(ψ_n(g))`. These are exactly multiplicative on the windows, and for `g ≠ 1`,
     `‖V_n(g) − 1‖ >= ‖(λ(ψ_n(g)) − 1)δ_e‖ = √2` eventually.
   - So `g ↦ [(V_n(g))]` is an injective corona homomorphism, and `G` is MF by Lemma l.351 of
     `non_mf_groups_exist.tex`.
