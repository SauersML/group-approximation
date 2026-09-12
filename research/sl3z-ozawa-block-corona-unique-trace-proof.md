---
rg: 2
id: sl3z-ozawa-block-corona-unique-trace-proof
kind: route
title: Fixed-point counts give the regular limit trace, Bekka rigidity excludes all others, and the parabolic vector state survives in the kernel
target: sl3z-ozawa-block-corona-has-unique-trace
requires: [kazhdan-block-algebras-contain-their-block-ideal]
artifacts:
  - research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md
---

Full proof: `research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md` §2.

1. **Limit trace.** `tr(σ_k(g)) = (Fix_{p_k}(g) − 1)/(p_k² + p_k)`.
   - A non-scalar matrix mod `p` fixes at most `p + 2` projective points.
   - For `g ≠ e`, `g` is scalar mod `p` for only finitely many `p`.
   - So `lim_k tr(x_k)` exists on `B`, vanishes on `I`, and is `δ_e` on `Γ`.
2. **Uniqueness.** The traces of `A` form a closed face of the traces of
   `C*(Γ)`. An extreme point is a finite factor representation vanishing on
   `ker(C*(Γ) → A)`. By Bekka, it is finite-dimensional, or `π|_Λ` extends to
   `L(Λ)` for some finite-index normal `Λ`.
   - The first case is a finite-dimensional representation of `A`, excluded by
     `kazhdan-block-algebras-contain-their-block-ideal`.
   - In the second case the character is `δ_e` on `Λ`.
   - Every `g ≠ e` has infinite `Λ`-conjugacy class, since a finite class would
     make `g` commute with powers of all elementary matrices.
   - Distinct conjugates `g_i` give orthonormal vectors `π(g_i) ξ`, because
     `g_j⁻¹ g_i ∈ Λ ∖ {e}`. Their inner products with `ξ` all equal `φ(g)`, so
     Bessel gives `φ(g) = 0`.
   - By Krein–Milman, `τ_0` is the only trace.
3. **Nonzero kernel.** Let `ξ_k` be the normalized component of `δ_{[1:0:0]}`
   orthogonal to the constants.
   - `⟨σ_k(g) ξ_k, ξ_k⟩ → 1_P(g)` pointwise, because `g` fixes `[1:0:0]` mod `p`
     for all large `p` iff `g_21 = g_31 = 0`.
   - A weak* limit of these vector states vanishes on `I`, so it gives
     `λ_{Γ/P} ≺ ρ_∞`.
   - If `K = 0`, restricting to `P` gives `1_P ≺ λ_P`, contradicting
     non-amenability of `P ⊃ SL(2,Z)` (Hulanicki–Reiter).
4. **No bounded traces on `K`.** A bounded trace on an ideal extends to a trace on
   `A`: take the norm-preserving positive extension `φ`. Then
   `φ(y*y) = lim τ(y e_λ² y*) ≤ φ(yy*)`, and equality follows by symmetry. So the
   extension is `c τ_0`, which is zero on `K`.

Literature imports:
- Bekka, Invent. Math. 169 (2007), main theorem;
- the Hulanicki–Reiter criterion.

Bekka's statement was checked against the abstract of arXiv:math/0609102v2. The
theorem is virtual, extending only on a finite-index `Λ`, which is why step 2
contains the orthogonality argument. The full PDF was not re-read, because MSI
authentication was unavailable. Status is kept in §6 of the artifact.
