---
rg: 2
id: compressor-extension-makes-roundable-vertex-part-invariant-proof
kind: route
title: Close roundable corners under joins by Kazhdan corner rounding, then let each compressor endomorphism fix the maximum
target: compressor-extension-makes-roundable-vertex-part-invariant
requires:
  - elementary-groups-over-fg-rings-have-property-t
  - kt-wreath-models-never-round-on-the-vertex
artifacts:
  - research/artifacts/hs-extension-roundable-part-invariance-2026-09-13.md
---

The full derivation is in §§1–5 of the artifact. The first premise supplies property (T) of the vertex. The second
is used only in the wreath corollary.

1. **Kazhdan corner lemma.** Suppose `π` is genuine and `max_s ||[P, π(s)]||_2 <= ε`. Projecting `P` onto
   `Fix(Ad π)` gives `X ∈ π(Γ)'` with `||P - X||_2 <= ε/κ`. Then `P_0 = 1_[1/2, ∞)(X)` has
   `||P - P_0||_2 <= 2ε/κ`.
2. **Closure.**
   - **Subprojections.** A subprojection of a roundable `p` almost commutes with the rounding. Item 1 rounds it.
   - **Equivalence.** `v ∈ R` intertwines the two corner representations.
   - **Orthogonal sums.** Off-diagonal blocks vanish in `||·||_2`, since `p ∈ R`.
   - **Increasing limits.** Replace the small corner by a trivial representation and diagonalize.
3. **Maximum.**
   - Kaplansky's `p ∨ q - p ~ q - p ∧ q` with item 2 makes the roundable projections upward directed. Their
     supremum `p_max` is roundable.
   - Unitary conjugates of `p_max` in `R` are roundable, so `p_max ∈ Z(R)`.
4. **Invariance.**
   - `gΓg^(-1) ⊆ Γ` gives `θ_g(R) ⊆ R`.
   - A rounding of the `p`-corner restricts to `gΓg^(-1)` on bounded words. So `θ_g(p)` is roundable and
     `θ_g(p_max) <= p_max`.
   - Trace preservation forces equality. `H = <P_Γ(H)>` then gives `p_max ∈ σ(H)'`.
5. **Traces.** `τ(p ·)/τ(p)` is a normal trace on `L(H)`, of the form `τ_reg(· c)` with `c ∈ C[Z]`. So it
   vanishes off the center `Z`.
6. **The actor.**
   - `I + E_ij` generate `SL_d(Z)`. Sign-changing elements of `SL_d(Z)` move `N^d` onto every orthant, so
     `<Γ, SL_d(Z)> = G`.
   - Non-scalar elements have infinite conjugacy classes under the `e_ij(x^v)` and substitutions.
7. **Wreath.**
   - `p_max ∈ Z(R)` commutes with `e_Γ ∈ R`, and with `σ(G)`, so it commutes with `σ(W)`.
   - With trivial center the corner is a trace-preserving `W`-model whose vertex rounds. The second premise
     excludes it, so `p_max = 0`.
