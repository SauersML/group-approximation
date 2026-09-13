---
rg: 2
id: f2-groups-have-paradoxical-free-minimal-subshifts-proof
kind: route
title: Proof — paradox from F_2 along right cosets, closed coordinate encoding, product with a Gao–Jackson–Seward free minimal subflow
target: f2-groups-have-paradoxical-free-minimal-subshifts
requires:
  - gjs-countable-groups-have-free-minimal-subflows
artifacts:
  - research/artifacts/un-horofunction-families-paradoxical-subshifts-2026-09-13.md
---

Full details: `research/artifacts/un-horofunction-families-paradoxical-subshifts-2026-09-13.md`, §§1–3.

1. **Paradox on `Γ` (Lemma 1).**
   - In `F = ⟨a, b⟩` free, let `W(x)` be the reduced words starting with `x`. Then `a W(a^{-1}) = F \ W(a)`, and likewise
     for `b`.
   - The partitions `F = W(a) ⊔ a W(a^{-1}) = W(b) ⊔ b W(b^{-1})` with `g = (e, a^{-1})`, `h = (e, b^{-1})` have
     translates `W(a), W(a^{-1}), W(b), W(b^{-1})`, which are pairwise disjoint.
   - With a transversal `T` of right cosets, `A_i = ⊔_t A_i^F t` and `B_j = ⊔_t B_j^F t` work for `Γ`, because left
     multiplication by `F` preserves each `F t`.
2. **Encoding (Lemma 2).**
   - `Γ` acts on `({0,1}^4)^Γ` by `(γ·x)(g) = x(gγ)`, and `x_0(g) = (χ_{A_1}, χ_{A_2}, χ_{B_1}, χ_{B_2})(g)`.
   - `γ·{x(e)_k = 1} = {y(γ^{-1})_k = 1}`, so the partition and disjointness assertions for `X = cl(Γ x_0)` are
     closed coordinate identities.
   - On the orbit, `y = δ·x_0` gives `y(g_i^{-1})_i = χ_{g_i A_i}(δ)` and `y(e)_1 + y(e)_2 = 1`, and these hold by
     step 1.
3. **Product (Proposition 3).**
   - `W ⊆ 2^Γ` is a free minimal subflow (the required import; `Γ` is countably infinite). `Z` is a minimal subset of
     `X × W`, which exists by Zorn's lemma.
   - Free: stabilizers are contained in those of `W`, which are trivial.
   - Cantor: `Z` is infinite, since the action is free and `Γ` is infinite, and a minimal infinite flow has no isolated
     points; zero-dimensional compact metrizable spaces that are perfect are Cantor (Brouwer).
   - (H-gen): translates of the coordinate-at-`e` cylinders of both factors are all coordinate cylinders, so they
     separate points.
   - (H-par): pull back the partitions of step 2 along the equivariant projection `Z → X`.
