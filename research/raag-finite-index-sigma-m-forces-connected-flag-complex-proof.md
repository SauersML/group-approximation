---
rg: 2
id: raag-finite-index-sigma-m-forces-connected-flag-complex-proof
kind: route
title: A copy of L at infinity in the ascending orthants retracts off the punctured cube complex, so essential connectivity of half-spaces makes L connected
target: raag-finite-index-sigma-m-forces-connected-flag-complex
requires: []
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part2.md
---

Complete proof in `research/artifacts/zp-raag-virtual-kernels-2026-09-13-part2.md`, Sections 1--3.

Inputs: the geometric criterion of Bieri--Renz for `Σ^m` and `Σ^m(−; R)` (essential
`(m−1)`-connectivity, resp. acyclicity, of the half-spaces of an equivariant height on a
free cocompact contractible complex); openness of `Σ^m` in the character sphere (printed in
Zaremsky's list under Problem 1.13); the CAT(0) cube structure of the universal cover `X̃`
of the Salvetti complex, whose vertex links are octahedralizations `OL` and whose flats
`x·A_σ` are convex.

Steps.
1. For each generator `v`, `χ ↦ χ(v^{N_v})` is a nonzero functional on `Hom(H, R)`, since
   `[v^{N_v}]` maps to `N_v [v] ≠ 0` in `H_1(A_L; Q)`. By openness there is `[ψ] ∈ Σ^m(H)` with
   averaged slope `ψ̄(v) = ψ(v^{N_v}) / N_v ≠ 0` for every `v`.
2. Signs `s(v) = sign ψ̄(v)`. The union over simplices `σ` of the positive orthants of
   `1·A_σ` in directions `v^{s(v)}` is a Euclidean cone over the full subcomplex `{v^{s(v)}} ≅ L`
   of `OL`; let `S_R` be its sphere of radius `R`.
3. `ρ = forget ∘ dir_1: X̃ ∖ {1} → |L|` is continuous and restricts to a homeomorphism `S_R → |L|`.
4. For an `H`-equivariant height `g`, `g ≥ g(1) + cR − C'` on `S_R`, with `c = min_v |ψ̄(v)|`
   (finite-index lattices in each `A_σ` plus bounded variation).
5. If `f: S^k → |L|` is essential with `k ≤ m−1`, lift it to `S_R`. The criterion null-homotopes it
   inside `g ≥ g(1) + cR − C' − λ`, which misses `1` for large `R`; applying `ρ` null-homotopes `f`.
   The homological version is identical with cycles.
