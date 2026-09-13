---
rg: 2
id: constant-shape-substitutions-inflate-torus-tiling-modules-proof
kind: route
title: Inflated generators sum the parent idempotents; illegal inflated patterns expand into parent patterns whose legal ones substitute to legal patterns
target: constant-shape-substitutions-inflate-torus-tiling-modules
requires: []
artifacts:
  - research/artifacts/un-labbe-torus-decider-inflation-2026-09-13.md
---

Artifact §3.

1. **Well defined.** Changing `t'` by `Sλ` changes the parent `p` by `λ` and keeps `j`.
2. **(T1).** `sum_b f_b(t') = sum_a e_a(p̄) = 1`. By orthogonality of the `e_a(p̄)`,
   `f_b(t') f_(b')(t') = δ_(bb') f_b(t')`.
3. **(T2).** Generators with one parent commute. If `t'_2 - t'_1` has a representative `w'` with `|w'| <= 2D'`, the
   parents `⌊t'_l/S⌋` differ coordinatewise by at most `⌈|w'_i|/s_i⌉ <= 2(D-1) <= 2D`. So they commute by (T2) at
   scale `D`.
4. **(T3).** Let `π ∉ L_(B_(D'))(Ω)`, lift its ball to `Z^2`, and let `P` be its set of parents. In each coordinate `P`
   takes at most `⌈(2D'+1)/s_i⌉ <= 2D - 1` consecutive values, so `P ⊆ c + B_(D-1)`.
   - Grouping the commuting factors by parents gives `prod_(p ∈ P) sum_(a ∈ A_p) e_a(p̄)`, where `A_p` is the set of
     letters whose image agrees with `π` on the positions covered by `p`.
   - Inserting (T1) on `c + B_D \ P` expands this into `sum_(ρ̃) prod_(z ∈ c+B_D) e_(ρ̃(z))(z̄)`, over `ρ̃` with
     `ρ̃(p) ∈ A_p`. Repeated torus sites with different letters give zero terms, so no embedding of the ball is used.
   - Terms with `ρ̃` illegal vanish by (T3) at scale `D`.
   - If `ρ̃` is legal, pick `x ∈ Ω` extending it. Then `σ(x) ∈ Ω` agrees with `π` on the ball, so `π` is legal,
     which is a contradiction.
5. **Growth.** `D' = s_min(D-1) >= 2D - 2 >= D + 1` for `D >= 3`. ∎
