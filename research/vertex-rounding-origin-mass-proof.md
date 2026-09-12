---
rg: 2
id: vertex-rounding-origin-mass-proof
kind: route
title: Match the restricted and the transported roundings of a strictly positive compression by property (T)
target: vertex-rounding-non-unit-mass-at-origin
requires:
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - kazhdan-projection-is-norm-limit-of-finite-averages
artifacts:
  - research/artifacts/nh-unit-type-counterexample-2026-09-12.md
---

The full proof is in §§2–4 of the artifact. The Kazhdan input is property (T) of
`EL_r(F_q[y_1..y_d])` for `r >= 3` (Ershov–Jaikin-Zapirain, *Invent. Math.* 179 (2010)).

- **Two roundings of `Λ = AΓA^(-1) = EL_r(S)`,** where `S = F_q[x^(A e_j)]` and every `A_ij >= 1`:
  - `ρ_1 = π_n|Λ`;
  - `ρ_2 = U_n π_n(A^(-1)·A) U_n^*`, with `U_n = σ_n(A)`.
  Both are `o(1)`-close to `σ_n` on the generators of `Λ`.
- **Matching (Lemma 2.1).**
  - Property (T) turns `||ρ_1 - ρ_2||_2`-closeness into an intertwiner `T` with `||T - 1||_2 <= η_n`.
  - Since `|| |T| - 1 ||_2^2 <= 3η_n`, the polar part of `T` identifies subrepresentations of trace `>= 1 - 12η_n`.
  - So isotypic masses of any class set agree up to `12η_n`.
- **Types (Lemmas 3.1–3.2).**
  - Kernel ideals `J_ρ` are ideals of finite index (item 1 of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`).
  - Transport along `ψ : y_j -> x_j` keeps local types and depths.
  - Restriction to the strictly positive `S` sends every nonempty type to the full type, because `x^(A e_j) ∈ m` iff some `x_i ∈ m`.
  - At the origin, restriction divides the depth `o_j` by `A_jj`.
- **Items 1–2.**
  - Intermediate classes have zero mass in `ρ_1`, so their mass in `π_n` is at most `12η_n`.
  - At the origin, `P_n(t) <= P_n(2t-1) + 24η_n`; iterate for `t >= 2`.
- **Item 3.**
  - The congruence kernel `Γ_I` has finite index, so it is Kazhdan, and its Kazhdan projection is a norm limit of finite probability averages `a_k`.
  - `τ(π_n(a_k))` and `τ(σ_n(a_k))` differ by `o(1)` along `U`.
  - `τ(σ(a_k)) = a_k(e)` tends to `0`, because `Γ_I` is infinite.
