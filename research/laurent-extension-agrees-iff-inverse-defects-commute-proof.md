---
rg: 2
id: laurent-extension-agrees-iff-inverse-defects-commute-proof
kind: route
title: Steinberg commutator calculus against the rounding, plus the Kazhdan projection for the vertex
target: laurent-extension-agrees-iff-inverse-defects-commute
requires: []
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

**Conventions.**
- `[a, b] = a b a^(-1) b^(-1)`. In `St_r` with `i, j, k` distinct, `[x_ij(a), x_jk(b)] = x_ik(ab)`.
- `x_ij(a)` and `x_kl(b)` commute when `j ≠ k` and `i ≠ l`.
- `σ` satisfies these relations on `e_ij`, and `ρ'` on `x_ij`.
- `π = σ` on `Γ` in `M`. Closeness on `F_Γ` gives it on each fixed `γ ∈ Γ`, by word length.
- The map `R_+ -> A_n` is onto, so `ρ'_n(St_r(L)) = π_n(Γ)`.

**Item 1.** Fix `i`, set `h = x_i^(-1)`, `U = σ(e_23(h))` and `V = ρ'(x_23(h))`, so `W_i = V^* U`.
- For `f ∈ x_i R_+`, `fh ∈ R_+`. With `a = π(e_12(f))`, both `a U a^* U^*` and `a V a^* V^*` equal `π(e_13(fh))`.
  So `U a^* U^* = V a^* V^*`, and `V^* U` commutes with `a`.
- For `c ∈ x_i R_+`, `[x_23(h), x_31(c)] = x_21(hc)` with `hc ∈ R_+`. The same cancellation gives
  `W_i b = b W_i` for `b = π(e_31(c))`.
- Every root `e_kl(R_+)` that commutes with `e_23` commutes with both `U` and `V`, hence with `W_i`. Examples are
  `e_13` and `e_21`.
  - For `r >= 4`, the relations `[x_k2(f), x_23(h)] = x_k3(fh)` and `[x_23(h), x_3k(c)] = x_2k(hc)` add
    `e_k2(x_i R_+)` and `e_3k(x_i R_+)`.
- Let `H_i` be the group these elements generate. It contains:
  - `e_32(x_i^2 f) = [e_31(x_i f), e_12(x_i)]`;
  - for `r >= 4`, `e_k2(x_i^2 f) = [e_k1(x_i f), e_12(x_i)]` and `e_3k(x_i^2 f) = [e_31(x_i f), e_1k(x_i)]`.
- So `H_i` contains every `e_jk(x_i^2 R_+)`.
- `x_i` is a unit in `A_n` and `R_+ -> A_n` is onto, so `x_i^2 R_+ -> A_n` is onto. Hence `π_n(e_jk(x_i^2 R_+)) = π_n(e_jk(R_+))`,
  and `π_n(H_i) = π_n(Γ)`.

**Kazhdan projection.** `Γ` is Kazhdan (Ershov–Jaikin-Zapirain, r >= 3); let `(F_Γ, κ)` be a Kazhdan pair.
- Apply it to `Ad π_n` on `L^2(M_(n'), tr)`. Its invariant vectors are `π_n(Γ)'`, and
  `||T - E_n(T)||_2 <= κ^(-1) max_(s ∈ F_Γ) ||[T, π_n(s)]||_2`.
- So `π(Γ)' ∩ M = prod_U π_n(Γ)'`. An element of it commutes with every `(ρ'_n(y_n))_U`, even when `y_n` varies
  with `n`.

**Item 2, "if".** Let every `W_i ∈ π(Γ)' ∩ M`. Then `W_i` commutes with `V` and with `b = π(e_31(1))`.
- `σ(e_21(h)) = [V W_i, b] = V W_i b W_i^* V^* b^* = [V, b] = ρ'(x_21(h))`.
- For `f ∈ R_+`: `σ(e_23(hf)) = [σ(e_21(h)), π(e_13(f))] = ρ'(x_23(hf))`. Then `e_13(hf) = [e_12(1), e_23(hf)]`,
  `e_31(hf) = [e_32(1), e_21(hf)]` and `e_12(hf) = [e_13(hf), e_32(1)]`.
  - The other roots follow in the same way, and for `r >= 4` through a third index.
  - So `σ = ρ'` on `x_jk(x_i^(-1) R_+)` for all `j ≠ k` and all `i`.
- **Induction on the negative part `a` of the exponent.** `x_jk(x_i^(-1) x^(-a) f) = [x_jl(x_i^(-1)), x_lk(x^(-a) f)]`,
  with `l ∉ {j, k}`. So `σ = ρ'` on `x_jk(L)`, which generates `St_r(L)`.

**Item 2, "only if".** If `σ∘q = ρ'` then `W_i = 1`.

**Item 3.**
- `u_n` is a representative of `x_i^(m_n - 2)`.
- If `m_n <= m` along `U`, then `x_i^(m!) - 1` maps to zero in every `A_n`. So `π(e_12(x_i^(m!) - 1)) = 1`, and by
  `π = σ` on `Γ` the trace `τ(σ(e_12(x_i^(m!) - 1)))` is 1, not 0.

**Item 4.**
- If `ρ_n` is a Laurent rounding, then `ρ_n|Γ` factors through a finite `L/J` (artifact Lemma 6.1).
  - Its canonical extension is `ρ_n∘q`, by uniqueness of the ring extension `L -> L/J`.
  - So the defects are 1.
- Conversely, item 2 gives `σ∘q = ρ'` on `St_r(L)`.
- The finite-level descent statement is a remark, and nothing here uses it.
