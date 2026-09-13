---
rg: 2
id: rigid-actions-have-no-dbar-close-bernoulli-models-proof
kind: route
title: In an invariant joining, a rigidity sequence nearly fixes the model coordinates while i.i.d. labels at distinct sites differ with probability c_lambda
target: rigid-actions-have-no-dbar-close-bernoulli-models
requires: []
---

Notation as in the target. The shift is `(g.x)(t) = x(g^-1 t)`, so `x(g) = (g^-1.x)(1_G)`.

**Theorem.** Let `J` be a `G`-invariant joining of `ν` and `λ^G` on `L^G × L^G`, and `d = J(x(1) ≠ y(1))`.

- **Invariance.** `{(x, y) : x(g) ≠ y(g)}` is the preimage of `{x(1) ≠ y(1)}` under `(x, y) ↦ g^-1.(x, y)`.
  So it has `J`-measure `d` for every `g`.
- **The model is nearly fixed.** Put `A_l = α^-1(l)`. Then `α(g^-1 z) = l` iff `z ∈ g A_l`, so
  `{z : α(g^-1 z) ≠ α(z)} ⊆ ∪_l (g A_l Δ A_l)`. Along the rigidity sequence,
  `ν(x(g_n) ≠ x(1)) ≤ Σ_l μ(g_n A_l Δ A_l) → 0`.
- **The i.i.d. side is not.** For `g_n ≠ 1_G`, `y(g_n)` and `y(1)` are independent with law `λ`, so
  `λ^G(y(g_n) ≠ y(1)) = c_λ`. The `g_n` leave finite sets, so `g_n ≠ 1_G` for large `n`.
- **Triangle inequality.** In `J`,

      c_λ = J(y(g_n) ≠ y(1)) ≤ J(y(g_n) ≠ x(g_n)) + J(x(g_n) ≠ x(1)) + J(x(1) ≠ y(1)) = 2d + ν(x(g_n) ≠ x(1)).

  Letting `n → ∞` gives `d ≥ c_λ/2`. The joining was arbitrary, so `d̄(ν, λ^G) ≥ c_λ/2`.

**Hosts.** Let `G` be infinite and `ι: G → K` an injective homomorphism into a compact metrizable group.
Replace `K` by the closure of `ι(G)`, and let `G` act on `(K, Haar)` by `g.k = ι(g) k`.
- **Free.** `ι(g) k = k` forces `ι(g) = 1`, hence `g = 1`.
- **Ergodic.** An invariant `f ∈ L^2(K)` is invariant under the closure of `ι(G)`, which is `K`, since left
  translation is continuous on `L^2(K)`. So `f` is constant.
- **Rigid.** `K` is infinite, being the closure of an infinite injective image, and a compact group with an
  isolated point is finite. So every neighbourhood `U` of `1_K` has `U \ {1_K}` open and non-empty, and it meets
  the dense set `ι(G)`. Choose `g_n ≠ 1_G` with `ι(g_n) → 1_K`. Each fixed element occurs only finitely often
  among the `g_n`, so they leave every finite set. Left translation is continuous on `L^1(K)`, so
  `μ(g_n A Δ A) = ‖1_(ι(g_n) A) − 1_A‖_1 → 0`.

An infinite residually finite group embeds injectively in its profinite completion, so it is covered. The
Kun–Thom groups are residually finite (`bernoulli-entropy-counterexample-constraints`, Hosts). A product of
residually finite groups is residually finite, which covers `P × G` for residually finite `G`.
