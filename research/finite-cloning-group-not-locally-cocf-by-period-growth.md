---
rg: 2
id: finite-cloning-group-not-locally-cocf-by-period-growth
kind: route
title: "The bit-register cloning group contains a f.g. subgroup of doubly exponential period growth, beyond the coCF bound exp(n^4)"
target: some-finite-cloning-system-group-is-not-locally-cocf
requires:
  - bit-register-cloning-group-has-doubly-exponential-period-growth
  - cocf-group-torsion-order-bounded-by-word-length
---

**Witness.** The cloning system is `G_n = Sym({0,1}^n)`, pure, with `κ^n_k` inserting a fixed coordinate at `k+1`
(`bit-register-cloning-group-has-doubly-exponential-period-growth`). Every `G_n` is finite, so this is a cloning
system on finite groups. Its Thompson-like group `T` contains the finitely generated subgroup `Γ = ⟨S⟩`.

**Γ is not coCF.** Suppose `coWP(Γ, S')` is context-free for some finite generating set `S'` of `Γ`.
- Put `C = max_(t ∈ S) ‖t‖_(S')`. Then `‖x‖_(S') ≤ C‖x‖_S` for all `x ∈ Γ`.
- For `s ≥ 2`, the element `w_s` has finite order and `ord(w_s) ≥ 2^(2^s−2)/3 > 1`. So `w_s ≠ 1`.
- Put `n_s = ‖w_s‖_(S')`. Then `1 ≤ n_s ≤ 248 C s^3`.
- By `cocf-group-torsion-order-bounded-by-word-length`, there is `m` with
  `2^(2^s−2)/3 ≤ ord(w_s) ≤ n_s · ord(w_s) ≤ 2^((m n_s^2+1)^2) ≤ 2^((m·248^2 C^2 s^6 + 1)^2)`.
- The left side is `2^(2^s − O(1))` and the right side is `2^(O(s^12))`. So the inequality fails for all large `s`.

This contradiction shows `coWP(Γ, S')` is context-free for no finite generating set `S'`. So `Γ` is not coCF, and `T`
is not locally coCF.

The target's own statement allows "(or some finitely generated subgroup of it)", which is exactly this situation.

**Scope.**
- Finite generation of `T` itself is not used.
- For comparison, `p_V(n) ≍ exp(n^2)` (BBIP Thm 6.2(b)), while `Γ` has `p_Γ(n) ≥ exp(exp(c n^(1/3)))`.
- So no finitely generated subgroup of `V` contains `Γ`. This is the embedding half of Zaremsky 2.16 as well; see
  `zaremsky-2-16-by-not-cocf` and `finite-cloning-group-not-in-v-by-period-growth`.
