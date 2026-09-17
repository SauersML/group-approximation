---
rg: 2
id: bit-register-cloning-group-has-doubly-exponential-period-growth
kind: claim
title: "The bit-register cloning system on Sym({0,1}^n) has a f.g. subgroup with doubly exponential period growth"
distinct_from:
  some-finite-cloning-system-group-is-not-locally-cocf: that is the non-coCF conclusion; this is the explicit period-growth estimate for one concrete cloning system, with no coCF input
  twisted-direct-power-cloning-finite-groups-are-cocf: that family has G_n = S_n ⋉ G^n with exponent polynomial in n; here G_n = Sym({0,1}^n) and short words reach order exp(exp(n^(1/3)))
artifacts:
  - experiments/cloning-period-growth-2026-09-17/check_cloning_axioms.py
  - experiments/cloning-period-growth-2026-09-17/phi_and_counter_circuit.py
  - experiments/cloning-period-growth-2026-09-17/output.txt
---

**ESTABLISHED (unreviewed).** Route `bit-register-cloning-period-growth-proof`.

**The cloning system.**
- `G_n = Sym({0,1}^n)`, with product `(gh)(x) = g(h(x))`.
- `ι_(m,n)(σ)` acts by `σ` on the first `m` bits and trivially on the rest.
- `ρ_n` is trivial (the pure case).
- `(σ)κ^n_k ∈ Sym({0,1}^(n+1))` acts by `σ` on the coordinates `{1,…,n+1} \ {k+1}`, in order, and leaves coordinate `k+1` unchanged.

This is a cloning system on finite groups in the sense of Witzel–Zaremsky. Write `T` for its Thompson-like group `T(G_*)`.

**Claim.** There are:
- a finitely generated subgroup `Γ ≤ T`, with finite symmetric generating set `S`, and
- elements `w_s ∈ Γ` for `s ≥ 2`,

such that each `w_s` has finite order, `‖w_s‖_S ≤ 248 s^3`, and

`ord(w_s) ≥ lcm(1, 2, …, 2^s − 1) ≥ 2^(2^s − 2) / 3`.

So `p_(Γ,S)(n) ≥ exp(c · exp(c' n^(1/3)))` for suitable `c, c' > 0` and all large `n`.

**Generators.**
- `Γ = ⟨A, B_1, Sym({0,1}^3)⟩`.
- `A, B_1 ∈ F ≤ T` are dyadic PL maps with `A(p_i) = p_(i+1)` for `p_i = 1 − 2^(−i)`, `i ≥ 1`.
- `B_1` fixes `[0, 1/2]` and shifts `p_i ↦ p_(i+1)` for `i ≥ 2`.
- `Sym({0,1}^3)` sits in `T` as `[T_4, 1 ⊗ g, T_4]`, where `T_4` is the right comb with leaves `[0,1/2]`, `[1/2,3/4]`, `[3/4,7/8]`, `[7/8,1]`.

**How `w_s` works.** Conjugation by words in `A, B_1` moves a 3-bit gate to any three coordinates among `p_1, …, p_(3s)` at cost `O(s)`. The element `w_s` is a product of `O(s^2)` such conjugates. It implements a reversible counter circuit `P = Inc ∘ T_a` on `3s` bits. On the slice with register `a`, `P` has cycles of lengths `a+1` and `2^s − 1 − a`.

Consequence (with Bishop–Bodart–Issini–Perego Thm 2.7): `Γ` is not coCF. See `finite-cloning-group-not-locally-cocf-by-period-growth`.
