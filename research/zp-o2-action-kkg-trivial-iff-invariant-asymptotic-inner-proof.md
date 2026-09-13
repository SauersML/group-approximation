---
rg: 2
id: zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner-proof
kind: route
title: Apply Gabe--Szabó unital uniqueness to the generator and the identity, average the unitary path into the fixed points, then feed the splitting theorem
target: zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner
requires:
  - zp-restriction-trivial-splits-cellular-plus-phantom
  - gabe-szabo-unital-uniqueness-theorem
  - izumi-rokhlin-approximately-representable-duality
---

**Item 1.**
- **(⟹)** Apply Theorem 5.8 of `gabe-szabo-unital-uniqueness-theorem` with
  `A = B = O_2` and `α = β`. Its hypotheses hold:
  - `G = Z/p` is exact, and every action of a finite group is amenable;
  - `O_2` is unital, exact and Kirchberg;
  - `α` is pointwise outer, hence isometrically shift-absorbing
    (Proposition 3.15).

  The unital cocycle embeddings `(α_ω, 1)` and `(id, 1)` have classes `θ` and
  `1`. If `θ = 1`, they are asymptotically unitarily equivalent. By
  Definition 1.15 with trivial cocycles there is a continuous unitary path
  `u_t` with `α_ω(a) = lim u_t a u_t^*`, or the same with `u_t^*`, and
  `‖1 − u_t α_g(u_t)^*‖ = ‖α_g(u_t) − u_t‖ → 0`.
- **Averaging.** Put `E(x) = (1/p) Σ_g α_g(x)`, a conditional expectation onto
  `O_2^α`, and `δ_t := ‖E(u_t) − u_t‖ ≤ max_g ‖α_g(u_t) − u_t‖ → 0`.
  - For `δ_t < 1`, `E(u_t)` is invertible in `O_2^α`, and
    `w_t := E(u_t) |E(u_t)|^(−1)` is a unitary of `O_2^α` depending continuously
    on `t`.
  - The polar part depends continuously on invertibles near the unitaries, and
    `u_t` is a unitary with `‖E(u_t) − u_t‖ = δ_t → 0`. So `‖w_t − u_t‖ → 0`,
    and `‖Ad(w_t)(a) − Ad(u_t)(a)‖ ≤ 2‖w_t − u_t‖ ‖a‖ → 0`.
  - Hence `α_ω = lim Ad(w_t)` pointwise, and `α_(ω^k) = lim Ad(w_t^k)` with
    `w_t^k ∈ O_2^α`.
  - A sequence `t_n → ∞` gives Izumi's strong approximate innerness,
    Definition 4.13 as quoted in `izumi-rokhlin-approximately-representable-duality`.
- **(⟸)** This is the "if" part of Theorem 5.8.

**Item 2.** Let `E = (O_2, α)`. `Res E = O_2 ≃_KK 0`, by Cuntz. Item 5 of
`zp-restriction-trivial-splits-cellular-plus-phantom` (⟹ direction) gives
`θ_E = 1` for `E ∈ B^G`. Then:
- item 1 gives strong approximate innerness;
- item 3 of `izumi-rokhlin-approximately-representable-duality` (Izumi I,
  Theorem 4.6, prime-power order) gives approximate representability;
- item 2 there (duality) gives the Rokhlin property of `α̂`.

**Item 3.** Item 4 of the splitting theorem: detection gives `θ_E = 1` for
every separable `E` with `Res E ≃ 0`. Apply it to `E = (O_2, α)`, then
continue as in item 2.

**Item 4.** Let `E` be separable nuclear with `Res E ≃ 0`.
1. By Theorem D, `E` is KK^G-equivalent to an outer action `β` on a stable
   Kirchberg algebra `B`. `B` is KK-contractible, so `B ≅ O_2 ⊗ K`.
2. The fixed-point algebra `B^β` is a corner of `B ⋊ G`, which is simple and
   purely infinite because `β` is outer on a simple purely infinite algebra.
   So `B^β` contains a nonzero projection `q`.
3. `qBq` is a unital KK-contractible Kirchberg algebra, hence `≅ O_2`.
   `β|_(qBq)` is outer, and the full invariant corner inclusion is a
   KK^G-equivalence.
4. The hypothesis and item 1 (⟸) give `θ_(qBq) = 1`. By naturality of `θ`,
   `θ_E = 1`.
5. Item 4 of the splitting theorem gives detection for nuclear algebras.

The facts in steps 2 and 3 are standard (Kishimoto; Kirchberg–Phillips;
equivariant Morita invariance) and were not re-read from source.

**Item 5.**
- By item 1, failure of strong approximate innerness forces `θ ≠ 1`.
- In the splitting theorem `θ − 1 = (θ − 1)(1 − e)`, so `(1 − e)E ≠ 0`, and it
  is a phantom.
- By `zp-detection-equals-meyer-nadareishvili-sufficiency`, its existence is the
  failure of the converse there. That node is not a formal requirement of this
  route, since item 5 only restates it.
