---
rg: 2
id: flexible-hs-kazhdan-kernel-quotient-proof
kind: route
title: Pull back, stabilize, push the corner into the kernel-fixed subspace with a Kazhdan pair, absorb the defect trivially
target: flexible-hs-stability-passes-to-kazhdan-kernel-quotients
requires: []
---

## Direct proof

**Notation.**
- `q: Γ -> Q` is the quotient map.
- `||·||_HS` is the unnormalized Hilbert--Schmidt norm, so `||X||_(2,d) = d^(-1/2) ||X||_HS` on `M_d`.
- Every `o(·)` is as `n -> ∞`, for a fixed group element.

1. **Pull back.** Let `σ_n: Q -> U(d_n)` be an asymptotic representation. Then
   `π_n = σ_n ∘ q` is an asymptotic representation of `Γ`. For `k ∈ N`,
   `||π_n(k) - I||_(2,d_n) -> 0`, because `σ_n(1)` is unitary and asymptotically
   idempotent.
2. **Stabilize.** Flexible stability of `Γ` gives genuine representations
   `ρ_n: Γ -> U(H_n)`, with `H_n = C^(D_n) ⊇ V_n = C^(d_n)`, such that
   `||π_n(g) - P ρ_n(g) P||_HS = o(√d_n)`. Here `P = P_n` projects onto `V_n`.
3. **The corner almost commutes.** For each `g`,
   `||P ρ_n(g) P||_HS >= ||π_n(g)||_HS - o(√d_n) = √d_n - o(√d_n)`. Since `ρ_n(g)` is
   unitary, `||(1-P) ρ_n(g) P||_HS^2 = d_n - ||P ρ_n(g) P||_HS^2 = o(d_n)`.
4. **The kernel acts almost trivially on the corner.** For `k ∈ N`,
   `||(ρ_n(k) - 1) P||_HS <= ||(1-P) ρ_n(k) P||_HS + ||P ρ_n(k) P - π_n(k)||_HS
   + ||π_n(k) - I||_HS = o(√d_n)`.
5. **Kazhdan averaging.** Let `(S_N, κ)` be a Kazhdan pair for `N`, and let `E_n` be
   the projection onto the `ρ_n(N)`-fixed vectors. Take `v ∈ H_n` and put
   `w = (1-E_n)v`. Then `w` lies in an `N`-invariant subspace with no nonzero
   invariant vector, and `ρ_n(s)w - w = ρ_n(s)v - v` for `s ∈ S_N`. So
   `||(1-E_n)v||^2 <= κ^(-2) Σ_(s ∈ S_N) ||ρ_n(s)v - v||^2`. Summing over an
   orthonormal basis of `V_n`, step 4 gives `||(1-E_n) P||_HS = o(√d_n)`.
6. **The fixed subspace carries a representation of `Q`.** `E_n H_n` is
   `ρ_n(Γ)`-invariant because `N` is normal, and `N` acts trivially on it. So
   `ρ_n` restricts to a genuine representation `λ'_n` of `Q` on `E_n H_n`.
7. **Move the corner in.** Put `T = E_n P: V_n -> E_n H_n`. Then:
   - `||T - P||_HS = ||(1-E_n)P||_HS = o(√d_n)`;
   - `||T*T - P||_HS = ||P(1-E_n)P||_HS <= ||(1-E_n)P||_HS = o(√d_n)`;
   - `|| |T| - P ||_HS <= ||T*T - P||_HS`, by `|√x - 1| <= |x - 1|` on `[0,1]`.

   Write `T = W|T|`. On `K_n = ker T` we have `(1-E_n)v = v`, so
   `m_n = dim K_n <= ||(1-E_n)P||_HS^2 = o(d_n)`.

   Let `J: V_n -> E_n H_n ⊕ C^(m_n)` equal `W` on `K_n^⊥`, and on `K_n` be an
   isometry onto `C^(m_n)`. Then `J` is an isometry, and
   `||J - T||_HS^2 <= || |T| - P ||_HS^2 + m_n = o(d_n)`. So `||J - ι||_HS = o(√d_n)`,
   where `ι` is the inclusion of `V_n` in `H_n ⊕ C^(m_n)`.
8. **Compare.** Let `λ_n = λ'_n ⊕ 1_(m_n)`. It is a genuine representation of `Q` on
   `K'_n = E_n H_n ⊕ C^(m_n)`. Write `R(g) = ρ_n(g) ⊕ 1`. Since `J` maps into `K'_n`,
   `J* λ_n(q(g)) J = J* R(g) J`, and `ι* R(g) ι = P ρ_n(g) P`. So

   ```text
   ||J* λ_n(q(g)) J - σ_n(q(g))||_HS <= 2 ||J - ι||_HS + ||P ρ_n(g) P - π_n(g)||_HS = o(√d_n).
   ```

   Identify `K'_n` with `C^(D'_n)` by a unitary taking `J V_n` onto the first `d_n`
   coordinates. Since `J` is isometric, `D'_n = dim K'_n >= d_n`. Every `x ∈ Q` is
   some `q(g)`, so this is flexible stability for `σ_n`. ∎
