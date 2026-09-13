---
rg: 2
id: edge-twist-moment-test-elementary-abelian-edges-proof
kind: route
title: The coset-wise particular solution w(x q_0) = -c_e(x) replaces the cyclic one, and nothing else in the moment test used cyclicity
target: edge-twist-moment-test-elementary-abelian-edges
requires: [edge-twist-extensions-of-triangle-colimits-moment-test]
---

We follow `edge-twist-extensions-of-triangle-colimits-moment-test-proof` and note the one step that
changes.

**Lifts as cocycles (unchanged).** A lift `φ: Λ_c -> M ⋊ Q` over `π`, with `C ↦` constants, consists of
cocycles `f_v: A_v -> M` with `f_i(x) = f_j(x) + c_e(x)·1` on `E_e`.
- `M` is free over `F_p[A_v]`, so `f_v(a) = (a-1)u_v`.
- With `w_e = u_i - u_j`, the conditions are `(x-1)w_e = c_e(x)·1` for `x ∈ E_e`, and
  `w_13 = w_12 + w_23`.
- Conversely `u_3 = 0`, `u_2 = w_23`, `u_1 = w_13` reconstruct `φ`.

None of this uses the structure of `E_e`.

**The particular solution (changed).** Let `S_e = { w : (x-1)w = c_e(x)·1 for all x ∈ E_e }`. On each
right coset `E_e q_0`, fix the base point `q_0`, and put `w_e^0(y q_0) = -c_e(y)` for `y ∈ E_e`. The action
is `(x·w)(q) = w(π(x)^{-1} q)`, so

```text
((x - 1) w_e^0)(y q_0) = w_e^0(x^{-1} y q_0) - w_e^0(y q_0) = -c_e(x^{-1} y) + c_e(y) = c_e(x),
```

using that `c_e` is a homomorphism. So `w_e^0 ∈ S_e`. The difference of two elements of `S_e` is
`E_e`-invariant, so `S_e = w_e^0 + M^{E_e}`, where `M^{E_e}` is the space of functions constant on right
cosets.

**The affine intersection (unchanged in form).** A lift exists iff
`w_13^0 - w_12^0 - w_23^0 ∈ M^{E_12} + M^{E_13} + M^{E_23}`.
- The annihilator of the right side under `<λ, w> = Σ_q λ(q) w(q)` is `Z_N`.
- `<λ, w_e^0> = -Σ_{cosets} Σ_{y ∈ E_e} c_e(y) λ(y q_0) = -μ_e^{c_e}(λ)`.

This gives (M2').

**Base points.** Moving `q_0` to `z q_0` with `z ∈ E_e` replaces `c_e(y)` by `c_e(y z^{-1}) = c_e(y) - c_e(z)`.
That changes `μ_e^{c_e}(λ)` by `c_e(z) Σ_{coset} λ = 0`.

**(M4') and (M5').** The original arguments carry over.
- *Push-forward.* It maps `Z_{N'}` into `Z_N`, and base points in `Q'` chosen over those in `Q` preserve
  every `μ_e^{c_e}`.
- *Transfer.* For index prime to `p`, `push ∘ tr` is invertible.

Neither argument used cyclicity.

**Computation form.** `Z_N = ker B` by definition. Restricted to `Z_N`, the functionals
`λ ↦ Σ_g R_τ(g) λ(g)` span `I_N` as `τ` runs over a spanning set of `Hom(E_e, F_2)` for each `e`. Their
span has dimension `rank [B; R] - rank B`. ∎
