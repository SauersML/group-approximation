---
rg: 2
id: crossed-product-fixed-point-traces-detect-leavitt-k1-proof
kind: route
title: A conjugacy-class trace built from a centralizer-invariant functional on Fix(g) takes the value -ν(1) on the nilpotent 1 - u_g, and the Leavitt K_1 detector reads it
target: crossed-product-fixed-point-traces-detect-leavitt-k1
requires:
  - leavitt-tensor-k1-sees-traces-of-nilpotent-matrices
---

Notation as in the target. As a vector space `B = ⊕_(γ ∈ Λ) LC(X, k) u_γ`, and
`(f u_γ)(h u_δ) = f (h ∘ γ^(-1)) u_(γδ)`.

**Step 0 (nilpotence).** `u_g` commutes with `1`, and `char k = p`, so
`(1 - u_g)^(p^j) = 1 - u_g^(p^j) = 1 - u_e = 0`. Hence `x = 1 - u_g` is nilpotent
in `B = M_1(B)`.

**Step 1 (the trace, case (F)).** `Fix(g)` is closed in `X`, so restriction
sends `LC(X, k)` to `LC(Fix(g), k)`. Define `τ` on each summand by

`τ(f u_γ) = ν((f ∘ k)|_(Fix(g)))` if `γ = k g k^(-1)` for some `k ∈ Λ`,
and `τ(f u_γ) = 0` if `γ` is not conjugate to `g`,

and extend linearly.

- *Well defined.* If `k g k^(-1) = k' g k'^(-1)` then `k' = k c` with
  `c ∈ C_Λ(g)`. Since `c` commutes with `g`, it maps `Fix(g)` onto itself, and
  `(f ∘ k')|_Fix = ((f ∘ k)|_Fix) ∘ c|_Fix`. The two values agree because `ν`
  is `C_Λ(g)`-invariant.
- *Linear* in `f` on each summand, hence linear on `B`.

**Step 2 (trace property).** By linearity it suffices to take `a = f u_γ` and
`b = h u_δ`. Then

`ab = f (h ∘ γ^(-1)) u_(γδ)` and `ba = h (f ∘ δ^(-1)) u_(δγ)`.

Since `δγ = γ^(-1)(γδ)γ`, the element `γδ` is conjugate to `g` iff `δγ` is.
If neither is, `τ(ab) = 0 = τ(ba)`. Otherwise write `γδ = k g k^(-1)`, so that
`δγ = k' g k'^(-1)` with `k' = γ^(-1) k`. Then

- `τ(ab) = ν( (f ∘ k) · (h ∘ γ^(-1) k) |_Fix )`;
- `τ(ba) = ν( (h ∘ γ^(-1) k) · (f ∘ δ^(-1) γ^(-1) k) |_Fix )`.

For `ξ ∈ Fix(g)` we have `δ^(-1) γ^(-1) k ξ = (γδ)^(-1) k ξ = k g^(-1) ξ = k ξ`.
So the two restricted functions are equal, and `τ(ab) = τ(ba)`. Hence
`τ([B, B]) = 0`.

**Step 3 (value on x).** `g ≠ e`, so `e` is not conjugate to `g` and
`τ(1) = τ(1 · u_e) = 0`. With `k = e`, `τ(u_g) = ν(1)`. Therefore
`τ(x) = τ(1) - τ(u_g) = -ν(1) ≠ 0`.

**Step 4 (case (M)).** Put `τ_0(f u_γ) = μ(f)` if `γ = e`, and `0` otherwise.
For `a, b` as in Step 2, both `τ_0(ab)` and `τ_0(ba)` vanish unless
`δ = γ^(-1)`. In that case `τ_0(ab) = μ(f · (h ∘ γ^(-1)))` and
`τ_0(ba) = μ(h · (f ∘ γ)) = μ((h ∘ γ^(-1) · f) ∘ γ)`. These are equal by
`Λ`-invariance of `μ`. So `τ_0([B, B]) = 0`, and `τ_0(x) = μ(1) - 0 = μ(1) ≠ 0`.

**Step 5 (detector).** Apply `leavitt-tensor-k1-sees-traces-of-nilpotent-matrices`
with `n = 1`, `m = 1`, the nilpotent `x ∈ M_1(B)` and `φ = τ` (respectively
`τ_0`). It gives a homomorphism `χ_(φ,1) : K_1(B ⊗ L) -> k` with
`χ_(φ,1)[1 + x ⊗ e_1] = φ(x) ≠ 0`. So `[1 + x ⊗ e_1] ≠ 0`. ∎

**Easiest instance.** Suppose `S ⊂ Fix(g)` is finite, `C_Λ(g)`-invariant and
`|S|` is prime to `p`. Then `ν(F) = Σ_(ξ ∈ S) F(ξ)` is `C_Λ(g)`-invariant,
because `C_Λ(g)` permutes `S`, and `ν(1) = |S| ≠ 0` in `k`.

**Remark (odd torsion, heuristic only, not claimed).** For `g` of order prime to
`p`, the element `1 - u_g` is not nilpotent, and Steps 0–5 give nothing. When
all point stabilizers are finite of order prime to `p`, the local algebras are
Maschke-semisimple. This suggests such fixed points do not obstruct vanishing,
but no proof is offered here.
