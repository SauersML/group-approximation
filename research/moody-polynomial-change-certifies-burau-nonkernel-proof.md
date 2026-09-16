---
rg: 2
id: moody-polynomial-change-certifies-burau-nonkernel-proof
kind: route
title: "The loop around the arc pairs with alpha to (1 − t^s) times the Moody polynomial, and braids act on its class through Burau"
target: moody-polynomial-change-certifies-burau-nonkernel
requires: []
artifacts:
  - research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md
---

Full proof: artifact §§1–5 (Theorem A with `𝔞 = 0`, Corollary A1). This is the write-up that the
claim's own "Still to do" asks for.

**Setting.** `D̃ → D_n` is the infinite cyclic cover for total winding `φ`, with base-point fibre
`P̃_* = π^{-1}(p_*)`, and `H = H_1(D̃, P̃_*)`. Fix a lift `α̃` of the open arc `α°`.

1. **Intersection form (§2).**
   - Take a closed tubular neighbourhood `N` of `α°` that misses `∂D`. For each `ℓ`, collapse
     everything outside `t^ℓ Ñ` to one point. This gives a map of pairs
     `f_ℓ : (D̃, P̃_*) → (S^1, pt)`.
   - Put `I(x) = Σ_ℓ (f_ℓ)_*(x) t^ℓ`. The sum is finite, and `I(tx) = tI(x)`.
   - On a path transverse to the lifts of `α°`, `(f_ℓ)_*` is the signed count of crossings with
     `t^ℓ α̃`.
2. **Loop class (§3).** For an arc `A` from `p_*` to `p`, let `c_A` go out along `A`, once around
   a small counterclockwise circle about `p`, and back along a push-off. Let `c̃_A` be its lift
   from `p̃_*`.
   - The outward half contributes `Σ_i ε_i t^{k_i} = 𝕄(α, A)`.
   - The circle contributes `0` and shifts the sheet by `t^s`.
   - The return half contributes `−t^s 𝕄(α, A)`.
   - So `I([c̃_A]) = (1 − t^s) 𝕄(α, A)`, with `s = ±1` depending only on the choice of generator
     `t`.
3. **Burau action (§4).** A homeomorphism `h` fixing `∂D` preserves `φ`. So it lifts to `h̃`
   fixing `p̃_*`, commuting with `t` and preserving `P̃_*`, and `h̃_*` depends only on the
   mapping class.
   - `D_n` retracts onto a wedge of circles `x_1, ..., x_n`, so `H` is free on the lifts `e_j`,
     and `[γ̃] = Σ_k φ(∂γ/∂x_k) e_k` (Fox).
   - By Artin's formula (`σ_i ↦ A_i^{±1}` on `π_1`; Birman 1974, Ch. 1, locator not re-checked)
     and direct Fox calculus, `J_{A_i} = ρ_n(σ_i)`.
   - So the matrix of `h̃_*` is `ρ_n(w')`, possibly with `t ↦ t^{-1}`, with `w'` one of `w`,
     `rev w`, `mirror w`, `rev mirror w`.
   - `ρ_n(w)^T = D ρ_n(rev w) D^{-1}` for `D = diag(1, t, ..., t^{n−1})`, and
     `ρ_n(mirror w) = D^{-1} (ρ_n(w)^{-1})^T D`.
   - Hence `ρ_n(Ψ) = I` implies `h̃_{Ψ,*} = id` in every convention.
4. **Naturality (§5).** A homeomorphism `k` carries a small disk about `p_3` to one about `k(p_3)`.
   So `k ∘ c_β ≃ c_{k(β)}` rel `p_*`, and `[c̃_{k(β)}] = k̃_*[c̃_β]`.
5. **Conclusion.** Suppose `Ψ ∈ ker ρ_n`, and realize `Ψ` by `h` and `Γ` by `g`. Whichever
   composition order defines `(β_*^3)ΨΓ`:
   - `[c̃_{(β_*^3)ΨΓ}]` is `g̃_* h̃_* x` or `h̃_* g̃_* x`, where `x = [c̃_β]`;
   - either way it equals `g̃_* x = [c̃_{(β_*^3)Γ}]`.
   - Applying `I` gives `(1 − t^s) 𝕄_{ΨΓ} = (1 − t^s) 𝕄_Γ`. `Z[t^{±1}]` is a domain, so
     `𝕄_{ΨΓ} = 𝕄_Γ`.
   - Contrapositive: `𝕄_{ΨΓ} ≠ 𝕄_Γ` implies `Ψ ∉ ker ρ_n`. ∎

**Remarks.**
- With the preprint's normalization (first crossing gets exponent `0`), the polynomials are
  compared only up to units `±t^c`. The criterion holds a fortiori.
- The proof above is for the unreduced `ρ_n`, as in the root node. The reduced Burau kernel is the
  same (`burau-kernel-restricts-along-strand-inclusion`), but this proof does not use that.
- Imported input: Artin's formula for the half-twist action on `π_1(D_n, p_*)` (classical).

**Checks.** For the braid `Φ_0` of `burau-minus-one-kernel-meets-brunnian-four-braids`:
- check 6 of `experiments/zp-burau-parity-t-minus-one-2026-09-16/burau_minus_one.py` computes the
  Fox Jacobians of the Artin automorphism, for both twist directions and both composition orders;
- check 2 verifies the transpose identity.
