---
rg: 2
id: o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences-proof
kind: route
title: Absorb the quasi-free O_infinity model to get fixed and eigen isometries, then run Cuntz comparison in the fixed central sequence algebra
target: o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences
requires: [outer-actions-on-o2-kk-g-contractible-iff-rokhlin]
---

**Sources (read 2026-09-13 from ghostscript text extractions on MSI).**
Szabó, *Strongly self-absorbing C\*-dynamical systems*, arXiv:1509.08380:
* Theorem 5.15(2): for `G` finite and `A` separable, unital, nuclear and
  simple, "(A, α) ≅ (A ⊗ O_∞, α ⊗ γ), if A is purely infinite and α is
  pointwise outer".
* Remark 5.14: for finite `G`, Goldstein--Izumi show that `γ` is conjugate to
  any faithful quasi-free `G`-action on `O_∞`.
* Example 5.10: any quasi-free action of a finite group on `O_∞` is strongly
  self-absorbing.
* Theorem 3.7, (ii) ⟹ (iii): if `(D, γ)` is strongly self-absorbing and `α` is
  cocycle conjugate to `α ⊗ γ`, there is a unital equivariant
  \*-homomorphism `(D, γ) → (F_(∞,α)(A), α̃)`.  For finite `G` and unital `A`,
  `F_(∞,α)(A) = A_∞ ∩ A'`.

Hirshberg--Winter Theorem 3.3 and Szabó Corollary 3.8 are quoted in
`outer-actions-on-o2-kk-g-contractible-iff-rokhlin-proof`.

**Standard input, not re-read.**  (CU) In a unital C\*-algebra, two properly
infinite full projections with the same `K_0`-class are Murray--von Neumann
equivalent (Cuntz).  Hence a unital properly infinite algebra with `[1] = 0`
contains `O_2` unitally.  Take orthogonal isometries `t_1, t_2`, compare
`t_1t_1* + t_2t_2*` with `1`, and conjugate the `t_i` back.

**Item 1.**
* By Theorem 5.15(2), `α ≅ α ⊗ γ`, with `γ` the quasi-free action from
  `λ ⊗ 1` on `H = ℓ²G ⊗ ℓ²N`, which is faithful.  Theorem 3.7 gives a unital
  equivariant `(O_∞, γ) → (A_∞ ∩ O_2', α_∞)`, where `O_∞ = O(H)`.
* `S_ξ*S_η = ⟨ξ, η⟩` and `γ_g(S_ξ) = S_((λ_g ⊗ 1)ξ)`.
* The vectors `ξ_n = |G|^(−1/2) Σ_g δ_g ⊗ e_n` are orthonormal and invariant.
  Their isometries are fixed and have orthogonal ranges, so they generate a
  unital `O_∞` in `F^α`.
* For abelian `G`, `η_χ = |G|^(−1/2) Σ_g χ̄(g) δ_g ⊗ e_1` gives
  `α_g(S_(η_χ)) = χ(g) S_(η_χ)`.
* If `α_g(v) = χ(g)v` and `x ∈ F^α`, then `α_g(v x v*) = v x v*`, and `v x v*`
  commutes with `O_2`.  So `Ad(v)` maps `F^α` into itself.

**Item 2.**
* *Rokhlin ⟹ embedding.*  `O_2 ≅ O_2 ⊗ O_2` gives a central sequence of
  unital embeddings, and Hirshberg--Winter Theorem 3.3 puts `O_2` unitally in
  `F^α`.
* *Embedding ⟹ `[1] = 0`.*  `1 = s_1s_1* + s_2s_2*` with `s_is_i* ~ 1` gives
  `[1] = 2[1]`.
* *`[1] = 0` ⟹ embedding.*  By item 1 and (CU).
* *Embedding ⟹ contractible.*  Szabó Corollary 3.8 gives
  `α ≃_cc α ⊗ id_(O_2)`, which is contractible, as in item 1 of the
  Rokhlin characterization.
* *Contractible ⟹ Rokhlin.*  Item 2 of that node.

**Item 3.**  For finite `G`, `(A ⋊ G)_∞ = A_∞ ⋊ G`, since `A ⋊ G = ⊕_g A u_g`
with equivalent norms.  The dual action scales `u_g` and fixes `A_∞`, so its
fixed points in `(A ⋊ G)_∞` are `A_∞`.  An element `x ∈ A_∞` commutes with
`A ⋊ G` iff it commutes with `A` and with every `u_g`, that is, iff
`x ∈ A_∞ ∩ A'` and `α_g(x) = x`.  So
`F_∞(A ⋊ G)^(α̂) = F_∞(A)^α`.  By Szabó Corollary 3.8, the first condition
of item 2 holds for `α` iff it holds for `α̂`, whether or not the algebras are
`O_2`.

**Item 4.**
* *Well defined.*  If `v, v'` are both `χ`-eigen isometries, then `w = v'v*`
  is a fixed partial isometry in `A_∞ ∩ O_2'`, hence in `F^α`, with
  `w Φ_χ(x) w* = Φ'_χ(x)`.  So `φ_χ = φ'_χ` on `K_0`.
* *Action.*  `v_χ v_ψ` is a `χψ`-eigen isometry, so `φ_χ φ_ψ = φ_(χψ)`.  A fixed
  isometry `t` gives `φ_1 = K_0(Ad t) = id`.
* *The class of `F`.*  Take `s_g = S_(δ_g ⊗ e_1)` and
  `t_χ = |G|^(−1/2) Σ_g χ(g) s_g`.  Then `α_h(t_χ) = χ̄(h) t_χ`,
  `t_χ* t_ψ = δ_(χ,ψ)`, and by orthogonality of characters
  `Σ_χ t_χ t_χ* = Σ_g s_g s_g* = F`.  Each `t_χ t_χ*` lies in `F^α` and equals
  `Φ_χ̄(1)`, so `[F] = Σ_χ φ_χ[1]`.
* *`F ~ 1` ⟹ Rokhlin.*  Let `w ∈ F^α` with `w*w = 1` and `ww* = F`.  Put
  `e_g = w* s_g s_g* w`.  These are projections in `A_∞ ∩ O_2'` with
  `Σ e_g = 1` and `α_h(e_g) = e_(hg)`.
* *Rokhlin ⟹ `Σ_(χ≠1) φ_χ[1] = 0`.*  Rokhlin gives `[1] = 0` by item 2, so
  every `φ_χ[1] = 0`.
* *`Σ_(χ≠1) φ_χ[1] = 0` ⟹ `F ~ 1`.*  The hypothesis gives `[F] = [1]`.  `F`
  dominates `t_1t_1* ~ 1`, so `F` and `1` are properly infinite and full, and
  (CU) gives `F ~ 1`.
