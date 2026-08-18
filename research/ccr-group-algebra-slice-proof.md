---
rg: 2
id: ccr-group-algebra-slice-proof
kind: route
title: Finite-orbit pigeonhole plus transvection rigidity over the compressed subring
target: ccr-group-algebra-slice
requires: []
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

# Finite-orbit pigeonhole plus transvection rigidity

Notation: `R = 𝔽_q[x₁^{±1}…x_d^{±1}]`, `G = EL_r(R) ⋊ SL_d(ℤ)` with
`B ∈ SL_d(ℤ)` acting by the monomial substitution `β_B(x^v) = x^{Bv}`;
`Γ = EL_r(𝔽_q[x₁…x_d])`; the compressor `t` acts through a matrix
`A ∈ SL_d(ℤ)` with `Aℕ^d ⊊ ℕ^d`, so `Λ = tΓt⁻¹ = EL_r(S)` where
`S = span_{𝔽_q}{x^v : v ∈ Aℕ^d}` is a polynomial subalgebra containing
the constants (`A·0 = 0`).

**Step 0 (reduction).**  `x = Σ c_g u_g ∈ L(G)` commutes with `σ(Λ)`
iff `c` is constant on `Λ`-conjugation orbits (conjugation permutes
the basis `{u_g}` inside `L(G)`, independently of `σ` — for `σ`
arising from an embedding of `L(G)`, `σ(λ) x σ(λ)^* = Σ c_g u_{λgλ⁻¹}`).
An `ℓ²` function constant on orbits vanishes on infinite orbits, so
`x` is supported on `FC_Λ(G)`.  It therefore suffices to prove
`FC_Λ(G) = Z` (central scalars); then `x ∈ Z(L(G))` commutes with
everything.

**Step 1 (pigeonhole).**  Let `g = (w, B) ∈ G` have `Λ`-orbit of size
`N < ∞`.  Fix `i ≠ j`.  The map `s ↦ e_ij(s)\,g\,e_ij(s)^{-1}` on `S`
takes at most `N` values, and `e_ij(s)e_ij(s')^{-1} = e_ij(s−s')`, so
`T_ij := {δ ∈ S : [e_ij(δ), g] = 1}` is an additive subgroup with
`[S : T_ij] ≤ N`.  Put `T := ⋂_{i≠j} T_ij`, still of finite index,
hence of finite `𝔽_q`-codimension in `S`.

**Step 2 (unwinding the commutation).**  In the semidirect product,
`(w,B)\,e_ij(δ)\,(w,B)^{-1} = w\,e_ij(β_B(δ))\,w^{-1}`.  So for every
`δ ∈ T` and every `i ≠ j`:

```text
w\,e_ij(β_B(δ))\,w^{-1} = e_ij(δ) .                          (★)
```

**Step 3 (constant ratio).**  For `δ ≠ 0`, (★) expands to
`w (I + β_B(δ)E_ij) w^{-1} = I + δE_ij`, i.e.
`w E_ij w^{-1} = (δ / β_B(δ)) E_ij` in `M_r(R)` (the ring is a domain
and `β_B(δ) ≠ 0`).  The left side does not depend on `δ`, so the ratio
is a constant `c_{ij} ∈ R^×`:

```text
β_B(δ) = c_{ij}^{-1} δ     for all δ ∈ T .                   (†)
```

Comparing two index pairs sharing a slot (`r ≥ 3`) and using
`[e_ik(δ), e_kj(1)] = e_ij(δ)` with `1 ∈ T` after passing to a further
finite-index subgroup if needed, the constants agree: `c_{ij} = c`.

**Step 4 (killing `B` and `c`).**  `β_B` permutes the monomials of
`R`, and `T` has finite `𝔽_q`-codimension in `S`, so for all but
finitely many `v ∈ Aℕ^d` the subgroup `T` contains an element
`τ_v = x^v + (terms with exponents in a fixed finite complement)`.
Units of `R` are `c = c₀x^u`.  Apply (†) to `τ_v` and compare
supports under the monomial bijection `x^μ ↦ x^{Bμ}`: the support of
`β_B(τ_v)` is `B(supp τ_v)` with unchanged coefficients, while the
support of `c^{-1}τ_v` is `supp(τ_v) − u` with coefficients scaled by
`c₀^{-1}`.  Taking `v` outside the finite bad set and lexicographically
extremal in its support forces `Bv = v − u` for cofinitely many
`v ∈ Aℕ^d`; two such relations subtract to `B(v−v') = v−v'` on a
spanning set of `ℤ^d` (the differences of `Aℕ^d` span, `A ∈ SL_d`),
so `B = 1`, then `u = 0` and `c₀ = 1` (coefficients in `𝔽_q` match),
i.e. `c = 1`.

**Step 5 (killing `w`).**  With `B = 1`, `c = 1`, Step 3 reads
`w E_ij w^{-1} = E_ij` for all `i ≠ j`; a matrix over a commutative
ring commuting with all off-diagonal matrix units is scalar:
`w = λI`, `λ ∈ R^×`.  Scalars are central in `GL_r(R)` and are fixed
by the `SL_d(ℤ)`-action only up to `β`, but as elements of `G` the
pair `(λI, 1)` has `Λ`-orbit `{(β-images…)}` — conjugation by
`e_ij(s) ∈ Λ` fixes `(λI, 1)` exactly (same `EL_r(R)`-component
computation with `B = 1`), and conjugation by all of `Λ ≤ EL_r(R)`
leaves scalars fixed.  So `FC_Λ(G) = {(λI, 1)} = Z`, and every
element of `Z` has orbit size one.  ∎ (Steps 3–4 are where `1 ∈ S`
and the domain property carry the rigidity; no (T), no trace, no
ultraproduct.)

**Scope note.**  Step 0 is the only place the ambient `M` appears,
and it needs only that `σ` extends to an embedding of `L(G)` with
`σ(λ)u_gσ(λ)^* = u_{λgλ⁻¹}` — automatic for the group elements of any
trace-preserving representation of `G`.  Everything downstream of
Step 0 is finite group-and-ring theory.
