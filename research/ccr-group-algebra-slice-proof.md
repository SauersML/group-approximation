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
is a constant `c_{ij} ∈ R`:

```text
β_B(δ) = c_{ij}^{-1} δ     for all δ ∈ T ∖ 0 .               (†)
```

The constants agree across slots at once: `β_B` does not depend on
`(i, j)`, so (†) for two pairs gives `c_{ij}^{-1}δ = c_{kl}^{-1}δ`
and the domain cancels `δ`: `c_{ij} = c` for all `i ≠ j`.  (The
audit's correction: no commutator or `1 ∈ T` argument is available or
needed here.)

**Step 4 (killing `B`, and `c` with it — binomial pigeonhole).**
`T` has finite `𝔽_q`-codimension `m` in `S`, so the map
`v ↦ (x^v mod T)` on `Aℕ^d` takes at most `q^m` values; every class
of that map with elements `v, v'` yields a **binomial**
`x^v − x^{v'} ∈ T`.  Apply (†) to a binomial: `β_B` maps it to
`x^{Bv} − x^{Bv'}` monomial-by-monomial, while `c^{-1}(x^v − x^{v'})`
must match it in `R`.  Supports are two-element sets, so either
`c·x^{Bv} = x^v` (straight) or `c·x^{Bv} = −x^{v'}` (crossed), and in
particular `c` is a single monomial `c = c₀x^u` (this DERIVES the
unit form rather than assuming it).  For any class of size ≥ 3 with
elements `v, v', v''`, a crossed matching between two of them would
force two distinct class elements equal, so the straight matching
`Bv = v − u` holds on every class of size ≥ 3 — i.e. on a cofinite
subset of `Aℕ^d` (at most `2q^m` exponents lie in smaller classes) —
and this argument is characteristic-independent (no coefficient-sign
test, safe in char 2).  Differences of a cofinite subset of `Aℕ^d`
span `A(ℤ^d) = ℤ^d`, and subtracting two straight relations gives
`B(v − v') = v − v'`: so `B = 1`, then `u = 0`, and matching
coefficients gives `c₀ = 1`, i.e. `c = 1`.

**Step 5 (killing `w`, with the determinant step).**  With `B = 1`,
`c = 1`, Step 3 reads `w E_ij w^{-1} = E_ij` for all `i ≠ j`; a
matrix over a commutative ring commuting with all off-diagonal matrix
units is scalar: `w = λI`, `λ ∈ R^×`.  This alone is NOT enough:
Laurent-monomial scalars `c₀x^u I` are fixed by `Λ`-conjugation yet
are not central in `G` (the `SL_d(ℤ)`-action moves them), so `FC = Z`
would fail without one more line.  The line: `w ∈ EL_r(R) ⊆ SL_r(R)`,
so `λ^r = det(λI) = 1`; writing `λ = c₀x^u`, `λ^r = c₀^r x^{ru} = 1`
forces `u = 0` and `c₀^r = 1`, i.e. `λ ∈ 𝔽_q^×` is a CONSTANT scalar
— fixed by every `β_B` and central in `G`.  So
`FC_Λ(G) = {λI : λ ∈ 𝔽_q^×, λ^r = 1} = Z`, and every element of `Z`
has orbit size one.  ∎ (Steps 3–4 are where `1 ∈ S` and the domain
property carry the rigidity; no (T), no trace, no ultraproduct.
Even before the determinant step, the parent claim's CONSEQUENCE was
never at risk: any scalar `λI` commutes with all of `EL_r(R)`, hence
with the `σ(Γ)`-generators, so `σ(Λ)' ∩ L(G) ⊆ σ(Γ)' ∩ L(G)` holds
for the scalar-supported part regardless.)

**Scope note.**  Step 0 is the only place the ambient `M` appears,
and it needs only that `σ` extends to an embedding of `L(G)` with
`σ(λ)u_gσ(λ)^* = u_{λgλ⁻¹}` — automatic for the group elements of any
trace-preserving representation of `G`.  Everything downstream of
Step 0 is finite group-and-ring theory.
