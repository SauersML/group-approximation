---
rg: 2
id: ccr-group-algebra-slice
kind: claim
title: The group-algebra slice of compressor-commutant rigidity holds for every embedding
distinct_from:
  ccr-for-coordinate-collapsing-models: that proves full (CCR) for a special class of representations (coordinatewise, image-collapsing); this proves a slice of (CCR) — elements of L(G) only — for ALL representations, by pure group theory with no Kazhdan input.
  kt-centralizer-normalization-hs: that is the full question, whose remaining content is now confined to x ∈ M outside L(G); this closes every group-algebra-supported counterexample channel, including the centralizer and finite-conjugation-orbit templates.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**Proposition.**  For the Kun–Thom pair (`Γ = EL_r(𝔽_q[x₁…x_d])` inside
`G = EL_r(R) ⋊ SL_d(ℤ)`, `r ≥ 3`, compressor `t` with
`Λ = tΓt⁻¹ = EL_r(S)` for the compressed monomial subalgebra
`S ≅ 𝔽_q[y₁…y_d]`):

```text
FC_Λ(G) := { g ∈ G : the Λ-conjugation orbit of g is finite } = Z ,
```

the central scalars.  Consequently, for EVERY trace-faithful
`σ : G → U(M)` into a tracial ultraproduct,

```text
σ(Λ)' ∩ L(G)  =  σ(Γ)' ∩ L(G)  =  Z(L(G)) ,
```

i.e. the group-algebra slice of (CCR) holds unconditionally: an
element of `L(G)` commuting with the compressed copy is central, so it
commutes with all of `Γ` (indeed all of `G`).

**Why this matters.**  An `x ∈ σ(Λ)' ∩ L(G)` has coefficient function
constant on `Λ`-conjugation orbits; being `ℓ²`, it is supported on the
finite-orbit part `FC_Λ(G)`.  So any group-algebra-supported
counterexample to (CCR) would be exactly a finite `Λ`-orbit that `Γ`
moves — including the two simplest templates: a `g ∈ C_G(Λ) ∖ C_G(Γ)`
(orbit of size 1) and a `Γ`-noninvariant finite orbit sum.  The
proposition kills the entire channel: there are no nontrivial finite
`Λ`-orbits at all.  The remaining content of
`kt-centralizer-normalization-hs` is thereby pushed entirely outside
the group algebra, into `M ⊖ L(G)` — the genuinely ultraproduct part
of the commutant — matching the excess-commutant localization already
recorded there.

**Why it is true (proof sketch, elementary; full detail in the node
body of the proof route below).**  The load-bearing fact is that the
compressed subring `S` still contains the constants `𝔽_q`.

1. *Finite orbit forces transvection commutation on finite index.*
   If `g` has `Λ`-orbit of size `N`, then for each `i ≠ j` the map
   `s ↦ e_ij(s) g e_ij(s)⁻¹` on `S` takes at most `N` values, so
   `T_ij = {δ : e_ij(δ) commutes with g}` is an additive subgroup of
   index ≤ `N`.  Pass to the finite-index intersection `T`.
2. *Transvection rigidity over a domain.*  Writing `g = (w, B)`,
   commutation with `e_ij(δ)` for `δ ∈ T` reads
   `w e_ij(β_B(δ)) w⁻¹ = e_ij(δ)`, forcing
   `w E_ij w⁻¹ = (δ/β_B(δ)) E_ij` with a ratio independent of `δ`;
   since `β_B` permutes monomials and `T` has finite codimension over
   `𝔽_q`, a leading-monomial comparison forces `B = 1` and ratio `1`,
   and then `w` commutes with every matrix unit, so `w` is scalar.
3. Central scalars obviously have orbit size one, giving equality.

No property (T), no trace condition, no ultraproduct structure is
used: the slice is closed by ring-theoretic rigidity alone.

**Fences.**  This decides nothing about `x ∈ M` outside `L(G)` — the
full (CCR) and the endgame remain open exactly there.  The proof uses
`1 ∈ S` (compressions by `SL_d(ℤ)`-monoid maps fix the constants); a
hypothetical compression destroying the constants would evade step 1's
rigidity and is outside scope.
