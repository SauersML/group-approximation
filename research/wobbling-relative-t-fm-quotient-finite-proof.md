---
rg: 2
id: wobbling-relative-t-fm-quotient-finite-proof
kind: route
title: "The quotient map by a relative-(T) normal subgroup is a Kazhdan homomorphism, so FM lifts from the quotient to Γ, and FM groups have finite image in wobbling groups of subexponential growth"
target: wobbling-relative-t-pairs-with-fm-quotient-are-finite
requires:
  - wobbling-normal-relative-t-subgroups-are-locally-finite
---

Notation as in the target. All quotations are from Cornulier, arXiv:1308.1318v3.

## Imports (verbatim)

- **Example 2.7.** "if N is a closed normal subgroup of H, then the quotient homomorphism
  H → H/N is Kazhdan if and only (H, N) has relative Property T."
- **Theorem 6.12.** "Let π : H → Q be a homomorphism with dense image between locally compact
  groups. Suppose that π is a Kazhdan homomorphism (§2.3). Let (P) be one of the properties: dFH,
  dFH, FM, FM'. Then H has Property (P) if and only Q has Property (P)."
- **Proposition 5.6** (as stated in §1, item (4)). "If G is a locally compact group with Property
  FM, then it is compactly generated. In particular, if G is discrete then it is finitely
  generated."
- **Theorem 7.1(2).** "Let Γ be a finitely generated group. [...] (2) if Γ has Property FM and X is
  a discrete metric space of uniformly subexponential growth, then every homomorphism Γ → Wob(X)
  has a finite image." Here uniformly subexponential growth means
  `lim_n sup_x #B_X(x, n)^{1/n} = 1`, and `Wob(X)` is the group of bounded-displacement
  permutations of `X`.

Relative (T) in Cornulier's Example 2.7 is the usual one: every unitary (equivalently, by the
standard complexification, orthogonal) representation of `Γ` almost having invariant vectors has a
nonzero `H`-invariant vector. This is the definition in the target.

## Step 1: Γ has FM and is finitely generated

`Γ` is discrete, so `H` is closed and the quotient map `π : Γ → Γ/H` is a surjective, hence dense,
homomorphism of locally compact groups. By Example 2.7 it is a Kazhdan homomorphism, because
`(Γ, H)` has relative (T). Since `Γ/H` has FM, Theorem 6.12 with `(P) = FM` gives FM for `Γ`. By
Proposition 5.6, `Γ` is finitely generated. This is item 1.

(Self-contained check of finite generation, for discrete `Γ`. If `Γ` were not finitely generated,
every finitely generated `Λ ≤ Γ` would have infinite index. Let `Y = ⊔_Λ Γ/Λ` over the finitely
generated subgroups, directed by inclusion, and let `m` be a limit along an ultrafilter on this
directed set, containing all the cones `{Λ : Λ ⊇ Λ_0}`, of the Dirac masses at the cosets `Λ`. Each
`γ` lies in `Λ` for all `Λ` in the cone of `⟨γ⟩`, and fixes the point `Λ` there. So `m` is
`Γ`-invariant, while every orbit `Γ/Λ` is infinite. This contradicts FM.)

## Step 2: finite image in W(Z)

`Z` with the usual metric has `#B(x, n) = 2n + 1`, so it has uniformly subexponential growth, and
`Wob(Z) = W(Z)`. `Γ` is finitely generated with FM, so Theorem 7.1(2) gives item 2 for `Y = Z`
and for every other `Y` of uniformly subexponential growth.

## Step 3: finite image in [[X]]

Fix `x_0 ∈ X` with dense `σ`-orbit and identify the orbit with `Z` by `k ↦ σ^k x_0`. For
`f ∈ [[X]]` with continuous cocycle `k_f`, `f(σ^k x_0) = σ^{k + k_f(σ^k x_0)} x_0`. So `f` acts on
the orbit as a bijection of `Z` with displacement at most `max |k_f| < ∞`. This gives a homomorphism
`ι : [[X]] → W(Z)`. It is injective: if `ι(f) = 1`, then `f` fixes a dense set pointwise, and `f`
is continuous, so `f = id`. For `ρ : Γ → [[X]]`, item 2 applied to `ι ∘ ρ` gives finite image, and
`ι` is injective. This is item 3.

## Step 4: class kill

Let `Γ ≤ [[X]]` or `Γ ≤ W(Z)`, and let `H ⊴ Γ` be infinite with `(Γ, H)` relative (T).
- If `Γ/H` had FM, then by item 3 (or item 2) applied to the inclusion, `Γ` would be finite, and so
  would `H`. That is a contradiction.
- If `Γ/H` were amenable, then `Γ` would be amenable. This is where
  `wobbling-normal-relative-t-subgroups-are-locally-finite` is used: `H` is locally finite, hence
  amenable, and amenability is closed under extensions. The quasi-regular representation
  `ℓ²(Γ)` then almost has invariant vectors, so it has a nonzero `H`-invariant vector. A nonzero
  `ℓ²` function constant on the infinite `H`-cosets is impossible, so `H` is finite. That is a
  contradiction.

This is item 4. □

## Where the argument stops

- The kill needs FM of the **quotient**. For `Γ_p = EL_2(F_p[t,t^-1]) ⋉ F_p[t,t^-1]^2`, the
  quotient `SL_2(F_p[t,t^-1])` is an irreducible lattice in
  `SL_2(F_p((t))) × SL_2(F_p((t^-1)))`. Both factors are rank-one groups over non-Archimedean local
  fields. They have FM (Prop. 1.8) but not (T), so Theorem 1.13 does not apply. FM for this lattice
  is open. It is the tree-product analogue of the case Cornulier calls hard (Haagerup factors).
- A quotient without FM but with (T)-like rigidity on finite quotients (property `(τ)`) is not
  reached by this route. That case needs a separate argument through finite orbits.
