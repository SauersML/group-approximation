---
rg: 2
id: lifted-t-twisted-witnesses-lie-closure-proof
kind: route
title: "Adjoint transfer: Ad o sigma on the semisimple part of the Lie closure kills the centre of K(3,4), is a Z4 * Z3 representation of dimension N with T defect <= 2D, and below delta_N it is trivial; then the virtually-solvable-image lemma finishes"
target: lifted-thompson-t-twisted-witnesses-need-unbounded-lie-closure
requires: [thompson-gap-witnesses-need-nonamenable-image, thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes, thompson-t-lochak-schneps-presentation, lifted-thompson-t-is-a-quotient-of-a-brieskorn-lattice]
artifacts:
  - experiments/lifted-t-lie-closure-gap-2026-09-17/check_twisted_adjoint.py
  - experiments/lifted-t-lie-closure-gap-2026-09-17/out_check_twisted_adjoint.json
---

Notation as in the target.  All norms are operator norms, except `||·||_2`, the
Hilbert–Schmidt norm on `M_n(C)`.  Words are group products.  Maps in `T̄` compose, with the
convention of `lifted-thompson-t-is-a-quotient-of-a-brieskorn-lattice`.

## 0. `Γ̂ ≅ T̄`, and `Γ̂` has no nontrivial virtually solvable quotient

**Relators hold.**  Send `x ↦ α̃` and `y ↦ β̃`.  By (A) of the Brieskorn node:
- `α̃^4 = β̃^3 = z`, so this defines a homomorphism `K → T̄` with `c ↦ z`;
- `(β̃α̃)^5 = z^3 = α̃^12`, so `rhoP ↦ 1`.

For the commutator relators, `thompson-t-lochak-schneps-presentation` gives
`[βαβ, α²βαβα²] = 1` and `[βαβ, α²β²α²βαβα²βα²] = 1` in `T` (under both reading
conventions).

The lifts of two commuting circle maps `g, h` commute.
- `[g̃, h̃]` lifts the identity, so it equals `z^m` for some `m`.
- Then `g̃ h̃ g̃^(-1) = z^m h̃`.
- The translation number is conjugation invariant and satisfies `rot(z^m h̃) = m + rot(h̃)`.
- So `m = 0`.

Hence `rho1, rho2 ↦ 1`, and we get `q : Γ̂ → T̄`.  It is surjective, because `α̃, β̃`
generate `T̄` (item (B) of the Brieskorn node).

**Injective.**  `c` is central in `K`, hence in `Γ̂`.  Moreover

```text
Γ̂/<<c>> = <x, y | x^4, y^3, r1, r2, (yx)^5> = T
```

by Lochak–Schneps, and `q` induces this identification modulo `z`.  So
`ker q ⊂ <c̄>`.  Since `q(c̄^m) = z^m ≠ 1` for `m ≠ 0`, `q` is injective.

**Perfect.**  `K^ab = Z^2 / (4,-3) ≅ Z` via `x ↦ 3`, `y ↦ 4`.  The commutators `rho1, rho2`
map to `0`, and `rhoP ↦ 5·(4+3) - 12·3 = -1`.  So `Γ̂^ab = 0`.

**No virtually solvable quotient.**  Let `M ◁ Γ̂` with `Γ̂/M` virtually solvable, and put
`Z = <c̄>`.
- `Γ̂/MZ` is a virtually solvable quotient of `Γ̂/Z = T`.
- `T` is infinite and simple (Cannon–Floyd–Parry).
- An infinite simple group is not virtually solvable.  Otherwise the normal core of a
  finite-index solvable subgroup would be the whole group, so the group would be solvable and
  simple, hence cyclic of prime order.
- So `MZ = Γ̂`, and `Γ̂/M = MZ/M` is a quotient of `Z`, so it is abelian.
- `Γ̂` is perfect, so `Γ̂/M = 1`.

## 1. `δ_N > 0`, and the untwisted gap (1)

**`δ_N > 0`.**  For `n <= N`, `Hom(G0, U(n)) = {(A, B) : A^4 = B^3 = 1}` is compact.
- The trivial pair is isolated in it.  If `A^4 = 1` and `A ≠ 1`, some eigenvalue lies in
  `{-1, ±i}`, so `||A - 1|| >= √2`.  The same holds for `B`, with `||B - 1|| >= √3`.
- So the nontrivial pairs form a compact set.
- `D_T` is continuous on it.  If `D_T = 0`, the pair is a finite-dimensional unitary
  representation of `T`.  Its image is finitely generated and linear, hence residually finite
  (Mal'cev), so it is trivial because `T` is infinite and simple.
- Hence `min D_T > 0`.

**Imprimitive bound.**  Let `τ` be irreducible and imprimitive, with a system of `m >= 2`
blocks permuted transitively by `π : G0 → S_m`.
- If `π(r) = 1` for all relators `r`, then `π` factors through `T`.  But `T` has no nontrivial
  finite quotient, so `π` is trivial, which contradicts transitivity.
- So some `π(r)` moves a block `V_i` to an orthogonal block `V_j`.  For a unit vector
  `v ∈ V_i`, `||τ(r)v - v|| = √2`.

The inequality `D_T(τ) >= min(1/2, δ_{N_τ}/2)` of (1) is item 2 below, with `c` acting
trivially.  The final step there uses (C) of `thompson-gap-witnesses-need-nonamenable-image`
in place of the twisted computation.

## 2. The adjoint transfer, and the twisted gap (2)

Let `σ : K → U(n)` be exact, with `D = D(σ) < min(1/2, δ_N/2)`, where `N = N_σ`.

**Setting up.**  `K_σ = closure of σ(K)` is a closed subgroup of `U(n)`, so it is a compact
Lie group.  Its Lie algebra `l ⊂ u(n)` is compact, so `l = z(l) ⊕ [l, l]`, with `[l, l]`
semisimple.
- `Ad(g)X = gXg^(-1)`, for `g ∈ K_σ`, preserves `l` and `[l, l]`.
- Let `V = [l, l] + i[l, l] ⊂ M_n(C)`.  The sum is direct, since `u(n) ∩ i·u(n) = 0`.  So
  `V` is a complex subspace with `dim_C V = N`.
- `Ad(g)` preserves `V` and is unitary for `<X, Y> = tr(X* Y)`.
- Put `τ(k) := Ad(σ(k))|_V`, a unitary representation of `K` of dimension `N`.

**τ kills c.**  `σ(c)` commutes with `σ(K)`, hence with `K_σ`, hence with
`l = {X : exp(tX) ∈ K_σ for all t}`.  So `τ(c) = 1`, and `τ` factors through
`K/<<c>> = <x, y | x^4, y^3> = G0`, with `x ↦ α` and `y ↦ β`.

**Norm transfer.**  For `u ∈ U(n)` and `X ∈ M_n(C)`,

```text
||uXu^(-1) - X||_2 = ||uX - Xu||_2 <= ||(u-1)X||_2 + ||X(u-1)||_2 <= 2||u - 1|| ||X||_2.
```

So `||Ad(u)|_V - 1|| <= 2||u - 1||`.

**Relators.**
- `r1, r2` are the words `rho1, rho2` in `α, β`, so `τ(r_i) = Ad σ(rho_i)` for `i = 1, 2`.
- `(yx)^5 = rhoP · x^12 = rhoP · c^3`, and `τ(c) = 1`, so `τ(rP) = Ad σ(rhoP)`.
- Hence `D_T(τ) <= 2D < δ_N`.

**τ is trivial.**  If `N = 0` this is vacuous.  Otherwise it holds by the definition of
`δ_N`, since `dim τ = N`.

**`l` is abelian.**  `Ad(σ(K))` is trivial on `[l, l]`, hence so is its closure `Ad(K_σ)`.
- Differentiating `Ad(exp tY)`, we get `ad Y = 0` on `[l, l]` for every `Y ∈ l`.
- In particular `[[l,l], [l,l]] = 0`.
- A semisimple Lie algebra equals its derived algebra, so `[l, l] = 0`.

**Conclusion.**  `K_σ^0` is a torus of finite index in the compact group `K_σ`.  So
`σ(K) ∩ K_σ^0` is an abelian subgroup of finite index in `σ(K)`, and `σ(K)` is virtually
solvable.
- Apply (A) of `thompson-gap-witnesses-need-nonamenable-image` with `Q = K`,
  `R = {rho1, rho2, rhoP}` and `Γ = Γ̂`.  The hypotheses hold by item 0 and `D < 1/2`.
- So `σ(K)` is abelian and generated by `σ(R)`, and `σ` factors through `K^ab = Z`
  (`x ↦ 3`, `y ↦ 4`).
- Let `T` be the image of `1`.  Then `σ(x) = T^3`, `σ(y) = T^4`, `T = σ(x)^(-1)σ(y)`,
  `σ(rhoP) = T^(5·7 - 36) = T^(-1)` and `σ(c) = T^12`.
- So

  ```text
  ||σ(c) - 1|| = ||T^12 - 1|| <= 12 ||T - 1|| = 12 ||T^(-1) - 1|| <= 12 D.
  ```

**Sharpness.**  On the characters `x ↦ t^3`, `y ↦ t^4` we have `D = |t - 1|` and
`|σ(c) - 1| = |t^12 - 1| ~ 12|t - 1|`.

**Untwisted version (1).**  Run the same argument for a nontrivial `G0`-representation `τ0`
with `D_T(τ0) < min(1/2, δ_{N}/2)`, using `Q = G0` and `Γ = T`.
- `(A)` makes the image abelian, so `τ0` is a sum of characters of `G0^ab = Z/12`.
- Every nontrivial character has `D_T >= 2 sin(π/12) > 1/2`, by (C) of the same node.
- This is a contradiction.

## 3. Spectral rounding, and (3)

Let `U` be unitary with `||U^4 - μ|| <= η <= 1`, where `|μ| = 1`.
- Every eigenvalue satisfies `λ^4 = μ e^(iψ)` with `|ψ| <= πη/2`.
- So `λ` is within `|ψ|/4 <= η` of a fourth root of `μ`.
- Let `f` send each point of the circle to a nearest fourth root of `μ` (a Borel function).
- `U' = f(U)` is unitary, `U'^4 = μ`, and `||U - U'|| <= η`.

Do the same for `B` with cube roots.  This gives an exact `σ_n` with `σ_n(c) = μ_n`.
Every relator word has length at most `34`, so `D(σ_n) <= D_n + 34 η_n`.

Then (2) applies to `σ_n` with `N = N_{σ_n}`.
- Either `D(σ_n) >= min(1/2, δ_N/2)`,
- or `ε <= |μ_n - 1| <= 12 D(σ_n)`.

This gives the displayed bound.

## 4. Fixed compact group

Let `φ : K → M` with `M` a compact Lie group, and let `π_j : M → U(k_j)` be continuous.
- The closure of `π_j φ(K)` is `π_j(closure φ(K))`, since the image of a compact set is
  compact.
- Its Lie algebra is `dπ_j(m')`, where `m' = Lie(closure φ(K))`.
- So its semisimple part `dπ_j([m', m'])` has dimension `<= dim M`.

If `φ(K)` is finite or virtually solvable, the identity component of its closure is a
connected solvable compact group, hence a torus, so `N = 0`.

## Numerical sanity check

The artifacts check the identities of item 2 on random exact representations, and the
sharpness of `12`.  They also show that the factor `2` in the norm transfer is almost
attained by `Sym^1` versus `Sym^2` of an `SU(2)` pair.  See the target's "Evidence".
Nothing in the proof depends on them.
