---
rg: 2
id: eventually-periodic-twisted-affine-hosts-polynomial-wp-proof
kind: route
title: Pass to the finite-index subgroup μ^m A, where the twist is conjugation, and induce the affine action to an untwisted host
target: eventually-periodic-twisted-affine-hosts-have-polynomial-wp
requires: [untwisted-abelian-affine-hosts-have-polynomial-word-problem]
artifacts:
  - research/artifacts/fp-self-similar-hard-wp-swarm-2026-09-16.md
---

Direct proof (2026-09-17, lane sw-010). Notation as in the target.

## Step 1: the twist is a homomorphism of filtration-preserving automorphisms

For `γ in Γ` we have `γ(μA) = μA`, so `σ(γ)(a) = μ^(-1)(γ(μa))` is defined on `A`.

- **Automorphism.** It is injective, and surjective because `γ(μA) = μA`.
- **Filtration.** `σ(γ)(μ^k A) = μ^(-1)γ(μ^(k+1)A) = μ^k A`.
- **Homomorphism.** `σ(γγ') = μ^(-1)γ μ μ^(-1) γ' μ = σ(γ)σ(γ')`, since `γ'μA ⊆ μA`.
- **Iterates.** By induction, `σ^m(γ) = μ^(-m)γμ^m`, i.e. `γ μ^m = μ^m σ^m(γ)`.

## Step 2: on `B = μ^m A` the action is untwisted

Put `ν = μ^P δ`, `Γ_1 = σ^m(Γ_0)` and `B = μ^m A`.

- **`ν` commutes with `Γ_1`.** For `γ in Γ_0`, write `γ_1 = σ^m(γ)`. By (EP) and Step 1,
  `γ_1 μ^P = μ^P σ^P(γ_1) = μ^P σ^(m+P)(γ) = μ^P δ γ_1 δ^(-1)`. Hence
  `γ_1 ν = γ_1 μ^P δ = μ^P δ γ_1 = ν γ_1`.
- **Filtration of `ν`.** `δ` preserves every `μ^j A`, so by induction `ν^k A = μ^(Pk) A`.
  Thus `ν` is injective, `A/νA = A/μ^P A` is finite, and `∩_k ν^k A = 0`.
- **Restriction to `B`.** Every `γ in Γ` preserves `B`, and `γ|_B = μ^m σ^m(γ) μ^(-m)`,
  where `μ^m: A -> B` is a bijection.
- **Transported endomorphism.** Put `ν_B = μ^m ν μ^(-m): B -> B`.
  - `(B, ν_B)` is isomorphic to `(A, ν)` through `μ^m`. So `ν_B` is injective,
    `B/ν_B B` is finite, and `∩_k ν_B^k B = 0`.
  - For `γ in Γ_0`, `γ|_B` commutes with `ν_B`, because `σ^m(γ)` commutes with `ν`.
- **The restriction group.** Let `Δ = {γ|_B : γ in Γ}`, the image of the homomorphism
  `Γ -> Aut(B)`, and `Δ_0` the image of `Γ_0`. Then `[Δ : Δ_0] <= [Γ : Γ_0]`, and `Δ_0`
  commutes with `ν_B`.

## Step 3: induce the affine action

`B` has finite index `s = |A/μ^m A|` in `A`. Fix coset representatives `c_1, ..., c_s`
and identify `A` with `{1, ..., s} x B` by `c_i + b <-> (i, b)`.

**The images.** For `g = (α, γ) in A x| Γ`, acting by `x -> α + γ(x)`:

```text
g(c_i + b) = c_(π(i)) + β_i + γ|_B(b),
```

where
- `π = π_g` is the permutation of cosets induced by `g`, and
- `β_i = α + γ(c_i) - c_(π(i)) in B`.

So `g` acts on `{1, ..., s} x B` as `(i, b) -> (π(i), δ b + β_i)`, with `δ = γ|_B in Δ`.

**The host group.** Let `W` be the group of all permutations of `{1, ..., s} x B` of
the form `(i, b) -> (π(i), δ b + β_i)`, with `π in Sym(s)`, `δ in Δ` and `β in B^s`.
Write such a map as `(π, δ, β)`.

- **Composition.** `(π, δ, β)∘(π', δ', β')` sends `(i, b)` to
  `(ππ'(i), δδ' b + δβ'_i + β_(π'(i)))`, which again has this form. So `W` is a group.
- **Translations.** `N = {(id, id, β)}` is a normal subgroup isomorphic to `B^s`.
  Conjugation by `(π, δ, 0)` sends `(id, id, β')` to `(id, id, (δβ')∘π^(-1))`. This is
  a linear automorphism of `B^s`, faithful when `B != 0`.
- **Complement.** `{(π, δ, 0)} ≅ Sym(s) x Δ` meets `N` trivially, and together they
  generate `W`.
- So `W = A' x| Γ'`, where `A' = B^s` and `Γ' = Sym(s) x Δ <= Aut(B^s)`. The group `Δ`
  acts diagonally and `Sym(s)` permutes coordinates.

**(L_Z) for `W`.** Take `ν' = ν_B` diagonally on `B^s`.
- It is injective, `B^s/ν' B^s = (B/ν_B B)^s` is finite, and `∩_k ν'^k B^s = 0`.
- The finite-index subgroup `{1} x Δ_0` of `Γ'` commutes with `ν'`.

**The embedding.** `g -> (π_g, γ|_B, β(g))` is the action of `g` on `A`, transported
along the bijection `A ≅ {1, ..., s} x B`.
- So it is a homomorphism `A x| Γ -> W`.
- It is injective, because `A x| Γ` acts faithfully on `A`: `α = g(0)`, and `γ` is
  determined by `g(x) - g(0)`.

## Step 4: conclusion

By `untwisted-abelian-affine-hosts-have-polynomial-word-problem` applied to `W`,
every finitely generated subgroup of `W` has word problem in time `C*l^C + C`, and in
`F(2^n)`. In particular this holds for every finitely generated subgroup of `A x| Γ`.

**Finite-state form.**
- If `σ^(m_s + P_s)(s) = σ^(m_s)(s)` for each generator `s`, put `m = max m_s` and
  `P = lcm P_s`.
- Then `σ^(m+P)(s) = σ^m(s)` for every generator, since `σ^(m + jP_s)(s) = σ^m(s)`
  whenever `m >= m_s`.
- `σ^(m+P)` and `σ^m` are homomorphisms agreeing on generators, so they agree on `Γ`.
  This is (EP) with `δ = id` and `Γ_0 = Γ`. `∎`

## Trust surface

- Steps 1--3 are elementary and fully written out.
- Step 4 uses only the target of the `requires` edge, whose own trust surface (strong
  Gröbner bases over `Z`, or Aschenbrenner for the `F(2^n)` part) is stated there.
