---
rg: 2
id: char-p-untwisted-self-similar-affine-groups-linear-proof
kind: route
title: Expand elements in nu-adic digits, read commuting endomorphisms as power-series matrices, and induce from the commuting subgroup
target: char-p-untwisted-self-similar-affine-groups-are-linear
requires: []
artifacts:
  - research/artifacts/fp-self-similar-hard-wp-swarm-2026-09-16.md
---

Direct proof (2026-09-16, lane `swarm-fp-simple-groups-with-arbitrar`). The same
proof, with remarks, is §§2--6 of the artifact.

Notation:
- `Λ = F_p[[t]]` and `Λ_k = F_p[t]/(t^k)`;
- `ε_j` is the standard basis of `Λ^r`;
- every additive map of `A` is `F_p`-linear.

## Step 1: layers

For `j >= 0`, `ν^j` induces a map `A/νA -> ν^j A/ν^(j+1) A`.
- It is surjective.
- It is injective: `ν^j a = ν^(j+1) b` gives `a = νb`, because `ν^j` is injective.

So `dim A/ν^k A = kr`.

## Step 2: digits

Fix `e_1, ..., e_r in A` whose classes form a basis of `A/νA`. For
`f in F_p[t]^r`, write `f(ν)e = Σ_i f_i(ν) e_i`. Define
`π_k: Λ_k^r -> A/ν^k A` by `π_k(f) = f(ν)e mod ν^k A`.

- **Well defined.** `ν^k e_i in ν^k A`.
- **Surjective,** by induction on `k`. Write `a - Σ c_i e_i = ν a'` with
  `c in F_p^r`. If `a' ≡ g(ν)e mod ν^(k-1) A`, then
  `a ≡ (c + tg)(ν)e mod ν^k A`.
- **Bijective.** Both sides have dimension `kr` (Step 1).

## Step 3: the map ι

The inverses `π_k^(-1)(a mod ν^k A)` are compatible under truncation, because
`π_(k+1)` reduces to `π_k`. Let `ι(a) in Λ^r` be their limit.

- **Additive.** Each `π_k^(-1)` is linear.
- **Filtration.** `ι(a) ≡ 0 mod t^k` iff `a in ν^k A`. So `ι` is injective, since
  `∩ ν^k A = 0`.
- **Shift.** If `a ≡ f(ν)e mod ν^k A`, then `νa ≡ (tf)(ν)e mod ν^(k+1) A`, so
  `ι(νa) = t ι(a)`. Combined with additivity, `ι(g(ν)x) = g(t)ι(x)` for every
  `g in F_p[t]` and `x in A`.
- **Digits.** `ι(f(ν)e) = f` for `f in F_p[t]^r`. In particular `ι(e_j) = ε_j`.

## Step 4: the matrices M(e), proving (a)

For `e in End_ν(A)`, let `M(e) in M_r(Λ)` have `j`-th column `ι(e e_j)`.

- **The formula `ι(ea) = M(e)ι(a)`.** Fix `k` and write `a = f(ν)e + ν^k b`.
  Since `e` commutes with `ν`, we have `ea = Σ_j f_j(ν)(e e_j) + ν^k(eb)`. By
  Step 3:
  - `ι(ea) = M(e) f + t^k ι(eb)`;
  - `M(e)ι(a) = M(e) f + t^k M(e) ι(b)`.

  The two agree modulo `t^k` for every `k`.
- **Ring homomorphism.** `M` is additive. From `ι(ee'a) = M(e)M(e')ι(a)` at
  `a = e_j`, we get `M(ee') = M(e)M(e')`. Also `M(id) = I` and
  `M(ν) = tI`, because `ι(ν e_j) = tε_j`.
- **Injective.** `M(e) = 0` forces `ι(ea) = 0` for all `a`, so `e = 0`.

## Step 5: affine embedding, proving (b) when Γ_0 = Γ

- **Invertible linear parts.** If `γ in Aut(A)` commutes with `ν`, so does
  `γ^(-1)`. Then `M(γ)M(γ^(-1)) = I`, so `M(γ) in GL_r(Λ)`.
- **The map.** Put `Φ(a,γ) = [[M(γ), ι(a)], [0,1]]`.
- **Homomorphism.** The product `Φ(a,γ)Φ(a',γ')` has blocks `M(γγ')` and
  `M(γ)ι(a') + ι(a) = ι(a + γ(a'))`. So it equals `Φ((a,γ)(a',γ'))`.
- **Injective.** `Φ(a,γ) = I` forces `ι(a) = 0` and `M(γ) = M(id)`, so `a = 0` and
  `γ = id`.

## Step 6: finite index, proving (b) in general

Put `G = A x| Γ`, `G_0 = A x| Γ_0` and `ρ = Φ` on `G_0`. Then `[G:G_0] = d`.

- **Cosets.** Fix left coset representatives `g_1, ..., g_d`. For `g in G`, write
  `g g_j = g_(π_g(j)) h_j(g)` with `h_j(g) in G_0`.
- **The block matrix.** Let `Ψ(g)` have block `ρ(h_j(g))` at `(π_g(j), j)` and
  zero blocks elsewhere.
- **Homomorphism.**
  `g g' g_j = g_(π_g π_(g')(j)) h_(π_(g')(j))(g) h_j(g')`. So
  `Ψ(gg') = Ψ(g)Ψ(g')`. Also `Ψ(1) = I`, so `Ψ` maps into
  `GL_((r+1)d)(Λ)`.
- **Injective.** If `Ψ(g) = I`, then `π_g = id` and `ρ(g_1^(-1) g g_1) = I`.
  Since `ρ` is injective, `g = 1`.

## Step 7: Example 4.7, proving (c)

Let `A = R^n` and `ν(r_1, ..., r_n) = (r_1 x, ..., r_n x)`.

- **Setting (L).** `A` is elementary abelian because `p·1 = 0`. `ν` is injective,
  because `rx = 0` implies `r = 0`. Also `ν^k A = (Rx^k)^n`. So `A/νA = (R/Rx)^n`
  has dimension `ns`, and `∩_k ν^k A = 0`.
- **The group.** For `γ in GL_n(R)` acting on column vectors,
  `(γ(vx))_i = Σ_j γ_ij v_j x = (γv)_i x`. So `Γ` commutes with `ν`, and Step 5
  gives `R^n x| Γ -> GL_(ns+1)(Λ)`.
- **The ring.** Take `n = 1` and `λ_a(r) = ar`. Each `λ_a` commutes with `ν`, by
  associativity. The map `λ: R -> End_ν(R)` is a unital ring homomorphism, and it
  is injective because `λ_a(1) = a`. So `M∘λ` embeds `R` in `M_s(Λ)`.

## Step 8: twists, proving (d)

- **Commutation.** From `μ^(-m)γμ^m = δγδ^(-1)` we get `γμ^m = μ^m δγδ^(-1)`. So
  `γ(μ^m δ) = (μ^m δ)γ`.
- **Injective.** `ν = μ^m δ` is a composite of injections.
- **Filtration.** By induction `ν^k A = μ^m δ(μ^(m(k-1)) A) = μ^(mk) A`, since `δ`
  preserves every `μ^j A`. So `A/νA = A/μ^m A`, which is finite of dimension
  `m·dim A/μA` by the argument of Step 1 applied to `μ`, and `∩_k ν^k A = 0`.
- **Special cases.** Both special cases satisfy the hypothesis:
  - `δ = id` is filtration-preserving;
  - `δ in Γ` preserves every `μ^k A` by the stability assumption on `Γ`.

Step 6 finishes. `∎`

## Trust surface

The proof uses only linear algebra over `F_p`, inverse limits of finite
truncations, and the block-matrix computation in Step 6, which is written out
above. It cites no other theorem.
