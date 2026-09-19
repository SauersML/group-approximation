---
rg: 2
id: thompson-v-k-shadow-cannot-detect-mf-proof
kind: route
title: Simplicity reduces MF to one rank class, and rational traces from Higson--Kasparov plus Lück let a positive integer shadow give that class a nonzero value
target: thompson-v-k-shadow-cannot-detect-mf
requires:
  - thompson-v-finitely-presented-infinite-simple
  - thompson-v-character-simplex
  - thompson-v-has-haagerup-property
  - osajda-monster-hosts-for-bc-module-route
  - lueck-surjective-assembly-traces-lie-in-lambda-g
  - thompson-v-is-integrally-acyclic
  - thompson-v-torsion-centralizers-are-rationally-acyclic
  - dadarlat-matricial-stability-obstruction
---

Notation is as in the target. `λ : C*(V) → C*_r(V)` is the regular
quotient, and `τ = τ_red ∘ λ`.

## (i) Reduction to one class

*Asymptotic representations and *-homomorphisms.* An operator-norm
asymptotic representation `ψ_n : V → U(k_n)` defines a group homomorphism
`V → U(Q_k)`. By universality of `C*(V)` this extends to a unital
*-homomorphism `Ψ : C*(V) → Q_k`. Conversely, lifting `Ψ` on `V` gives such
a `ψ`.

*Rank classes.* Let `P ∈ M_m(Q_k)` be a projection. Lift it to a self-adjoint
element `(x_n)`. Eventually `spec(x_n)` lies within `1/4` of `{0,1}`, and
functional calculus gives projections `P_n`. Two lifts eventually differ by
less than `1`, and projections at distance less than `1` have equal rank. So
`r(P) = [(rank P_n)]` is well defined. It is additive on orthogonal sums and
invariant under unitary conjugation and homotopy. So `r ∘ Ψ` induces a
homomorphism on `K_0(C*(V))`, called the rank shadow of `Ψ`.

*(⇐).* Suppose `r(Ψ(p_s)) ≠ 0`. Then `rank P_n ≥ 1` for `n` in an infinite
set `S`, where `P_n` are projection lifts of `Ψ(p_s)`. Then `u_n = 1 - 2P_n`
lifts `Ψ(s)`, and `||u_n - 1|| = 2` on `S`. Choose a nonprincipal ultrafilter
`ω ∋ S`. The induced map `π_ω : V → U(∏_ω M_(k_n))/{||·-1|| → 0}` has
`π_ω(s) ≠ 1`. `V` is simple (`thompson-v-finitely-presented-infinite-simple`),
so `ker π_ω` is trivial.

To reach the target's normalization, with dimension `n` in the `n`-th
coordinate, pad the dimensions. Injectivity gives `c_g = lim_ω ||ψ_n(g) - 1|| > 0`
for `g ≠ 1`. Enumerate `V = {g_1, g_2, ...}` and let `F_j = {g_1..g_j}`.
Choose indices `n_1 < n_2 < ...`, each in the `ω`-large set where `ψ_n` is
`1/j`-multiplicative on `F_j` and `||ψ_n(g) - 1|| > c_g/2` on
`F_j \ {1}`. Replace `ψ_(n_j)` by an amplification `ψ_(n_j)^(⊕2^(e_j))`. This
changes no norm estimate, and it makes the dimensions `d_j` strictly
increasing. For `d_j ≤ m < d_(j+1)` set
`φ_m = ψ_(n_j)^(⊕2^(e_j)) ⊕ 1_(m-d_j)`. Adding an identity block changes no
defect and no distance to `1`. So `φ_m : V → U(m)` is an asymptotic
representation with `||φ_m(g) - 1|| ≥ c_g/2` eventually, for each `g ≠ 1`.
Hence `V` embeds in the target's ultraproduct, for every `ω`.

*(⇒).* Given the target's embedding, take `k_n = n` and let `Ψ` come from
the representing sequence. If `r(Ψ(p_s)) = 0`, then `Ψ(p_s) = 0` (a
projection of eventual rank `0` is `0` in `Q_k`). So `Ψ(s) = 1` and
`||ψ_n(s) - 1|| → 0`, which contradicts `s ≠ 1` being mapped to a nontrivial
element. The equivalent phrasings in the target follow. If `ψ_n(s) → 1`
fails, pass to a subsequence where it stays away from `1` and apply (⇐). The
spectral statement holds because, once `ψ_n(s)^2 ≈ 1`, the spectral
projection on `{Re z < 0}` is a lift of `Ψ(p_s)`.

## (ii) Construction of θ

*Step 1: `τ_*` is rational on `K_0(C*(V))`.* `V` is a-T-menable
(`thompson-v-has-haagerup-property`, Farley). So the Baum--Connes assembly map
for `V` is an isomorphism, by Higson--Kasparov (item (5) of
`osajda-monster-hosts-for-bc-module-route`: every a-T-menable group satisfies
Baum--Connes with coefficients, in particular with trivial coefficients). By
`lueck-surjective-assembly-traces-lie-in-lambda-g` (Lück, Invent. Math. 149
(2002), Theorem 0.3), `τ_red,*(K_0(C*_r V)) ⊆ Λ^V ⊆ Q`. Since
`τ_* = τ_red,* ∘ λ_*`, we get `τ_*(K_0(C*(V))) ⊆ Q`. (Here `Λ^V = Q`: `V`
contains every finite symmetric group, permuting the `2^d` cylinders of depth
`d`. Only `⊆ Q` is used.) Also `ε_*` takes values in `K_0(C) = Z`.

*Step 2: denominators.* `C*(V)` is separable, so `K_0(C*(V))` is countable.
Enumerate it as `x_1, x_2, ...`. Let `D_n ≥ 1` be a common denominator of
`τ_*(x_1), ..., τ_*(x_n)`, and put `b_n = 2 · n! · D_1 D_2 ... D_n`. Then
`b_n` is even, `n!` divides `b_n`, and `b_n τ_*(x_j) ∈ Z` for all `n ≥ j`.
Given `t ∈ (0,1]`, put `a_n = floor(b_n (1-t)/t)`. For `t = 0`, put
`a_n = n b_n`. Then `a_n ≥ 0`, and `b_n/(a_n + b_n) → t`, since
`b_n → ∞`. Put `k_n = a_n + b_n`.

*Step 3: θ is a homomorphism.* For `x = x_j` let `θ_n(x) = a_n ε_*(x) + b_n τ_*(x)`
if `n ≥ j`, and `0` otherwise. This is an integer. Let `θ(x)` be the class of
`(θ_n(x))_n` in `∏Z/⊕Z`. For `x, y` and `x + y`, the three sequences are
eventually given by the additive formula, so `θ(x + y) = θ(x) + θ(y)`.

*Step 4: properties.* For a projection `P ∈ M_m(C*(V))`, both `ε_*[P]` and
`τ_*[P]` are nonnegative (`ε` and `τ` are positive), so (S1) holds. `[1]` has
`ε = τ = 1`, so `θ[1] = [(a_n + b_n)] = [(k_n)]`, which is (S2).
`|θ_n(x)| ≤ (|ε_*(x)| + |τ_*(x)|) k_n` gives (S3). Dividing by `k_n` gives
`θ_n(x)/k_n → (1-t) ε_*(x) + t τ_*(x)`, which is (S4). Finally,
`ε(s) = 1` gives `ε(p_s) = 0`, and `s ≠ 1` gives `τ(s) = 0` and
`τ(p_s) = 1/2`. So `θ_n[p_s] = b_n/2 ≥ 1` eventually, and the class is
nonzero, which is (S5).

*Remarks in the target, checked.* A rank shadow `r ∘ Ψ_*` is positive,
because `Ψ` maps projections to projections. It sends `[1]` to `[(k_n)]`, and
it is bounded by `m k_n` on classes from `M_m`. Along any ultrafilter `ω`,
`lim_ω tr_(k_n) ∘ Ψ` is a tracial state on `C*(V)`, so it is some `τ_t` by
`thompson-v-character-simplex`, and `rank/k_n → τ_t,*` along `ω`.

Every bounded trace on `C*(V)` is a combination of `ε` and `τ`. A bounded
hermitian trace splits into positive tracial parts, and those are multiples
of tracial states. So every bounded-trace constraint is met by `θ`, for the
chosen `t`.

## (ii-a) Finite-subgroup packets

Let `H ≤ V` be finite and `n ≥ |H|`. `C*(H) = ⊕_π M_(dim π)`, and
`K_0(C*(H)) = R(H)` has basis the classes `[e_π]` of minimal projections.
Under `C*(H) → C*(V)` we have `ε_*[e_π] = δ_(π, 1)`, and
`τ_*[e_π] = dim π / |H|`, since `τ` restricts to the regular trace of `H`.
Up to the finitely many initial indices where Step 3 sets `θ_n = 0`,

```text
θ_n[e_π] = a_n δ_(π,1) + (b_n/|H|) dim π,
```

which is the multiplicity of `π` in `ρ_H = a_n 1_H ⊕ (b_n/|H|) reg_H`. This
is an integer because `|H|` divides `n!`, which divides `b_n`.

- *Restriction.* For `K ≤ H`, `Res^H_K reg_H = [H:K] reg_K`, so
  `Res ρ_H = a_n 1_K ⊕ (b_n/|K|) reg_K = ρ_K`.
- *Conjugation.* `ρ_(gHg^(-1)) ∘ Ad g ≅ ρ_H`, since both summands are
  conjugation invariant.
- *The involution.* On `⟨s⟩ ≅ Z/2`, `reg = 1 ⊕ sign`, so the sign
  multiplicity is `b_n/2`.

So no argument that counts multiplicities or packets over finite subgroups
can force the `-1` eigenspace of `s` to vanish.

## (iii) Cohomology

`H^(2k)(V; Q) = 0` for `k ≥ 1` by `thompson-v-is-integrally-acyclic` and
universal coefficients. `H^(2k)(C_V(g); Q) = 0` for torsion `g` and `k ≥ 1` is
`thompson-v-torsion-centralizers-are-rationally-acyclic`.
`dadarlat-matricial-stability-obstruction` (Theorem 1.1) concludes non-matricial
stability only from some `H^(2k)(G; Q) ≠ 0` with `k ≥ 1`. So it has no input
for `V`. Theorem 1.2's cohomological conclusion holds trivially for `V`.

The final clause of (iii) is interpretive. It says that an invariant built
from the groups `H^(≥1)(C_V(g); Q)` has zero input. It asserts no theorem
about such invariants. QED.
