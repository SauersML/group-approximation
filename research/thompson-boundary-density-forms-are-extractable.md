---
rg: 2
id: thompson-boundary-density-forms-are-extractable
kind: claim
title: "Class-kill (no complementary series): every Hermitian form on weight-lambda dyadic step functions invariant under T-bar (theta-quasi-periodic on R) or under nV (on C^n) is classified for every complex lambda; the positive ones give only twisted Koopman, jump-orbit or trivial representations, all extractable, so no boundary-density representation of any weight carries a cocycle unbounded on the centre of T-bar or a witness of R1, P1, P2, P3 for nV"
distinct_from:
  lifted-thompson-t-extractable-cocycles-bounded-on-centre: that bounds cocycles into representations already known to carry a circle extraction, and treats only the unitary weight s = 0 of step (b); this classifies all invariant forms for every complex weight, which is what shows that the weights s != 0 carry no unitary structure at all
  nv-extractable-cocycles-bounded-on-centralizers: that is the gap bound for coordinate-extractable representations of nV; this proves that every positive invariant form on weighted locally constant functions yields such a representation (twisted Koopman) or the trivial one
  lifted-thompson-t-convex-line-walls-are-trivial: that kills invariant measures on pairs of points (order-convex walls); this kills invariant Hermitian kernels on weighted densities, a linear rather than measured-wall structure
  thompson-t-c0-continuous-affine-actions-are-trivial: that kills actions continuous for the uniform C^0 topology; the representations here are not assumed continuous in any topology on T-bar
  lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure: that is an exact criterion for T-bar in terms of the twist cost; this rules out one concrete source of candidate measures, the boundary-density family
---

**ESTABLISHED** by `thompson-boundary-density-forms-are-extractable-proof`.

**Conventions.**
- `e(t) = e^{2πit}`. For `k ∈ Z` and `λ ∈ C`, `2^{kλ} := e^{kλ ln 2}`.
- `Λ_0 = (2πi/ln 2)Z` and `Λ_1 = 1 + Λ_0`. If `λ ∈ Λ_0` then `2^{kλ} = 1`, and if `λ ∈ Λ_1` then
  `2^{kλ} = 2^k`, for all `k ∈ Z`. So on these sets the representations below are those of
  `λ = 0` and `λ = 1`.
- A *Hermitian form* on a complex vector space is linear in the first slot, conjugate-linear in
  the second, with `B(G,F) = conj B(F,G)`. Positivity is not assumed.
- `B` is *invariant* if `B(π(g)F, π(g)G) = B(F,G)` for all `g` and all `F, G`.

## Setting T̄

- `T̄` is the group of homeomorphisms `g` of `R` that commute with `z(x) = x + 1` and are
  piecewise affine, with finitely many breakpoints in `[0,1)`, all breakpoints in `Z[1/2]`,
  slopes in `2^Z`, and `g(Z[1/2]) = Z[1/2]`. This is the lift of Thompson's `T`.
- A *brick* is `[c 2^{-k}, (c+1) 2^{-k})` with `c ∈ Z` and `k ≥ 0`. Its level is `k`.
- For `θ ∈ R`, `D_θ` is the space of `F: R → C` with `F(x+1) = e(θ)F(x)` that are constant on
  every brick of some level `k`.
- For `λ ∈ C` and `g ∈ T̄`, `(π_λ(g)F)(x) = (g^{-1})'(x+)^λ F(g^{-1}x)`. The right derivative is
  `2^j` for some `j ∈ Z`, and its `λ`-th power is `2^{jλ}`. Then `π_λ` is a representation of
  `T̄` on `D_θ`, and `π_λ(z)` is the scalar `e(−θ)`.
- Three model forms:
  - `K_θ(F,G) = ∫_0^1 F Ḡ dx`.
  - `B^1_θ(F,G) = ∫_0^1 ∫_0^1 F(x) Ḡ(y) k_θ(x,y) dx dy`, where `k_θ(x,y) = e(θ/2)` for `x < y`
    and `k_θ(x,y) = e(−θ/2)` for `x > y`.
  - For `λ ∈ Λ_0` and `γ ∈ C`, `J_γ(F,G) = Σ_x v_G(x)^* M_γ v_F(x)`, summed over
    `x ∈ Z[1/2] ∩ [0,1)`. Here `v_F(x) = (F(x−), F(x))^T` and
    `M_γ = [[−Re γ, γ], [γ̄, −Re γ]]`. For `γ = −1` this is the jump form
    `Σ_x (F(x) − F(x−)) conj(G(x) − G(x−))`.

**Theorem A (T̄).** Let `θ ∈ R`, `λ ∈ C`, and let `B` be a `π_λ`-invariant Hermitian form on
`D_θ`.
1. If `λ ∉ Λ_0 ∪ Λ_1` and `Re λ ≠ 1/2`, then `B = 0`.
2. If `Re λ = 1/2`, then `B = c K_θ` for some `c ∈ R`.
3. If `λ ∈ Λ_1`, then `B = r B^1_θ` for some `r ∈ R`.
4. If `λ ∈ Λ_0`, then `B = J_γ` for some `γ ∈ C`.

Each listed form is invariant. The positive semidefinite ones are exactly these:
- `c ≥ 0` in case 2;
- in case 3, `r e(θ/2) ≥ 0` when `θ ∈ Z`, and only `r = 0` when `θ ∉ Z`;
- `γ ∈ (−∞, 0]` in case 4, which gives the multiples `s·J_{−1}` with `s ≥ 0` of the jump form.

**Corollary A (the representations).** Let `B ≥ 0` be invariant, and let `H_B` be the Hausdorff
completion of `(D_θ, B)`. Then `π_λ` extends to a unitary representation `ρ_B` of `T̄` on `H_B`,
and `ρ_B` is one of the following:
- zero;
- `L²_θ` (locally `L²`, `θ`-quasi-periodic, normed on `[0,1)`) with
  `ρ(g)f = (g^{-1})'^{1/2 + it} f∘g^{-1}`, where `λ = 1/2 + it`;
- the trivial representation, which occurs only when `θ ∈ Z` and `λ ∈ Λ_1`;
- a subrepresentation of `ℓ²_θ(Z[1/2])` with `(σ(g)ξ)(x) = ξ(g^{-1}x)`, which occurs only when
  `λ ∈ Λ_0`.

Every nontrivial case has a covariant projection-valued measure on `S^1`, namely multiplication
by `1_{E + Z}`. So each is a circle extraction of type (a) in
`lifted-thompson-t-extractable-cocycles-bounded-on-centre`.

**Corollary A′ (class-kill for T̄).** Let `ρ = ⊕_α ρ_{B_α}` be any direct sum of such
representations, over any family of `(θ_α, λ_α, B_α)`. Let `b` be any 1-cocycle into `ρ`, and
`ψ = ‖b‖²`. Then `sup_M ψ(z^M) ≤ 400 Σ_i ψ(ĥ_i)`. The same bound holds if the nontrivial part of
`ρ` is replaced by any representation weakly contained in it. In particular:
- no complementary-series-type family `(g^{-1})'^{1/2+s}` exists for real `0 < |s| < 1/2`;
- the unitary members, `s ∈ iR`, together with the endpoints `s = ±1/2`, carry no cnd function
  that is unbounded on `⟨z⟩`.

This closes next step (b) of the w8 attempt on `lifted-thompson-t-is-a-t-menable` for every
weight and every `θ`.

## Setting nV

- `C = {0,1}^ω`, `n ≥ 1`, and `μ` is the product of the fair Bernoulli measures on `C^n`.
- A *brick* is `[w_1] × ... × [w_n]` for finite words `w_i`. Its measure is `2^{-Σ|w_i|}`.
- `nV` (with `1V = V`) is the group of homeomorphisms `g` of `C^n` for which there are two brick
  partitions `{P_i}` and `{P'_i}` of equal size with `g|P_i` the canonical (prefix-replacing)
  map onto `P'_i`.
- `J_g = d(g^{-1})_*μ/dμ` equals `μ(P'_i)/μ(P_i) ∈ 2^Z` on `P_i`.
- `LC` is the space of locally constant `F: C^n → C`, and `π_λ(g)F = J_{g^{-1}}^λ · F∘g^{-1}`.
- `m(F) = ∫ F dμ`.

**Theorem N (nV).** Let `n ≥ 1`, `λ ∈ C`, and let `B` be a `π_λ`-invariant Hermitian form on
`LC`.
1. If `λ ∉ Λ_1` and `Re λ ≠ 1/2`, then `B = 0`. This includes `λ ∈ Λ_0`: unlike `T̄`, the Cantor
   set has no jump forms.
2. If `Re λ = 1/2`, then `B = c ∫ F Ḡ dμ` for some `c ∈ R`.
3. If `λ ∈ Λ_1`, then `B = κ m(F) conj m(G)` for some `κ ∈ R`.

**Corollary N (class-kill for nV).** Let `n ≥ 2`. Every positive invariant form yields one of:
- zero;
- the trivial representation;
- the twisted Koopman representation `f ↦ J_{g^{-1}}^{1/2+it} f∘g^{-1}` on `L²(C^n, μ)`.

The twisted Koopman representation is coordinate-extractable in the sense of
`nv-extractable-cocycles-bounded-on-centralizers`, via `μ_r = (pr_j)_*(|r|² μ)`. Homomorphisms
`nV → C` vanish, because `nV` is simple. So for every 1-cocycle `b` into any direct sum of such
representations, `ψ = ‖b‖²` is bounded on every `E_j ≅ (n−1)V`. Consequently `ψ` is:
- not proper;
- not proper on the cocycle kernel (not P3);
- not a scale for the exponent cocycle (not P1);
- not a pattern-depth majorant (not P2);
- not proper modulo `T_n` (not R1).

These are corollaries 1-4 of that node. So a witness for
`brin-thompson-groups-nv-are-a-t-menable` along any of its routes cannot come from any weighted
boundary-density representation of `nV`.

## Scope

- **Covered.** Every function space that contains the dyadic step functions (`D_θ` or `LC`) and
  is preserved by `π_λ`. On any such space, an invariant form restricts to one classified here.
  This includes `L^p` and Sobolev `H^σ` with `σ < 1/2`, which are the spaces where classical
  complementary-series norms live.
  - If step functions are dense for the form's seminorm, the whole representation is the one
    in Corollary A or Corollary N.
  - Otherwise the restriction to the step functions still says the following: the closed
    span of the orbit of any step function is extractable or trivial.
- **Not covered.**
  - Forms on spaces that meet the step functions trivially.
  - Configuration spaces of `k ≥ 2` boundary points, for example kernels on
    `(S^1)^2 ∖ Δ` with density weights in each variable. For these, only order-convex walls have
    been killed, in `lifted-thompson-t-convex-line-walls-are-trivial`.
  - The Ptolemy model of `T`, with piecewise-`PSL_2(Z)` maps and non-locally-constant
    Jacobians. There the step functions are not preserved, and the proof does not apply.
