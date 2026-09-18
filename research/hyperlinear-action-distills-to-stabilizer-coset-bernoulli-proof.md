---
rg: 2
id: hyperlinear-action-distills-to-stabilizer-coset-bernoulli-proof
kind: route
title: Realize a positive-definite function peaking exactly on the stabilizer, power it to the indicator, and pass to the Gaussian limit inside the closed hyperlinear class
target: hyperlinear-action-distills-to-stabilizer-coset-bernoulli
requires: []
---

# Proof

Throughout, `G` is countable, actions are p.m.p. on standard spaces, and an action
`G ↷ (Y,ν)` is **hyperlinear** when `M_Y := L^∞(Y) ⋊ G` (canonical trace
`τ(f u_g) = δ_(g,e) ∫ f dν`) embeds trace-preservingly in `R^ω`. For a real
`θ ∈ L²(Y)` write `π(h)θ = θ∘h^(-1)` (Koopman representation).

## Step 0: three closure properties

**(C1) Factors.** If `B ⊆ L^∞(Y)` is a `G`-invariant von Neumann subalgebra, then
`B ⋊ G ⊆ M_Y` trace-preservingly, so a factor of a hyperlinear action is hyperlinear.
In particular any `G`-equivariant measurable map `Φ : Y → Ω` gives the hyperlinear
action `G ↷ (Ω, Φ_*ν)`.

**(C2) Countable products.** For hyperlinear `Y_1, Y_2` the map
`(f_1⊗f_2) u_g ↦ (f_1 u_g) ⊗ (f_2 u_g)` is a `*`-homomorphism from the algebraic
crossed product of the diagonal action on `Y_1×Y_2` into `M_(Y_1) ⊗̄ M_(Y_2)`, and it
preserves traces: `τ(f_1u_g)τ(f_2u_g) = δ_(g,e) ∫f_1 ∫f_2`. A trace-preserving
`*`-homomorphism of a weakly dense `*`-subalgebra extends to a normal embedding of the
von Neumann algebra (it is isometric in `‖·‖_2`). Tensor products of embeddable
algebras are embeddable (`R^ω ⊗̄ R^ω ⊆ (R⊗̄R)^ω ≅ R^ω`). For a countable product
`∏_(i∈N) Y_i`, the crossed products of the finite products form an increasing
sequence of embeddable subalgebras with weakly dense union; a finitely generated
moment problem is decided on a finite stage, so the union is embeddable.

**(C3) Weak-star limits.** Let `Ω = [-1,1]^G` with the shift `(g·ω)_h = ω_(g^(-1)h)`,
and let `ν_k → ν` weak-star, all shift-invariant. If every `G ↷ (Ω,ν_k)` is
hyperlinear then so is `G ↷ (Ω,ν)`. Indeed, on the `*`-algebra
`𝒜 = C(Ω) ⋊_alg G` the traces `τ_k(f u_g) = δ_(g,e)∫ f dν_k` converge pointwise to
`τ(f u_g) = δ_(g,e)∫ f dν`, whose GNS von Neumann algebra is `L^∞(Ω,ν) ⋊ G`. A
tracial state on a countably generated `*`-algebra (generators of bounded norm) has
`R^ω`-embeddable GNS algebra iff for every finite set of generators, every `L` and
every `ε>0` there are matrices of the same norm bounds whose normalized-trace
`*`-moments of length `≤ L` are `ε`-close to those of the state. This condition is
evidently closed under pointwise limits of states (use `τ_k` with `k` large, then its
microstates). So `τ` is embeddable.

A real process `(ω_h)_(h∈G)` is sent to `Ω` by the homeomorphism
`t ↦ t/(1+|t|)` coordinatewise; convergence of finite-dimensional marginals of real
processes gives weak-star convergence of the pushforwards on `Ω` (cylinder functions
are dense in `C(Ω)`). So (C3) applies to processes with values in `R`.

## Step 1: a vector peaking exactly on the stabilizer

Let `A ⊆ X` with `α = μ(A) ∈ (0,1)`. In `L²(X×X)` (diagonal action) put

```text
ζ_A = 1_(A × A^c) − α(1−α),       ‖ζ_A‖² = α(1−α)(1 − α(1−α)) > 0.
```

`π(h)ζ_A = 1_(hA × (hA)^c) − α(1−α)`. Put `ψ_A(h) = ⟨π(h)ζ_A, ζ_A⟩ / ‖ζ_A‖²`, a real
normalized positive-definite function with `|ψ_A| ≤ 1`.

* `ψ_A(h) = 1` iff `π(h)ζ_A = ζ_A` iff `hA × (hA)^c = A × A^c` (mod null) iff `hA = A`
  (because `0<α<1`, the product set determines both factors). So `ψ_A = 1` exactly on
  `Stab(A)`.
* `ψ_A(h) = −1` never happens: it would force `1_(hA×(hA)^c) + 1_(A×A^c) = 2α(1−α)` a.e.;
  the left side is integer-valued and the right side lies in `(0, 1/2]`.

Now let `(A_i)_(i∈I)`, `I ⊆ N`, be the family of the claim, and
`Y = ∏_(i∈I) (X×X)` with the product measure and diagonal action; `Y` is hyperlinear by
(C2). Let `ζ̂_i = ζ_(A_i) ∘ pr_i` and choose `c_i > 0` with `Σ_i c_i² ‖ζ_(A_i)‖² = 1`.
Put `η = Σ_i c_i ζ̂_i ∈ L²_0(Y)` (real, mean zero). Distinct coordinates are independent
and each `π(h)ζ̂_i` is a mean-zero function of the `i`-th coordinate only, so the cross
terms vanish and

```text
ψ(h) := ⟨π(h)η, η⟩ = Σ_i c_i² ‖ζ_(A_i)‖² ψ_(A_i)(h),
```

a convex combination. Hence `ψ(h) = 1` iff `h ∈ ∩_i Stab(A_i) = Δ`, and `|ψ(h)| < 1`
for `h ∉ Δ` (a convex combination of numbers in `(−1,1]` equals `−1` never, and equals
`1` only if every term is `1`).

## Step 2: powers

For `n ≥ 1` the product `Y^n` is hyperlinear (C2), and `η^(⊗n)(y_1,…,y_n) = ∏_j η(y_j)`
is real, mean zero, and satisfies `⟨π(h)η^(⊗n), η^(⊗n)⟩ = ψ(h)^n`. Pointwise on `G`,

```text
ψ^n  →  1_Δ     (n → ∞).
```

## Step 3: central limit theorem

Let `Z` be a hyperlinear action and `θ ∈ L²_0(Z)` real with `φ(h) = ⟨π(h)θ,θ⟩`,
`φ(e)=1`. On `Z^M` (hyperlinear by (C2)) put `F_M = M^(-1/2) Σ_(j=1)^M θ∘pr_j` and
`Φ_M : Z^M → R^G`, `Φ_M(z)_h = F_M(h^(-1)z)`. Then `Φ_M(gz)_h = Φ_M(z)_(g^(-1)h)`, so
`Φ_M` is equivariant for the shift and `ν_M = (Φ_M)_*(product measure)` gives a
hyperlinear action by (C1). For `h_1,…,h_k ∈ G` the vector
`(Φ_M(z)_(h_a))_a` is `M^(-1/2)` times a sum of `M` i.i.d. mean-zero vectors
`(θ(h_a^(-1) z_j))_a` with covariance
`E[θ(h_a^(-1)z)θ(h_b^(-1)z)] = ⟨π(h_a)θ, π(h_b)θ⟩ = φ(h_a^(-1)h_b)`. By the multivariate
CLT the marginals converge to the centered Gaussian with covariance
`[φ(h_a^(-1)h_b)]`. By (C3) the stationary Gaussian process `γ_φ` with covariance
function `φ` defines a hyperlinear action.

Apply this to `Z = Y^n`, `θ = η^(⊗n)`: the Gaussian actions `γ_(ψ^n)` are hyperlinear.

## Step 4: the limit is the Gaussian Bernoulli shift over G/Δ

Centered Gaussian laws whose covariances converge entrywise converge in every finite
marginal, so `γ_(ψ^n) → γ_(1_Δ)` weak-star and `γ_(1_Δ)` is hyperlinear by (C3). In
`γ_(1_Δ)`, `E[(ω_h − ω_(h'))²] = 2 − 2·1_Δ(h^(-1)h')`, so `ω_h = ω_(h')` a.s. when
`hΔ = h'Δ`, while coordinates over distinct cosets are jointly Gaussian and
uncorrelated, hence independent `N(0,1)`. The map
`(x_c)_(c∈G/Δ) ↦ (x_(hΔ))_(h∈G)` is an injective shift-equivariant map carrying
`N(0,1)^(⊗ G/Δ)` onto the law of `γ_(1_Δ)`. So `G ↷ (R, N(0,1))^(G/Δ)` is hyperlinear.

## Step 5: any base, and the wreath

For a standard `(K,κ)` pick measurable `β : R → K` with `β_* N(0,1) = κ`; coordinatewise
`β` is a factor map onto `(K,κ)^(G/Δ)`, hyperlinear by (C1). With `K = {±1}` fair,
Fourier transform identifies `L^∞({±1}^(G/Δ))` with `L(⊕_(G/Δ) Z/2)` equivariantly, so
`L^∞({±1}^(G/Δ)) ⋊ G = L(W_Δ)`, and a group is hyperlinear iff its group von Neumann
algebra embeds in `R^ω`. ∎

## Consequence 1 (faithful actions)

If the action is faithful on the measure algebra, choose `(A_i)` a countable dense
family in the measure algebra, discarding null and conull sets. If `h` fixes every
`A_i` then `h` fixes their closure, i.e. every measurable set, so `h` acts trivially
and `h = e`. Thus `Δ = {e}` and `Z/2 ≀ G = W_(e)` is hyperlinear.

## Consequence 2 (pointwise stabilizers)

For a sub-σ-algebra `B`, the sets fixed (mod null) by a given `h` form a σ-algebra;
so `h` fixes `B` pointwise iff it fixes a countable generating family. Taking that
family as `(A_i)` gives `Δ = Δ_B`.

## Remark: sofic variant (not used, not part of the claim)

(C1), (C2) and (C3) hold for Păunescu-sofic actions as well: restriction of a
diagonal-plus-permutation embedding, tensor products of diagonal and permutation
matrices, and the microstate description with diagonal and permutation constraints,
which is again closed under pointwise limits of traces. So Steps 1–5 should give the sofic
statement; this remark is unrefereed and no other node depends on it.

## Calibration

For a residually finite `G` and a subgroup `Δ` closed in the profinite topology, the
profinite action on `Ĝ/Δ̄` is sofic and its clopen neighbourhoods of the base point have
stabilizers intersecting to `Δ`; the sofic remark then predicts `W_Δ` sofic, in agreement
with residual finiteness of such permutational wreaths. For the Theorem E pair the congruence quotients do not isolate `Γ`: every finite
quotient ring of `F_q[x^(±1)]` inverts each `x_i` by a polynomial in `x_i`, so `Γ` has the
same image as `EL_r(F_q[x^(±1)])` at every congruence level. Consistently with Kun--Thom
Theorem A, the established statement (via profinite actions, which are hyperlinear) shows that
if `Γ` were closed in the profinite topology of `G` then `W_Γ` would be hyperlinear, and the
sofic remark would make it sofic; so the remark predicts that `Γ` is not profinitely closed.
