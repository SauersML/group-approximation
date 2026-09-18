---
rg: 2
id: cantor-central-v-elliptic-witnesses-die-proof
kind: route
title: "Exchangeable cone phases, de Finetti's directing measure and Cesàro averaging give φ(k·1_U) = P(ν̂(k) = 1) ≥ P(ν = δ_0) = φ(1_U); the circumcentre of a bounded V-orbit transfers this to cnd functions on G bounded on V"
target: cantor-central-v-elliptic-witnesses-die
requires: []
---

Notation is as in the target. `T = R/Z` and `Â = Hom(A, T)`, the compact dual of the discrete group
`A`. A character acts by `f ↦ e(χ(f))`. `V` acts on `Â` by `(v·χ)(f) = χ(v^{-1}·f)`.

**Imports (standard, stated in the form used).**
- (I1) *Bochner's theorem for discrete abelian groups.* A positive definite `φ` on `A` with
  `φ(0) = 1` is `φ(f) = ∫_Â e(χ(f)) dμ(χ)` for a unique Borel probability measure `μ` on `Â`.
- (I2) *Schoenberg's theorem.* If `ψ` is cnd on a group `Γ` with `ψ(e) = 0`, then:
  - `e^{-tψ}` is positive definite for all `t > 0`;
  - `ψ(γ) = ‖b(γ)‖²` for a 1-cocycle `b` of some orthogonal representation;
  - hence `√ψ(γγ') ≤ √ψ(γ) + √ψ(γ')`.
- (I3) *de Finetti's theorem* (Hewitt–Savage, Trans. AMS 80 (1955); in the form of Aldous, *Exchangeability
  and related topics*, LNM 1117, §3). Let `(Y_i)_{i≥1}` be an infinite exchangeable sequence of
  random variables with values in a standard Borel space. Then there is a random probability measure
  `ν` such that, conditionally on `ν`, the `Y_i` are i.i.d. with law `ν`.
- (I4) *Circumcentre lemma.* An affine isometric action on a Hilbert space with a bounded orbit has a
  fixed point.

## Step 1. The spectral law is V-invariant

Let `φ` be as in part 1 of the theorem, and let `μ` be its measure from (I1). For `v ∈ V`, let `μ^v`
be the law of `χ ↦ χ(v·(·))`. Then `∫ e(χ(f)) dμ^v = φ(v·f) = φ(f)`. By uniqueness in (I1),
`μ^v = μ`. So if `χ` has law `μ`, then for every `v ∈ V` the process `(χ(v·f))_{f∈A}` has the same
law as `(χ(f))_{f∈A}`. Note `v·1_U = 1_{vU}`.

Every proper clopen `U` is `v[0]` for some `v ∈ V`, since `V` is transitive on ordered pairs
`(U, C∖U)` of nonempty clopens. So `φ(k·1_U) = φ(k·1_{[0]})`, and it suffices to treat `U = [0]`.

## Step 2. Exchangeable cone phases with constant partial-sum law

Let `U_i = [1^{i-1}0]` for `i ≥ 1`. These are disjoint cones, `U_1 = [0]`, and
`W_m := U_1 ⊔ … ⊔ U_m = C ∖ [1^m]`. Put `Y_i = χ(1_{U_i}) ∈ T` and
`S_m = Y_1 + … + Y_m = χ(1_{W_m})`, using additivity of `χ`.

*(a) Exchangeability.* Fix `n` and `σ ∈ S_n`. Let `v_σ ∈ V` act as follows:
- on `U_i` for `i ≤ n`, by the prefix replacement `1^{i-1}0w ↦ 1^{σ(i)-1}0w`;
- on `[1^n]`, as the identity.

These cones partition `C`, so `v_σ ∈ V` and `v_σ·1_{U_i} = 1_{U_{σ(i)}}`. By Step 1,
`(Y_{σ(1)}, …, Y_{σ(n)})` has the same law as `(Y_1, …, Y_n)`. So `(Y_i)` is exchangeable.

*(b) Constant partial sums.* Fix `m ≥ 2`. Let `w_m ∈ V` act as follows:
- on `[1]`, by `1w ↦ 1^m w`;
- on the partition `[01], [001], …, [0^{m-1}1], [0^m]` of `[0]` into `m` cones, by prefix
  replacements onto `U_1, …, U_m`, in that order.

Then `w_m·1_{[0]} = 1_{W_m}`. By Step 1, `S_m` has the same law as `S_1 = χ(1_{[0]})`. Consequently,
for every `k ∈ Z` and every `m ≥ 1`,

`(2.1)   E e(k S_m) = E e(k χ(1_{[0]})) = φ(k·1_{[0]}) =: c_k.`

## Step 3. Cesàro identity for the directing measure

`T` is a standard Borel space, so (I3) gives a random probability measure `ν` on `T` such that,
given `ν`, the `Y_i` are i.i.d. with law `ν`. Fix `k ∈ Z` and set `z = ν̂(k) = ∫ e(kθ) dν(θ)`, a
random variable with `|z| ≤ 1`. Conditional independence gives `E[e(kS_m) | ν] = z^m`. Taking
expectations in (2.1):

`(3.1)   E z^m = c_k   for every m ≥ 1.`

Average (3.1) over `m = 1, …, M`. Pointwise, `(1/M) Σ_{m≤M} z^m` tends to `1_{z=1}`:
- it equals `1` if `z = 1`;
- it is bounded by `|z|/(M(1 − |z|))` if `|z| < 1`;
- it is bounded by `2/(M|1 − z|)` if `|z| = 1` and `z ≠ 1`.

It is bounded by `1`, so dominated convergence gives

`(3.2)   c_k = P(ν̂(k) = 1).`

## Step 4. Parts 1 and 2 of the theorem

`ν̂(k) = 1` holds iff `ν` is carried by `{θ : kθ = 0 in T}`. For `k = 1` this set is `{0}`, so (3.2)
gives `c_1 = P(ν = δ_0)`. Since `{ν = δ_0} ⊆ {ν̂(k) = 1}`,

`φ(k·1_{[0]}) = c_k ≥ c_1 = φ(1_{[0]}) ≥ 0`,

and every `c_k` is real by (3.2). With Step 1 this proves part 1 for every proper `U`. (For `k = 0`
it reads `1 ≥ c_1`.)

For part 2, let `ψ` be `V`-invariant and cnd on `A` with `ψ(0) = 0`. By (I2), `φ_t = e^{-tψ}` is
positive definite with `φ_t(0) = 1`, and `V`-invariant. Part 1 gives
`e^{-tψ(k·1_U)} ≥ e^{-tψ(1_U)}`, so `ψ(k·1_U) ≤ ψ(1_U)` (both are real because `ψ = ‖b‖²`).

`V` maps `[0]` to `[1]`, so `ψ(1_{[1]}) = ψ(1_{[0]})`. Since `k·1_C = k·1_{[0]} + k·1_{[1]}`, the
subadditivity in (I2) gives

`√ψ(k·1_C) ≤ √ψ(k·1_{[0]}) + √ψ(k·1_{[1]}) ≤ 2√ψ(1_{[0]})`,

so `ψ(k·1_C) ≤ 4ψ(1_{[0]})`.

## Step 5. Real laws are trivial (the `L^α` and `E g(X)` constructions)

Let `X` be a random homomorphism `A → R` whose law is `V`-invariant. For `t ∈ R`, the function
`φ_t(f) = E e(tX(f))` is positive definite, `V`-invariant, and has `φ_t(0) = 1`. Write
`r(t) = Re φ_t(1_{[0]}) = E cos(2πtX(1_{[0]}))`.

Part 1 gives `r(t) ≤ Re φ_t(k·1_{[0]}) = r(kt)` for every `k ≥ 1`. Average over `k = 1, …, K`. As
`K → ∞`, `(1/K) Σ_k cos(2πktx)` tends to `1_{tx ∈ Z}`, with bound `1`. Dominated convergence gives

`r(t) ≤ P(tX(1_{[0]}) ∈ Z).`

`X(1_{[0]})` has at most countably many atoms, so for all `t` outside a countable set,
`P(tX(1_{[0]}) ∈ Z ∖ {0}) = 0` and hence `r(t) ≤ P(X(1_{[0]}) = 0)`. Let `t → 0` through such `t`.
Then `r(t) → 1`, so `X(1_{[0]}) = 0` a.s. By Step 1 the same holds for every proper `U`, and
`X(1_C) = X(1_{[0]}) + X(1_{[1]}) = 0` a.s.

So no `V`-invariant law of random real homomorphisms moves `1_C`. This kills, among others:
- `ψ(f) = Σ_j E(1 − e^{-s_j X(f)²})`;
- `ψ(f) = E|X(f)|^α`;
- every `L^α` embedding whose norm depends only on the image set.

## Step 6. Part 3: cnd functions on G bounded on V

Let `ψ = ‖b‖²` on `G`, where `b` is a cocycle for an orthogonal representation `π`, and assume
`sup_V ‖b‖ < ∞`. The affine action `α(g)x = π(g)x + b(g)` then has a bounded `V`-orbit, so by (I4)
it has a `V`-fixed point `ξ`. Put `b'(g) = α(g)ξ − ξ = b(g) + π(g)ξ − ξ`. This is a cocycle with:
- `b'(v) = 0` for all `v ∈ V`;
- `‖b(g)‖ ≤ ‖b'(g)‖ + 2‖ξ‖`.

In `G`, `v f v^{-1} = v·f`, so the cocycle identity gives `b'(v·f) = π(v) b'(f)`. So
`ψ'(f) = ‖b'(f)‖²` is a `V`-invariant cnd function on `A` with `ψ'(0) = 0`. By part 2,
`ψ'(k·1_C) ≤ 4ψ'(1_{[0]})` for all `k`. Hence

`sup_k ψ(k·1_C) ≤ (2√ψ'(1_{[0]}) + 2‖ξ‖)² < ∞`. ∎

## Where the argument stops

- Step 2(a) uses the elements `v_σ` for all `σ ∈ S_n` and all `n`.
- Step 3 uses the partial sums `S_m` for all `m`.

A law that is only `ε`-invariant under a fixed finite `F ⊂ V` gives approximate exchangeability for
boundedly many phases only. The Cesàro limit then does not exist uniformly, so nothing survives for
the V-almost-invariant laws of `cantor-integer-maps-central-growth-criterion` with non-vanishing
defect. A quantitative version would need the defect to be small under the unbounded families
`{v_σ}` and `{w_m}` at once. That is exactly what almost invariance does not give.
