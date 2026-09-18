---
rg: 2
id: nv-extractable-cocycles-bounded-on-centralizers-proof
kind: route
title: "Paradoxical gap of one coordinate copy of V plus the commuting-cocycle identity bounds the cocycle on the other coordinates"
target: nv-extractable-cocycles-bounded-on-centralizers
requires:
  - brin-thompson-nv-haagerup-iff-proper-modulo-triangular
---

Notation as in the target. Norms of vectors are `‖·‖`, norms in `H` are `|·|`. The only
imports are the displayed formula of `brin-thompson-nv-haagerup-iff-proper-modulo-triangular`
(used only in Corollary 4), plus three standard facts.
- (S1) An amenable group acting on a compact metrizable space fixes a Borel probability
  measure.
- (S2) Weak containment `σ ≺ ρ`: every function of positive type associated to `σ` is a
  pointwise limit (the group is discrete) of finite sums of functions of positive type
  associated to `ρ` (Bekka–de la Harpe–Valette, *Kazhdan's property (T)*, Appendix F,
  Definition F.1.1; not re-read at source).
- (S3) Change of variables for a quasi-invariant measure: `∫ F (d g_*μ/dμ) dμ = ∫ F∘g dμ`.

**Step 0 (the subgroups `E_j`).** Let `ψ ∈ (n−1)V` act on `C^{n−1}` by a brick table
`(u_k z_k)_{k} ↦ (v_k z_k)_{k}`, indexed by the coordinates `k ≠ j`. Insert the empty word in
coordinate `j` on both sides of every row of the table. The result is a brick table on `C^n`,
because the bricks `[u] × C` (with `C` in slot `j`) partition `C^n`. So it defines
`ψ^{[j]} ∈ nV`, which acts by `ψ` on the coordinates other than `j` and leaves `x_j` unchanged.
- The map `ψ ↦ ψ^{[j]}` is an injective homomorphism. Its image `E_j` is isomorphic to `(n−1)V`,
  hence infinite.
- `ψ^{[j]}` and `h^{(j)}` act on disjoint sets of coordinates, so they commute. Hence
  `E_j ⊆ Z_j`.
- For `k ≠ j`, `h^{(k)} = (h acting on coordinate k of C^{n−1})^{[j]}`, so `V_{(k)} ⊆ E_j`.

**Step 1 (gap).** Let `ρ` be `j`-extractable, and let `r ∈ K` with `‖r‖ = 1`. Put `ν = μ_r`,
a probability measure on `C`. Write `β_i = β^{(j)}_i`, and let
`δ = max_{i,B} |h_{i*}ν(B) − ν(B)|`. By the equivariance and continuity axioms, with `s = ρ(β_i) r`
(a unit vector),

`|h_{i*}ν(B) − ν(B)| = |μ_{ρ(β_i) r}(B) − μ_r(B)| ≤ 2‖ρ(β_i) r − r‖`.

Now use the three elements. (This is the computation of Step 3 of
`nv-vertically-triangular-chart-cocycles-are-bounded-proof`, repeated so that the route is
self-contained.)
- `h_1^{-1}[00] = [0]` gives `|ν[0] − ν[00]| ≤ δ`, that is `ν[01] ≤ δ`.
- `h_2^{-1}[01] = [0]` gives `|ν[0] − ν[01]| ≤ δ`, that is `ν[00] ≤ δ`. So `ν[0] ≤ 2δ`.
- `h_3^{-1}[1] = [0]` gives `ν[1] ≤ ν[0] + δ ≤ 3δ`.

So `1 = ν(C) ≤ 5δ ≤ 10 max_i ‖ρ(β_i) r − r‖`. Squaring and scaling gives, for all `r ∈ K`,

`‖r‖² ≤ 100 max_i ‖r − ρ(β_i) r‖² ≤ 100 Σ_{i=1}^{3} ‖r − ρ(β_i) r‖².` (1)

**Step 2 (commuting identity).** Let `b` be a 1-cocycle, `b(gh) = b(g) + ρ(g) b(h)`, and let
`a ∈ Z_j`. From `a β_i = β_i a`,

`b(a) + ρ(a) b(β_i) = b(β_i) + ρ(β_i) b(a)`, so `(1 − ρ(β_i)) b(a) = (1 − ρ(a)) b(β_i)`.

Since `ρ(a)` is unitary, `‖(1 − ρ(a)) b(β_i)‖ ≤ 2‖b(β_i)‖`. Apply (1) to `r = b(a)`:

`‖b(a)‖² ≤ 100 Σ_i ‖(1 − ρ(β_i)) b(a)‖² ≤ 400 Σ_i ‖b(β_i)‖².`

Only (1) was used, so Step 2 holds for every `ρ` that satisfies (1). ∎ (Theorem)

**Step 3 (the examples are coordinate-extractable).** All examples are special cases of one
construction. Let `Ω` be a standard Borel `G`-space with a σ-finite quasi-invariant measure `μ`,
let `p: Ω → Prob(C^n)` be Borel with `p(gω) = g_* p(ω)`, and let `π` be a unitary
representation of `G` on a separable `H`. Let `ρ` act on `L²(Ω, μ; H)` by
`(ρ(g) f)(ω) = √(d g_*μ/dμ)(ω) π(g) f(g^{-1}ω)`. Fix `j` and put

`μ_f(B) = ∫_Ω |f(ω)|² p(ω)(pr_j^{-1} B) dμ(ω)`.

- *Mass.* `μ_f(C) = ‖f‖²`, since each `p(ω)` is a probability measure.
- *Equivariance.* Let `g = h^{(j)}`, so that `pr_j ∘ g = h ∘ pr_j` and
  `g^{-1}(pr_j^{-1} B) = pr_j^{-1}(h^{-1} B)`. By (S3), then `p(gω') = g_* p(ω')`:

  `μ_{ρ(g)f}(B) = ∫ |f(g^{-1}ω)|² p(ω)(pr_j^{-1}B) (d g_*μ/dμ)(ω) dμ(ω)`
  `= ∫ |f(ω')|² p(gω')(pr_j^{-1}B) dμ(ω') = ∫ |f(ω')|² p(ω')(pr_j^{-1} h^{-1} B) dμ(ω') = (h_*μ_f)(B)`.

  The first equality uses `|π(g)ξ| = |ξ|`.
- *Continuity.* `|μ_f(B) − μ_{f'}(B)| ≤ ∫ ||f|² − |f'|²| dμ ≤ ∫ |f − f'| (|f| + |f'|) dμ ≤ ‖f − f'‖(‖f‖ + ‖f'‖)`,
  by Cauchy–Schwarz.

Now the examples.
- *Countable `Ω` with counting measure* (the Radon–Nikodym factor is 1). This gives `ℓ²(X; H)`
  for every `G`-set `X` with an equivariant map `m: X → Prob(C^n)`.
  - *Charts:* `X` a `G`-invariant set of charts with `g·φ = g∘φ`, and `m(φ) = φ_*λ`, so that
    `m(g∘φ) = g_* m(φ)`. Then `μ_r = Σ_φ |r(φ)|² (pr_j∘φ)_*λ`, the extraction of the target.
  - *Quasi-regular:* `X = G/L` where `L` fixes some `μ_L ∈ Prob(C^n)` (every amenable `L`, by
    (S1); every point stabilizer, with `μ_L = δ_x`; every rigid stabilizer of a clopen set `W`,
    with `δ_x` for some `x ∉ W`). Put `m(gL) = g_* μ_L`, which is well defined because
    `L_* μ_L = μ_L`. With `L = 1` this is the regular representation.
- *`Ω = C^n` with `λ` and `p(x) = δ_x`.* This is the Koopman representation on `L²(C^n, λ; H)`,
  quasi-invariant because every element of `nV` is piecewise a brick map, which scales `λ` by a
  locally constant power of 2. This is the setting of the Koopman wavelet attempt recorded in
  `brin-thompson-nv-cnd-proper-on-cocycle-kernel`.

**Step 4 (closure of inequality (1)).** Fix `j`.
- *Direct sums.* Both sides of (1) are additive over orthogonal summands.
- *Subrepresentations.* Restrict (1).
- *Unitary conjugates.* `(ρ∘Ad(t))(β_i) = ρ(t) ρ(β_i) ρ(t)^{-1}`. With `s = ρ(t)^{-1} r`,
  `‖r − ρ(t)ρ(β_i)ρ(t)^{-1} r‖ = ‖s − ρ(β_i) s‖` and `‖r‖ = ‖s‖`.
- *Weak containment.* For a unit vector `r`, put `φ_r(g) = ⟨ρ(g) r, r⟩`. Inequality (1) reads

  `Σ_i (2φ_r(e) − φ_r(β_i) − φ_r(β_i^{-1})) − φ_r(e)/100 ≥ 0`.

  This condition is linear in `φ_r`, holds for every function of positive type associated to
  `ρ`, and is preserved under finite sums and pointwise limits. By (S2) it holds for every `σ ≺ ρ`.
- *Coordinate permutations.* `α_σ^{-1}(h^{(j)}) = h^{(j')}` for a coordinate `j'` depending
  only on `σ` and `j`. So if `ρ` satisfies (1) for every `j`, so does `ρ∘α_σ^{-1}`.

**Step 5 (corollaries).** Let `ρ` satisfy (1) for some `j`, let `b` be a cocycle into `ρ`, and
put `ψ = ‖b‖²`. Pick `k ≠ j`, which exists since `n ≥ 2`. By Steps 0 and 2, `ψ` is bounded on
`E_j ⊇ V_{(k)}`.
1. *Not proper.* `E_j` is infinite.
2. *Not P3.* A permutation `σ` of the level-`m` cylinders of `C` by prefix replacement of equal
   length has `c(σ^{(k)}) = 0`. The elements `σ^{(k)}` (`m ≥ 1`, `σ ∈ Sym(2^m)`) form an
   infinite subset of `K ∩ E_j` on which `ψ` is bounded.
3. *Not P1, not P2.* Here `c(h^{(k)})(x) = c(h)(x_k) e_k`, with the exponent cocycle
   `c(g)(x) = (|v_i| − |u_i|)_i` of `brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination`.
   - `h_1^N(0t) = 0^{N+1} t`, so `‖c((h_1^N)^{(k)})‖ ≥ N`.
   - For `g_m` as in the target, the brick table of `g_m` has rows `0^m 0 ↦ 0^m 00`,
     `0^m 10 ↦ 0^m 01`, `0^m 11 ↦ 0^m 1`, and the identity on `[w]` for the other words `w` of
     length `m`. So `c(g_m) = +1` on `[0^m 0]` and `−1` on `[0^m 11]`. That is not constant on
     the level-`m` cube `[0^m]`, so `pd ≥ m + 1`.

   `ψ` is bounded along both families, so no `F → ∞` has `ψ ≥ F(‖c‖)` or `ψ ≥ F(pd)`.
4. *Not R1.* Let `ρ` satisfy (1) for every `j`, and suppose `ψ` is proper modulo `T_n`.
   - By `brin-thompson-nv-haagerup-iff-proper-modulo-triangular`,
     `Ψ = Σ_{t,σ} ψ∘α_σ^{-1}∘Ad(t)` is a proper cnd function. The sum is finite, the `t` are
     shears in `nV`, and `α_σ = Ad σ̂` is a coordinate permutation.
   - Each term is `‖b_{σ,t}‖²` with `b_{σ,t} = b∘α_σ^{-1}∘Ad(t)`, a cocycle into
     `ρ_{σ,t} = ρ∘α_σ^{-1}∘Ad(t)`. It is a cocycle because `α_σ^{-1}∘Ad(t)` is an automorphism.
   - By Step 4, each `ρ_{σ,t}` satisfies (1) for every `j`, and so does `⊕ρ_{σ,t}`.
   - So `Ψ = ‖⊕ b_{σ,t}‖²` is bounded on `E_1` by Step 2, a contradiction with properness.
   - For `n ≥ 3` there is also a direct argument. `ψ` is bounded on `E_n ⊇ A = (n−1)V × id`.
     From the definition of `T_n`, `A ∩ T_n = T_{n−1} × id`. If `A` lay in finitely many left
     cosets `g T_n`, then `A` would be a finite union of cosets `a(A ∩ T_n)`, so `T_{n−1}` would
     have finite index in `(n−1)V`. The first route avoids this and needs nothing about `T_{n−1}`.
5. *Shape of a witness.* Let `b` be a proper cocycle into any `ρ`, and fix `j` and `t ∈ G`.
   - `b∘Ad(t)` is a proper cocycle into `ρ∘Ad(t)`.
   - If `ρ∘Ad(t)` satisfied (1) for `j`, then Corollary 1 would fail. So
     `ρ|_{t ⟨β^{(j)}_i⟩ t^{-1}}` does not satisfy (1).
   - The constant 100 in (1) is not special. The argument of Step 2 gives the same conclusion with any
     constant, so this restriction has almost invariant vectors.
   - By Step 3 and Step 4, `ρ` is then not weakly contained in any `j`-extractable representation.
   ∎

**Where the class dies.**
- *Invariant.* A measure extraction in coordinate `j` gives a uniform spectral gap for the
  three elements `h_i^{(j)}`, by the paradoxical inequality `1 ≤ 5δ`.
- *Step where every member dies.* Step 2: the cocycle identity for a commuting pair turns the
  gap into a uniform bound on the centralizer, which contains the other `n − 1` coordinates.
- *Contrast with the sweep.* The sweep of `nv-vertically-triangular-chart-cocycles-are-bounded-proof`
  is not needed, because this argument uses no support condition. The price is that the bound holds
  on `E_j` only, not on all of `nV`.
