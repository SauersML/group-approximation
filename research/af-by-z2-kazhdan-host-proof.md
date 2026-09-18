---
rg: 2
id: af-by-z2-kazhdan-host-proof
kind: route
title: "Proof: every arrow of Γ⋉Ω has a chart (a generator s_{v̄,ū} whose image is u_γ1_{Ω[ū]}); the gauge action and injectivity of φ make the shape offset of the chart independent of the chart; same-shape charts give compact open principal subgroupoids exhausting the kernel; simplicity against an augmentation representation gives topological freeness"
target: af-by-z2-ample-groupoid-full-group-contains-infinite-kazhdan
requires:
  - rs-boundary-groupoid-is-expansive-amenable-kazhdan-host
  - robertson-steger-boundary-cylinders-and-pure-infiniteness
  - robertson-steger-a2-boundary-algebras-are-rank-two-ck
  - robertson-steger-rank-two-ck-algebra-gauge-action
  - robertson-steger-word-products-and-boundary-topology
---

## References and conventions

**Abbreviations.**
- [H] is `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`, items 1-7.
- [RS-C] is `robertson-steger-boundary-cylinders-and-pure-infiniteness`: (rel1), `f2`,
  Lemma `5`, Corollary `4`, the formula for φ, `c1`, `c2`, main2 and the Remark.
- [RS-I] is `robertson-steger-a2-boundary-algebras-are-rank-two-ck`: φ is an
  isomorphism `𝒜 → C(Ω)⋊Γ`, in particular **injective**.
- [RS-G] is `robertson-steger-rank-two-ck-algebra-gauge-action`: the automorphisms
  `α_t`, `t ∈ T²`, with `α_t(s_{u,v}) = t^{σ(u)-σ(v)}s_{u,v}`.
- [RS-W] is `robertson-steger-word-products-and-boundary-topology`: `D` and `A` finite,
  so each `W̄_m` is finite; restrictions and (H1); the boundary topology.

All hypotheses of these imports hold in the setting of the target (a lattice in
`PGL_3(K)`, `K` nonarchimedean of characteristic zero, type rotating, free on vertices,
finitely many vertex orbits); there `r = 2`.

**Crossed product facts** (textbook, as in [H]'s proof):
- (CP1) the faithful conditional expectation `E: C(Ω)⋊Γ → C(Ω)`, `E(f u_γ) = δ_{γ,1} f`;
- (CP2) `u_γ f u_γ^* = f∘γ^{-1}`, hence `u_γ 1_U = 1_{γU} u_γ` for clopen `U`;
- (CP3) universal property of the full crossed product: a covariant pair `(π, λ)` on a
  Hilbert space gives a *-homomorphism `Π` with `Π(f u_h) = π(f)λ(h)`;
- (CP4) `C(Ω)⋊Γ` is simple (Remark in [RS-C]).

**Cells and group elements.** For `ū ∈ W̄` put `Ω[ū] = Ω(ᾱ^{-1}ū)`, a clopen set. For
`ū, v̄ ∈ W̄` with `t(ū) = t(v̄)`, `g(v̄,ū) ∈ Γ` is the element `γ` of the formula for φ, so
`φ(s_{v̄,ū}) = u_{g(v̄,ū)}1_{Ω[ū]} = 1_{Ω[v̄]}u_{g(v̄,ū)}`, and `φ(s_{ū,ū}) = 1_{Ω[ū]}`.
Concatenation `ūw` (for `o(w) = t(ū)`) is Corollary `4`; it has shape `σ(ū)+σ(w)` and
`t(ūw) = t(w)`.

## Lemma A (restated from the proof of [H])

These are Lemma A (a)-(d) of `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host-proof`.
Their proofs there use only [RS-C] and [RS-W]; they are recalled in one line each.

Let `t(ū) = t(v̄)` and `g = g(v̄,ū)`.
- **(a)** `gΩ[ū] = Ω[v̄]`. From `1_{gΩ[ū]}u_g = u_g1_{Ω[ū]} = 1_{Ω[v̄]}u_g` (CP2).
- **(b)** For each `m`, the cells `Ω[x̄]`, `x̄ ∈ W̄_m`, partition `Ω`. This is `c1`, read
  pointwise.
- **(c)** For `n ∈ Z²_+`, `Ω[ū] = ⊔ Ω[ūw]` over `w ∈ W_n` with `o(w) = t(ū)`. Apply φ to
  `f2` with `u = v = ū`.
- **(d1)** `s_{v̄,ū}s_{ūw,ūw} = s_{v̄w,ūw}` for `w ∈ W_n`, `o(w) = t(ū)`. Expand
  `s_{v̄,ū}` by `f2`; Lemma `5` kills the terms `w' ≠ w` (their words `ūw' ≠ ūw` have
  equal shape, by (H1) and Corollary `4`).
- **(d)** `gΩ[ūw] = Ω[v̄w]`. Conjugate (d1) and apply φ.

## Step 0. Standing properties (item 1 of the target)

Item 1 is items 1-6 of [H], with `R = Γ × Ω` as there. `R` is Hausdorff and second
countable (`Γ` is countable and discrete, `Ω` is a compact metrizable Cantor set), étale,
and ample, since the compact open bisections `{γ} × U`, `U` clopen, form a basis.

## Step 1. E-uniqueness

**Lemma E.** If `a, b ∈ Γ`, `U ⊆ Ω` is a nonempty clopen set and `u_a1_U = u_b1_U`, then
`a = b`.

*Proof.* Multiply on the left by `u_b^*`: `u_{b^{-1}a}1_U = 1_U`. If `b^{-1}a ≠ 1`, then
by (CP2) and (CP1) `E(u_{b^{-1}a}1_U) = E(1_{b^{-1}aU}u_{b^{-1}a}) = 0`, while
`E(1_U) = 1_U ≠ 0`. ∎

**Corollary E1.** `g(ū,ū) = 1` whenever `Ω[ū] ≠ ∅`: `u_{g(ū,ū)}1_{Ω[ū]} = φ(s_{ū,ū}) = u_1 1_{Ω[ū]}`.

## Step 2. Charts

**Definition.** For `(γ,ω) ∈ R`, a *`γ`-chart at `ω`* is a pair `(ū,v̄)` in `W̄` with
`t(ū) = t(v̄)`, `ω ∈ Ω[ū]` and `g(v̄,ū) = γ`. Its *degree* is `σ(v̄) - σ(ū) ∈ Z²`.

By Lemma E (with `U = Ω[ū] ∋ ω`), `(ū,v̄)` with `t(ū) = t(v̄)` and `ω ∈ Ω[ū]` is a
`γ`-chart at `ω` iff `u_γ1_{Ω[ū]} = φ(s_{v̄,ū})`. With `ū = ᾱ(p)`, `v̄ = ᾱ(p')` this is
exactly the condition `γ1_{Ω(p)} = φ(s_{ᾱ(p'),ᾱ(p)})`, `ω ∈ Ω(p)`, of item 3 of the
target. A `γ`-chart at `ω` is a `γ`-chart at every point of `Ω[ū]`.

**(C0) Existence at every shape `(N,N)` with `N ≥ d(O,γ^{-1}O)`.** Let `m = (N,N)`. By
(b) there is a unique `ū ∈ W̄_m` with `ω ∈ Ω[ū]`; let `p = ᾱ^{-1}(ū) ∈ 𝔚̄_m`. By main2
in [RS-C] (item 5), there is `p' ∈ 𝔚̄` with `γ1_{Ω(p)} = φ(s_{ᾱ(p'),ᾱ(p)})`. So
`(ū, ᾱ(p'))` is a `γ`-chart at `ω`, with `ū ∈ W̄_{(N,N)}`.

**(C1) Refinement.** If `(ū,v̄)` is a `γ`-chart at `ω`, `n ∈ Z²_+`, `w ∈ W_n`,
`o(w) = t(ū)` and `ω ∈ Ω[ūw]`, then `(ūw, v̄w)` is a `γ`-chart at `ω` of the same degree.

*Proof.* `t(ūw) = t(w) = t(v̄w)`. Apply φ to (d1), using `Ω[ūw] ⊆ Ω[ū]` from (c):
`φ(s_{v̄w,ūw}) = u_γ1_{Ω[ū]}1_{Ω[ūw]} = u_γ1_{Ω[ūw]}`. Lemma E with `U = Ω[ūw] ∋ ω`
gives `g(v̄w,ūw) = γ`. The degree is `(σ(v̄)+n) - (σ(ū)+n)`. ∎

By (c), for every `n` such a `w` exists and is unique.

**(C2) Inverse.** If `(ū,v̄)` is a `γ`-chart at `ω`, then `(v̄,ū)` is a `γ^{-1}`-chart at
`γω`, of opposite degree.

*Proof.* `γω ∈ γΩ[ū] = Ω[v̄]` by (a). By (rel1a) and (CP2),
`φ(s_{ū,v̄}) = φ(s_{v̄,ū})^* = 1_{Ω[ū]}u_γ^* = u_{γ^{-1}}1_{γΩ[ū]} = u_{γ^{-1}}1_{Ω[v̄]}`.
Lemma E with `U = Ω[v̄]`. ∎

**(C3) Composition.** If `(ā,b̄)` is a `γ`-chart at `ω` and `(b̄,c̄)` is a `δ`-chart at
`γω`, then `(ā,c̄)` is a `δγ`-chart at `ω`, and its degree is the sum of the two degrees.

*Proof.* `t(ā) = t(b̄) = t(c̄)` and `ω ∈ Ω[ā]`. By (rel1b), `s_{c̄,b̄}s_{b̄,ā} = s_{c̄,ā}`.
Apply φ, using (CP2) and `γ^{-1}Ω[b̄] = Ω[ā]` from (a):
`φ(s_{c̄,ā}) = u_δ1_{Ω[b̄]}u_γ1_{Ω[ā]} = u_{δγ}1_{γ^{-1}Ω[b̄]}1_{Ω[ā]} = u_{δγ}1_{Ω[ā]}`.
Lemma E with `U = Ω[ā]`. The degree is `(σ(c̄)-σ(b̄)) + (σ(b̄)-σ(ā))`. ∎

## Step 3. The degree does not depend on the chart (gauge action)

**Lemma D.** Any two `γ`-charts `(ū,v̄)` and `(x̄,ȳ)` at the same `ω` have the same degree.

*Proof.* Let `n = σ(v̄) - σ(ū)` and `n' = σ(ȳ) - σ(x̄)`, and put `x = s_{ū,ū}s_{x̄,x̄} ∈ 𝒜`.
- By [RS-G], `α_t(x) = x` for all `t ∈ T²`, since both factors have equal source and
  range shapes.
- `φ(s_{v̄,ū}x) = u_γ1_{Ω[ū]}1_{Ω[ū]}1_{Ω[x̄]} = u_γ1_{Ω[ū]∩Ω[x̄]}` and
  `φ(s_{ȳ,x̄}x) = u_γ1_{Ω[x̄]}1_{Ω[ū]}1_{Ω[x̄]} = u_γ1_{Ω[ū]∩Ω[x̄]}`.
  By injectivity of φ ([RS-I]), `y := s_{v̄,ū}x = s_{ȳ,x̄}x`.
- `y ≠ 0`: `φ(y)^*φ(y) = 1_{Ω[ū]∩Ω[x̄]}`, which is nonzero because it takes the value `1` at `ω`.
- Since `α_t` is multiplicative, `α_t(y) = t^n y` (first expression) and `α_t(y) = t^{n'} y`
  (second expression). So `t^n = t^{n'}` for all `t ∈ T²`, and `n = n'`. ∎

**Definition of c.** `c(γ,ω)` is the degree of any `γ`-chart at `ω`. It exists by (C0),
and it is well defined by Lemma D. By the reformulation in Step 2, this is precisely the
function described in item 3 of the target, and that description determines it
uniquely, because every arrow has a chart.

## Step 4. c is a continuous cocycle

**Continuity.** A `γ`-chart `(ū,v̄)` at `ω` is a `γ`-chart at every `ω' ∈ Ω[ū]`. So `c` is
constant on the open set `{γ} × Ω[ū] ∋ (γ,ω)` of `R`. Hence `c` is locally constant, and so
continuous.

**Cocycle identity.** Let `(γ,ω)` and `(δ,γω)` be composable in `R`. Take a `γ`-chart
`(ā,b̄)` at `ω` and a `δ`-chart `(x̄,ȳ)` at `γω`.
- `γω ∈ Ω[b̄]` by (a), and `γω ∈ Ω[x̄]`. Choose `k ∈ Z²_+` with `k ≥ σ(b̄), σ(x̄)`
  coordinatewise.
- By (c), `γω ∈ Ω[b̄w]` for a unique `w` of shape `k - σ(b̄)` with `o(w) = t(b̄)`, and
  `γω ∈ Ω[x̄w']` for a unique `w'` of shape `k - σ(x̄)` with `o(w') = t(x̄)`.
- Both `b̄w` and `x̄w'` lie in `W̄_k` and their cells contain `γω`, so by (b)
  `b̄w = x̄w' =: z̄`.
- By (d), `γΩ[āw] = Ω[b̄w] ∋ γω`, so `ω ∈ Ω[āw]`. By (C1), `(āw, z̄)` is a `γ`-chart at
  `ω` and `(z̄, ȳw')` is a `δ`-chart at `γω`, with the degrees `c(γ,ω)` and `c(δ,γω)`.
- By (C3), `(āw, ȳw')` is a `δγ`-chart at `ω` of degree `c(γ,ω) + c(δ,γω)`.

So `c(δγ,ω) = c(δ,γω) + c(γ,ω)`, and `c: R → Z²` is a continuous groupoid homomorphism.
This proves item 3.

## Step 5. The kernel is AF (item 4)

For `m ∈ Z²_+` let `K_m` be the set of `(γ,ω) ∈ R` having a `γ`-chart `(ū,v̄)` at `ω` with
`ū, v̄ ∈ W̄_m`. Equivalently,

`K_m = ⋃ {g(v̄,ū)} × Ω[ū]`, over pairs `(ū,v̄) ∈ W̄_m × W̄_m` with `t(ū) = t(v̄)`.

This is the set of item 4 of the target: `γ|_{Ω(p)}` is the prefix replacement
`ᾱ(p) ⇒ ᾱ(p')` of (d), with `p, p' ∈ 𝔚̄_m`.

**(K1) Compact open.** `W̄_m` is finite ([RS-W]), so `K_m` is a finite union of the compact
open sets `{g} × Ω[ū]` of `R`.

**(K2) Contains the units.** For `ω ∈ Ω`, (b) gives `ū ∈ W̄_m` with `ω ∈ Ω[ū]`, and
`(ū,ū)` is a `1`-chart at `ω` by Corollary E1. So `(1,ω) ∈ K_m`.

**(K3) Inverses.** By (C2), with both words still in `W̄_m`.

**(K4) Products.** Let `(γ,ω), (δ,γω) ∈ K_m`, with a `γ`-chart `(ā,b̄)` at `ω` and a
`δ`-chart `(b̄',c̄)` at `γω`, all four words in `W̄_m`. Then `γω ∈ Ω[b̄]` by (a) and
`γω ∈ Ω[b̄']`, so `b̄ = b̄'` by (b). By (C3), `(ā,c̄)` is a `δγ`-chart at `ω`, so
`(δγ,ω) ∈ K_m`.

**(K5) Principal.** Let `(γ,ω) ∈ K_m` with `γω = ω`, via a chart `(ū,v̄)` in `W̄_m`. Then
`ω ∈ Ω[ū]` and `ω = γω ∈ Ω[v̄]` by (a), so `ū = v̄` by (b), and `γ = g(ū,ū) = 1` by
Corollary E1. So the isotropy of `K_m` is its unit space.

**(K6) Increasing.** `K_m ⊆ K_{m+e_j}`: given a chart `(ū,v̄)` in `W̄_m` at `ω`, (c) gives
`w ∈ W_{e_j}` with `o(w) = t(ū)` and `ω ∈ Ω[ūw]`, and (C1) gives the chart `(ūw,v̄w)` in
`W̄_{m+e_j}`. Hence `K_{(N,N)} ⊆ K_{(N+1,N+1)}`.

**(K7) Exhaustion of the kernel.**
- `K_m ⊆ ker c`, because a chart in `W̄_m × W̄_m` has degree `0`.
- Conversely, let `c(γ,ω) = 0` and `N ≥ d(O,γ^{-1}O)`. The chart `(ū,v̄)` of (C0) has
  `ū ∈ W̄_{(N,N)}`, and its degree is `c(γ,ω) = 0` by Lemma D. So `σ(v̄) = (N,N)`, that is
  `v̄ ∈ W̄_{(N,N)}`, and `(γ,ω) ∈ K_{(N,N)}`.

So `ker c = ⋃_N K_{(N,N)}`.

**Conclusion.** `ker c = c^{-1}(0)` is an open subgroupoid of `R` (`c` is a continuous
homomorphism to a discrete group), hence étale, with unit space `Ω`. It is the increasing
union of the compact open principal subgroupoids `K_{(N,N)}`, each with unit space `Ω`.
So `ker c` is AF in Matui's sense. This proves item 4.

## Step 6. Topological freeness (item 2)

**Claim.** For `γ ≠ 1`, `Fix(γ) = {ω : γω = ω}` has empty interior.

*Proof.* Suppose `γ ≠ 1` fixes a nonempty open set pointwise. By `c2` it contains a
nonempty clopen cell `U`, so `γ` fixes `U` pointwise. Fix `ω ∈ U`, let
`Γ_ω = {h : hω = ω}`, and let `H = ℓ²(Γ/Γ_ω)` with basis `δ_{gΓ_ω}`.
- `π(f)δ_{gΓ_ω} = f(gω)δ_{gΓ_ω}` defines a unital representation of `C(Ω)`. It is well
  defined because `gω` depends only on `gΓ_ω`.
- `λ(h)δ_{gΓ_ω} = δ_{hgΓ_ω}` is a unitary representation of `Γ`.
- Covariance: `λ(h)π(f)λ(h)^*δ_{gΓ_ω} = f(h^{-1}gω)δ_{gΓ_ω} = π(f∘h^{-1})δ_{gΓ_ω}`,
  matching (CP2).
- By (CP3) there is a *-homomorphism `Π: C(Ω)⋊Γ → B(H)` with `Π(fu_h) = π(f)λ(h)`, and
  `Π(1) = 1 ≠ 0`.
- `Π(u_γ1_U)δ_{gΓ_ω} = 1_U(gω)δ_{γgΓ_ω}`. If `gω ∈ U` then `γgω = gω`, so
  `g^{-1}γg ∈ Γ_ω` and `γgΓ_ω = gΓ_ω`. Hence `Π(u_γ1_U) = Π(1_U)`.
- `u_γ1_U - 1_U ≠ 0`, because by (CP1), (CP2) and `γ ≠ 1`,
  `E(u_γ1_U - 1_U) = E(1_{γU}u_γ) - 1_U = -1_U ≠ 0`.

So `ker Π` is a closed two-sided ideal that is nonzero and proper, contradicting (CP4). ∎

**Consequences.**
- *Effective.* `Iso(R) \ R^{(0)} = {(γ,ω) : γ ≠ 1, γω = ω}`. If it had an interior point
  `(γ,ω)`, some basic open `{γ} × V`, `V ∋ ω` open, would lie in it, so `γ ≠ 1` would fix
  `V` pointwise. So its interior is empty.
- *Topologically principal.* The units with trivial isotropy are
  `Ω \ ⋃_{γ≠1} Fix(γ)`. Each `Fix(γ)` is closed (`Ω` is Hausdorff) with empty interior,
  and `Γ` is countable. By the Baire category theorem on the compact Hausdorff space `Ω`,
  the complement is dense.
- *R is the germ groupoid.* The map `(γ,ω) ↦ [γ,ω]` onto the germ groupoid of `Γ ↷ Ω`
  is a surjective groupoid homomorphism. It carries each basic bisection `{γ} × U` onto
  the basic set of germs of `γ` over `U`, so it is continuous and open. It is injective:
  `[γ,ω] = [δ,ω]` means `δ^{-1}γ` fixes a neighbourhood of `ω` pointwise, so
  `δ^{-1}γ = 1` by the Claim. Hence it is an isomorphism of topological groupoids.

This proves item 2.

## Step 7. All ranks k ≥ 2 (item 5) and the conclusion

For `k ≥ 2`, `c_k = (c, 0, …, 0) = ι∘c`, where `ι: Z² → Z^k` is the injective inclusion
of the first two coordinates. So `c_k` is a continuous groupoid homomorphism, and
`ker c_k = ker c`, which is AF by Step 5. This proves item 5.

By Steps 0 and 6, `R` is a minimal, effective, ample groupoid (second countable,
Hausdorff, Cantor unit space). By Step 7 it carries a continuous `Z^k` cocycle with AF
kernel for each `k ≥ 2`. By item 6 of [H], `γ ↦ {γ} × Ω` embeds the infinite Kazhdan
group `Γ` in `[[R]]`. This gives the Consequences recorded in the target.

