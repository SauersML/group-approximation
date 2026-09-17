---
rg: 2
id: rank-two-prefix-replacement-kazhdan-proof
kind: route
title: Proof — the formula for φ turns each lattice element into cylinder prefix replacements, simplicity gives faithfulness, pure infiniteness kills invariant measures, and Kazhdan's theorem gives (T)
target: rank-two-prefix-replacement-groups-contain-infinite-kazhdan
requires:
  - pgl3-nonarchimedean-lattices-have-property-t
  - robertson-steger-boundary-cylinders-and-pure-infiniteness
---

Notation as in the target claim. Items (rel1), `f2`, `5`, `4`, φ, `c1`, `c2`, main2
and "Remark" refer to `robertson-steger-boundary-cylinders-and-pure-infiniteness`. All
hypotheses there hold: `Γ` is a lattice in `PGL_3(K)`, `K` nonarchimedean of characteristic
zero, acting type rotatingly and freely on vertices with finitely many orbits.

**Standard crossed product facts used.** These are textbook facts, not imported.
- In `C(Ω)⋊_rΓ` there is a faithful conditional expectation `E` onto `C(Ω)` with
  `E(f u_γ) = δ_{γ,1} f`.
- `C(Ω)` embeds, and `u_γ f u_γ^* = f∘γ^{-1}`.
- By the Remark, the full and reduced crossed products coincide, so these facts hold in
  `C(Ω)⋊Γ`.

In the Robertson–Steger formulas, `γ` stands for `u_γ`. A clopen `U` gives the projection
`1_U`, and `u_γ 1_U u_γ^* = 1_{γU}`. Two clopen sets are equal iff their indicators are
equal in `C(Ω)`.

## Step 1. Γ is infinite and Kazhdan

- (T) is `pgl3-nonarchimedean-lattices-have-property-t`.
- `B` has infinitely many vertices, since each apartment is a Euclidean plane
  tessellated by triangles. `Γ` acts freely with finitely many vertex orbits, so a finite
  `Γ` would give finitely many vertices. Hence `Γ` is infinite.

## Step 2. Each γ is a finite union of prefix replacements

Fix `γ ∈ Γ` and choose `m` with `d(O, γ^{-1}O) ≤ m_1, m_2`, as in main2.

**(2a) Partition.**
- By `c1`, `1 = Σ_{p∈𝔚̄_m} 1_{Ω(p)}`.
- A finite sum of projections equal to the projection `1` has pairwise orthogonal
  terms. So the sets `Ω(p)`, `p ∈ 𝔚̄_m`, are pairwise disjoint and cover `Ω`.

**(2b) The pieces.**
- Fix `p ∈ 𝔚̄_m`. By the claim in main2 there is `p' ∈ 𝔚̄` with `γt(p) = t(p')` and
  `u_γ1_{Ω(p)} = φ(s_{v̄,ū})`, where `ū = ᾱ(p)` and `v̄ = ᾱ(p')`. Since
  `s_{v̄,ū}` is a generator, `t(ū) = t(v̄)`.
- `φ` is a *-homomorphism, so by (rel1a,b) and main2:
  `1_{γΩ(p)} = (u_γ1_{Ω(p)})(u_γ1_{Ω(p)})^* = φ(s_{v̄,ū}s_{ū,v̄}) = φ(s_{v̄,v̄}) = 1_{Ω(p')}`.
- Hence `γ` restricts to a homeomorphism `Ω(p) -> Ω(p')`.

**(2c) Algebraic identity.** Let `w ∈ W` with `o(w) = t(ū)`. Then
`s_{v̄,ū} s_{ūw,ūw} s_{ū,v̄} = s_{v̄w,v̄w}`.

- By `f2`, `s_{v̄,ū} = Σ_{w'} s_{v̄w',ūw'}`, summed over `w' ∈ W` with
  `σ(w') = σ(w)` and `o(w') = t(ū)`.
- By Corollary `4` the products `ūw'` are distinct for distinct `w'`, since
  `ūw'|_{[m,m+n]} = w'`.
- By (rel1b), `s_{v̄w',ūw'} s_{ūw,ūw} = s_{v̄w',ūw'} s_{ūw',ūw'} s_{ūw,ūw}`. By
  Lemma `5` this vanishes for `w' ≠ w`. For `w' = w` it is `s_{v̄w,ūw}`.
- Hence `s_{v̄,ū}s_{ūw,ūw} = s_{v̄w,ūw}`.
- In the same way, `s_{ū,v̄} = Σ_{w'} s_{ūw',v̄w'}`, and
  `s_{v̄w,ūw} s_{ūw',v̄w'} = s_{v̄w,ūw} s_{ūw,ūw} s_{ūw',ūw'} s_{ūw',v̄w'}`. This is `0`
  for `w' ≠ w` and `s_{v̄w,v̄w}` for `w' = w`.

**(2d) Nesting.**
- By `f2` with `u = v = ū`, `s_{ū,ū} = Σ_{w'} s_{ūw',ūw'}`. So
  `1_{Ω[ūw]} = φ(s_{ūw,ūw}) ≤ φ(s_{ū,ū}) = 1_{Ω(p)}`, and `Ω[ūw] ⊆ Ω(p)`.
- Apply φ to (2c):
  `1_{γΩ[ūw]} = u_γ 1_{Ω(p)} 1_{Ω[ūw]} 1_{Ω(p)} u_γ^* = φ(s_{v̄,ū}) φ(s_{ūw,ūw}) φ(s_{ū,v̄}) = 1_{Ω[v̄w]}`.
- So `γΩ[ūw] = Ω[v̄w]` for every `w` with `o(w) = t(ū)`. That is, `γ|_{Ω(p)}` is a
  prefix replacement `ū ⇒ v̄`.

Together with (2a), this proves item 2.

## Step 3. Faithfulness

- Let `N` be the kernel of `Γ -> Homeo(Ω)`, and suppose `γ ∈ N` with `γ ≠ 1`.
- Since `N` acts trivially, `(C(Ω), Γ -> Γ/N)` is a covariant pair. It gives a
  surjection `π: C(Ω)⋊Γ -> C(Ω)⋊(Γ/N)`.
- `π ≠ 0`, because `C(Ω) ≠ 0` embeds in the target.
- `π(u_γ - 1) = 0`, but `u_γ - 1 ≠ 0`, since `E(u_γ - 1) = -1`.
- So `ker π` is a proper nonzero closed ideal, which contradicts simplicity (Remark).

Hence `N = 1`, which is item 3.

## Step 4. No invariant probability measure

Suppose `μ` is a `Γ`-invariant Borel probability measure on `Ω`, and put `τ = μ∘E`.

**τ is a tracial state.** It is a state. On the dense span of `f u_γ`, with
`δ = γ^{-1}`:
- `τ(f u_γ g u_δ) = ∫ f·(g∘γ^{-1}) dμ`;
- `τ(g u_δ f u_γ) = ∫ g·(f∘γ) dμ`;
- these agree by invariance of `μ`.

Products with `γδ ≠ 1` have trace `0` in either order. By continuity, `τ` is tracial.

**τ is faithful.**
- Put `J = {a : τ(a^*a) = 0}`. It is a closed left ideal by Cauchy–Schwarz.
- It is also a right ideal: `τ((ab)^*(ab)) = τ(a b b^* a^*) ≤ ‖b‖² τ(aa^*) = ‖b‖² τ(a^*a)`.
- `1 ∉ J`, so by simplicity `J = 0`.

**Contradiction.**
- `C(Ω)⋊Γ` is unital, simple and purely infinite (Remark). So `1` is an infinite
  projection: there is `v` with `v^*v = 1` and `vv^* ≠ 1`.
- Then `τ(1 - vv^*) = 1 - τ(v^*v) = 0`, while `1 - vv^* ≥ 0` is nonzero. This
  contradicts faithfulness.

**Consequences.**
- A measure on a closed invariant subset extends by zero to an invariant measure on
  `Ω`, so no such subset carries one.
- A finite orbit would carry the normalized counting measure, so every orbit is
  infinite.

This proves item 4 and the claim.
