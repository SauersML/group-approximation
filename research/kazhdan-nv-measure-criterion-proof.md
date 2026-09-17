---
rg: 2
id: kazhdan-nv-measure-criterion-proof
kind: route
title: The slope cocycle is an integer coboundary for each invariant measure, and deep bricks transported along the potential give almost invariant l2 vectors that (T) pushes onto finite orbits
target: kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures
requires: []
artifacts:
  - research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md
---

Direct establishment; complete proofs are Sections 0 to 4 of the artifact.
`requires: []` is a proof commitment. The only imports are Delorme–Guichardet
((T) gives (FH)) and the defining form of (T) with a Kazhdan pair, both standard
and not re-read at source.

## 1. Brick calculus

- A brick `[v] = [v_1] x ... x [v_n]` has shape `|v| ∈ N^n` and canonical chart
  `φ_[v](x) = (v_1x_1,...,v_nx_n)`. An element `g ∈ nV` is canonical on a brick `B`
  if `g ∘ φ_B = φ_(gB)` with `gB` a brick.
- Each `g` has a depth `D_g`: it is canonical on every brick whose shape has all
  coordinates `>= D_g`.
- The slope `s(g,x) = |w| - |w'|` for a brick `[w] ∋ x` on which `g` is canonical
  onto `[w']` is well defined, locally constant, and satisfies
  `s(gh,x) = s(g,hx) + s(h,x)`. If `g` is canonical on `B ∋ x` of shape `k`, then
  `gB` is the brick of shape `k - s(g,x)` containing `gx`.

## 2. Integer potential (artifact Lemma 1)

Let `ν` be `K`-invariant. `b(g)(x) = s(g, g^{-1}x)` is a 1-cocycle for the Koopman
representation on `L^2(ν; R^n)`. (T) makes it a coboundary: `s(g,y) = F_0(y) - F_0(gy)`
a.e. for all `g`. `F_0 mod Z^n` is a.e. invariant; subtracting its Borel lift to
`[0,1)^n` gives `F: C^n -> Z^n` with `s(g,y) = F(y) - F(gy)` a.e.

## 3. The K-set and U_K (artifact Section 2)

`Ω` is the set of pairs `(E, φ)` with `E` clopen and `φ: C^n -> E` a homeomorphism;
`g·(E,φ) = (gE, g∘φ)`. The stabilizer of `(E,φ)` is the identity on `E`. `Ω_fin` is the
union of finite orbits and `l^2(Ω_inf)` has no invariant vectors.
`U_K = ∪{E : (E,φ) ∈ Ω_fin}` is exactly the set of points with a clopen neighbourhood
fixed pointwise by a finite-index subgroup.

## 4. Invariant measures live on U_K (artifact Proposition 2)

Fix a Kazhdan pair `(Q, ε)` and `D = max_Q D_q`.
- `Ψ_c(x) = (B, φ_B)` with `B` the brick of shape `c·1 + F(x)` containing `x` when that
  shape is `>= D`, else `*`.
- Off the set where the potential identity fails for some `q ∈ Q` or the shape at `x`
  or `qx` is shallow, `q·Ψ_c(x) = Ψ_c(qx)`. That set has measure `-> 0`.
- `m_c = (Ψ_c)_*ν` satisfies `||q_*m_c - m_c||_1 -> 0`, so `ξ_c = (m_c|_Ω)^{1/2}` are
  almost invariant vectors of norm `-> 1`.
- The `l^2(Ω_inf)` component is also almost invariant, hence tends to `0` by the
  Kazhdan pair. So `m_c(Ω_fin) -> 1`, and `ν(U_K) >= m_c(Ω_fin)`.

## 5. The criterion (artifact Theorem 3)

- Finite `K` gives `U_K = C^n` and measures on closed invariant sets by averaging a
  finite orbit.
- If every closed invariant set is measured, `C^n \ U_K` cannot be nonempty, by
  Section 4.
- If `U_K = C^n`, compactness gives finitely many pairs with finite orbits whose
  clopen sets cover; the common stabilizer has finite index and is trivial.
- Closed invariant sets contain minimal ones, so minimal sets suffice.
