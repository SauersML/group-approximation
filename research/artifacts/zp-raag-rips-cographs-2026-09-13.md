# Rips complexes of RAAGs on cographs are contractible at large scale (z4-05-raag-rips, 2026-09-13)

Status: complete argument, UNREVIEWED. It proves that the Salvetti cover of `A_Γ` has the Jensen–Helly property
of dimension `k` (node `jensen-helly-graphs-have-contractible-rips-complexes`) for every P4-free graph `Γ`, where
`k` is the clique number. So `R_t(A_Γ, V(Γ))` is contractible for all `t ≥ k(k+1) − 1`. This contains
`research/artifacts/zp-raag-rips-products-of-trees-2026-09-13.md` (trees are wedges of lines).

## 0. Setting

A **cograph** is a finite graph with no induced path on four vertices. Equivalently it is built from `K_1` by
disjoint unions and joins (Corneil–Lerchs–Stewart Burlingham 1981). For RAAGs,
`A_{Γ_1 ⊔ Γ_2} = A_{Γ_1} * A_{Γ_2}` and `A_{Γ_1 * Γ_2} = A_{Γ_1} × A_{Γ_2}`, and the clique number is the max,
respectively the sum. Let `X_Γ` be the universal cover of the Salvetti complex, with the l^1 metric on each cube
and the induced path metric `d`. Its vertex set is `A_Γ` with the standard word metric.
- `X_{K_1} = R`.
- `X_{Γ_1 * Γ_2} = X_{Γ_1} × X_{Γ_2}`, with `d = d_1 + d_2`.
- `X_{Γ_1 ⊔ Γ_2}` is tree-graded. Its pieces are copies of `X_{Γ_1}` and `X_{Γ_2}`, and two pieces meet in at
  most one vertex (each vertex `g` lies in the piece `g·X_{Γ_1}` and the piece `g·X_{Γ_2}`). Distances
  between different pieces are computed through the sequence of cut vertices.

Call a **J-space** a geodesic metric space `X` with a discrete set `V` of vertices such that:
- (J) for every finitely supported probability measure `μ` on `V` there is `b ∈ X` with
  `d(x,b) ≤ ∫ d(x,y) dμ(y)` for all `x ∈ V`;
- (C) there is a continuous bicombing `σ : X × X × [0,1] → X` with `σ(c,c',0) = c` and `σ(c,c',1) = c'`, and
  `λ ↦ σ(c,c',λ)` of constant speed `d(c,c')`, such that `λ ↦ d(z, σ(c,c',λ))` is convex for all `z, c, c' ∈ X`.

## 1. Base case: `R`

(J): `b` = the mean, since `|x − ∫ y dμ| ≤ ∫ |x − y| dμ`. (C): straight segments.

## 2. Products

Let `X = X_1 × X_2` with `d = d_1 + d_2`.
- (J): let `b = (b_1, b_2)`, with `b_i` from (J) for the marginal `μ_i`. Then
  `d(x,b) = Σ_i d_i(x_i,b_i) ≤ Σ_i ∫ d_i(x_i,y_i) dμ = ∫ d(x,y) dμ`.
- (C): `σ = (σ_1, σ_2)`. Each coordinate moves at constant speed in `λ`, so the product path has constant speed
  `d(c,c')` for `d_1 + d_2`. Also `d(z, σ(λ)) = Σ_i d_i(z_i, σ_i(λ))` is a sum of convex functions.

## 3. Wedges (gluing two J-spaces at one vertex)

Let `X = A ∨_g B`, where `g` is a vertex of both. For `x ∈ A`, `y ∈ B`: `d(x,y) = d(x,g) + d(g,y)`.

**Lemma W (J for wedges).** If `A` and `B` satisfy (J), so does `X`.

*Proof.* Split `μ = μ_A + μ_B` (put any mass at `g` in `μ_A`), with masses `m_A + m_B = 1`. Put
`M_A = ∫_A d(g,y) dμ` and `M_B = ∫_B d(g,y) dμ`. Let `c_A ∈ A` be a (J)-centre in `A` of the probability measure
`ν_A = μ_A + m_B δ_g`, and `c_B ∈ B` one of `ν_B = μ_B + m_A δ_g`. By (J) at the vertex `g`,
`d(c_A, g) ≤ M_A` and `d(c_B, g) ≤ M_B`. For `x ∈ A`,
(A1) `d(x, c_A) ≤ ∫_A d(x,y) dμ + m_B d(x,g)`, and `∫ d(x,y) dμ = ∫_A d(x,y) dμ + m_B d(x,g) + M_B`.
- **Case 1: `d(c_A, g) ≥ M_B`.** Take `b` on an `A`-geodesic from `c_A` to `g` with `d(c_A,b) = M_B`, so
  `d(b,g) = d(c_A,g) − M_B`.
  - For `x ∈ A`: by (A1), `d(x,b) ≤ d(x,c_A) + M_B ≤ ∫ d(x,y) dμ`.
  - For `x ∈ B`: `d(x,b) = d(x,g) + d(c_A,g) − M_B ≤ d(x,g) + M_A − M_B`. On the other hand
    `∫ d(x,y) dμ = ∫_A (d(x,g) + d(g,y)) dμ + ∫_B d(x,y) dμ ≥ m_A d(x,g) + M_A + (m_B d(x,g) − M_B)`,
    using `d(x,y) ≥ d(x,g) − d(g,y)` on `B`. This equals `d(x,g) + M_A − M_B`.
- **Case 2: `d(c_B, g) ≥ M_A`.** Symmetric, with `b ∈ B`.
- **Case 3: `d(c_A,g) < M_B` and `d(c_B,g) < M_A`.** Take `b = g`. For `x ∈ A`, by (A1),
  `d(x,g) ≤ d(x,c_A) + d(c_A,g) < ∫_A d(x,y) dμ + m_B d(x,g) + M_B = ∫ d(x,y) dμ`. For `x ∈ B`, symmetrically. ∎

**Lemma C (C for wedges).** If `A` and `B` satisfy (C), so does `X`: for `c ∈ A`, `c' ∈ B`, let `σ(c,c',·)`
traverse `σ_A(c,g,·)` and then `σ_B(g,c',·)`, parametrized proportionally to length. On `A × A` and `B × B` use
`σ_A` and `σ_B`.

*Proof of convexity.* Paths of constant speed `d(c,c')` have length `d(c,c')`, so they are geodesics, and
the concatenation through `g` is a geodesic of `X`. Let `f(λ) = d(z, σ(c,c',λ))`, and let `λ_g` be the
parameter of `g`. On `[0,λ_g]` and `[λ_g,1]`, `f` is convex: there it is `d(z, σ_A)` or `d(z, σ_B)`, or
`d(z,g)` plus the distance from `g` along a geodesic, which is linear. It remains to check the one-sided
derivatives at `λ_g`. `f` is `d(c,c')`-Lipschitz, so both one-sided slopes lie in `[−d(c,c'), d(c,c')]`.
- If `z ∈ A`: for `λ ≥ λ_g`, `f(λ) = d(z,g) + d(g,σ(λ)) = d(z,g) + d(c,c')(λ − λ_g)`. The right slope is
  `d(c,c')`, which is at least the left slope.
- If `z ∈ B`: for `λ ≤ λ_g`, `f(λ) = d(z,g) + d(c,c')(λ_g − λ)`. The left slope is `−d(c,c')`, which is at most
  the right slope.
So `f` is convex on `[0,1]`. Continuity: `σ` is defined separately on `A × A`, `B × B`, `A × B` and `B × A`,
which are closed sets, and the definitions agree on the overlaps (for example on `A × {g}` both give
`σ_A(c,g,·)`). The pasting lemma applies. ∎

For tree-graded unions of finitely many pieces, apply Lemmas W and C inductively, removing a leaf piece at a time.
A finitely supported `μ` and any finite set of points lie in such a finite union `Y`. For `x ∉ Y` with gate
`p ∈ Y`, both sides of (J) change by the same `d(x,p)`, so (J) on `Y` gives (J) on `X`. The bicombing on `X` goes
through the gates, and convexity reduces in the same way.

**Conclusion.** By induction on the cograph structure, every `X_Γ` with `Γ` P4-free is a J-space.

## 4. Helly number `k+1` and rounding

Let `k` be the clique number (= `dim X_Γ`). Every point of a cube lies within `k/2` of a corner: (R).

**Lemma H'.** Let `𝓑` be a finite family of balls `B(z,ρ) = {c : d(z,c) ≤ ρ}` in `X = X_Γ`. If every `k+1`
members have a common point, then all do.

*Proof.* Take a large closed ball `P = B(v, R)` containing all centres and witnesses (finitely many points).
- By (C), balls are σ-convex: if `c, c'` are in a ball, so is `σ(c,c',λ)`, by convexity of `d(z,σ(·))`.
  Intersections are σ-convex. So `P` and all nonempty `P ∩ ⋂ B` are compact, contractible via
  `(c,λ) ↦ σ(c,c_0,λ)`, locally contractible (intersect with small balls, also σ-convex), and finite-dimensional.
  Hence they are ARs.
- `dim P ≤ k`, and `P` is contractible, so for every compact `A ⊆ P` and `j ≥ k`, `Ȟ^j(A) = 0`
  (as in Lemma H of the products-of-trees artifact: the exact sequence of `(P, A)`, `Ȟ^k(P) = 0`,
  `dim(P/A) ≤ k`).
- A minimal subfamily `K_0..K_m` with empty intersection has `m ≥ k+1`, nerve `∂Δ^m`, and union `≃ S^{m−1}` by
  Borsuk's nerve theorem. That gives a nonzero `Ȟ^{m−1}` with `m − 1 ≥ k`, a contradiction.
- Witnesses outside `P` cannot occur for `R` large, by the choice of `P`. ∎

## 5. Theorem

For every P4-free `Γ` with clique number `k ≥ 1`, `(X_Γ, V = A_Γ)` has the Jensen–Helly property of dimension
`k`: (J) by §§1–3, (H) by Lemma H', (R) by §4. The Cayley graph has degree `2|V(Γ)|`. So
`jensen-helly-graphs-have-contractible-rips-complexes` gives `R_t(A_Γ, V(Γ))` contractible for every integer
`t ≥ k(k+1) − 1`.

Examples newly covered: `Z × (Z^2 * Z)` (triangle with a pendant vertex), `(F_2 × Z^2) * Z^3`, `Z × (F_2 × F_2 * Z)`.

## 6. What remains

Graphs with an induced P4 that contain a triangle, e.g. `K_1 * P4` (`Z × A_{P4}`), where `A_{P4}` is an amalgam
`Z^2 *_Z Z^2 *_Z Z^2`. Lemma W glues along a single vertex. The next step is gluing along convex subcomplexes
(for `P4`, lines), where the gate map is a nearest-point projection onto a line and the case analysis must
balance moments along that line.
