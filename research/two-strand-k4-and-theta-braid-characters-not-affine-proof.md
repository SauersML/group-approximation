---
rg: 2
id: two-strand-k4-and-theta-braid-characters-not-affine-proof
kind: route
title: "When every edge deletion Gamma_e is connected, affine classes factor through H^1(Gamma); the Euler characteristic forces a larger H^1"
target: two-strand-k4-and-theta-braid-characters-not-affine
requires: []
artifacts:
  - research/artifacts/graph-braid-hyperplane-affine-counterexample-2026-09-16.md
---

Full details are in the artifact, §§1–6. Write `X = UD_2Γ`, and let
`Γ_e = Γ − ē` be the induced subgraph off the endpoints of an edge `e`.

1. **Classes.** A hyperplane class consists of X-edges over one edge `e` of
   `Γ`, all oriented along `e`. An antisymmetric function on oriented classes
   is a function on classes, and the cochain it induces is a cocycle.
2. **One class per edge.** Suppose `z, z'` are adjacent in `Γ_e`. Then the
   X-edges `{e,z}` and `{e,z'}` are opposite in the square `{e,[z,z']}`. So
   if `Γ_e` is connected, all X-edges over `e` form a single class, and an
   affine cochain is `c({e,z}) = a(e)` for some `a ∈ C^1(Γ)`.
3. **Chain maps.** Set `σ({x,y}) = x + y` and `τ({e,z}) = e`. Then
   `∂τ = σ∂`, and `τ(∂{e,f}) = e + f − e − f = 0`. So `τ` induces
   `τ_*: H_1(X; ℝ) → H_1(Γ; ℝ)`. For affine `c = a∘τ` and a 1-cycle `z`,
   `c(z) = a|_{Z_1(Γ)}(τ_*[z])`. Hence `[c]` lies in the image of the dual
   of `τ_*`, which has dimension at most `β_1(Γ)`.
4. **`Γ_e` is connected.**
   - *`K_4`, any subdivision, `e` on the path `P_{ab}`.* `c` and `d`
     survive and are joined by `P_{cd}`. Every other surviving vertex reaches
     `c` or `d` along `P_{ac}, P_{ad}, P_{bc}, P_{bd}`, or along a piece of
     `P_{ab}` through `a` or `b`.
   - *`Θ_3`, arcs of length at least 2, `e` on `A_1`.* If `e` misses `p` and
     `q`, then `A_2 ∪ A_3` is intact and each piece of `A_1` reaches `p` or
     `q`. If `e ∋ p`, then `q` survives and `A_2 − p`, `A_3 − p` and
     `A_1 − ē` are paths through `q`. The case `e ∋ q` is symmetric.
5. **Euler characteristic.** For a simple graph,
   `e(UD_2Γ) = C(N,2) − M(N−2) + C(M,2) − Σ_v C(deg v,2)`. This counts
   vertices, edge–vertex pairs off `ē`, and pairs of edges with disjoint
   closures. It equals `−3` for `K_4` with `s` subdivision vertices
   (`N = 4+s`, `M = 6+s`, `Σ = 12+s`). It equals `−2` for `Θ_3` with
   `K = Σ k_i` (`N = K−1`, `M = K`, `Σ = K+3`). Since `dim X ≤ 2`,
   `b_1 = b_0 + b_2 − e ≥ 1 − e`, which is 4, resp. 3.
6. **Conclusion.** `β_1(K_4) = 3 < 4` and `β_1(Θ_3) = 2 < 3`, so the map is
   not surjective. `UD_2Γ` is connected: slide the particle nearest a leaf of
   a spanning tree onto that leaf, then induct. ∎
