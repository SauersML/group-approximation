---
rg: 2
id: hyperbolic-groups-have-sft-horofunction-compactifications
kind: claim
title: The horofunction lemma holds on every hyperbolic Cayley graph, so the distance-gradient SFT is exactly the horofunction compactification and every hyperbolic group has an SFT compactification, although descents need not merge (Webster–Winchester non-Busemann points)
distinct_from:
  k-local-distance-functions-on-hyperbolic-groups-are-global: that proves the unique seed and the structure of seedless points and reduces (HL) to a tube lemma; this proves (HL) outright by propagating one local target upstream, with no merging.
  finite-type-branch-blow-ups-are-sft-compactifications: its part 4(c) poses (HL) and its part 4(b) gives the Busemann criterion f = b_γ; this proves (HL) and shows that criterion is not necessary.
---

**ESTABLISHED** (lane proof, bh-g2-buildings, 2026-09-18; elementary; not reviewed; no priority
claimed). The proof closes part 4(c) of `finite-type-branch-blow-ups-are-sft-compactifications` and the
tube question of `k-local-distance-functions-on-hyperbolic-groups-are-global`.

## Statement

Let `Γ` be hyperbolic with finite symmetric generating set `S`.
- Fix `δ ≥ 1` such that the Cayley graph satisfies all of the following:
  - it is `δ`-thin and `δ`-slim;
  - Gromov's four-point condition holds with constant `δ`;
  - `d(w,[x,y]) ≤ (x|y)_w + 4δ` for every geodesic `[x,y]`;
  - geodesic rays with the same endpoint are eventually within `8δ` of each other (Bridson–Haefliger
    III.H.3.3; recalled, not re-read).
- Let `k ≥ 13δ + 4`.
- Let `Y_k` be the distance-gradient SFT: gradients of `f : Γ -> Z` whose restriction to every `B_k(g)`
  equals `d(·,q)` up to a constant, for some `q ∈ Γ`.
- Let `K_h` be the closure of `{∇d(·,g)}`.

Then `Y_k = K_h`. With the unique seed (part 3 of
`k-local-distance-functions-on-hyperbolic-groups-are-global`), `(Y_k, "sink at 1")` is therefore an SFT
compactification of `Γ` in the sense of the tree-gluing node: (C1) and (C2) both hold.

## Proof

`K_h ⊆ Y_k` because limits of genuine patterns are genuine. Conversely, let `f ∈ Y_k`. If `f` has a sink it is
a translate of `d(·,1)`. So let `f` be seedless, and fix a finite `F ∋ 1`.
- **Rays.** By part 2 of the parent, every `x ∈ F` has a descending geodesic ray `α_x`, and all of these
  rays converge to the same `ξ`. Put `γ = α_1`.
- **One window.** For `t` large and every `x ∈ F`, there is a point `w_x ∈ α_x` with
  `d(w_x, γ(t)) ≤ 8δ` and `f(x) − f(w_x) ≥ δ + 1`. This uses the asymptotic-rays fact and
  `f(γ(t)) -> −∞`.
- **The target.** Let `W = B_k(γ(t))`, and let `q` fit `f` on `W`: `c_q := f − d(·,q)` is constant, equal
  to `c`, on `W`.

**Monotonicity.**
- Along an `f`-descent step, `f` drops by 1 and `d(·,q)` drops by at most 1, so `c_q` does not increase.
- Along a geodesic step toward `q`, `d(·,q)` drops by 1 and `f` drops by at most 1, so `c_q` does not
  decrease.

**Lower bound.** `α_x` descends from `x` to `w_x ∈ W`, so `c_q(x) ≥ c_q(w_x) = c`.

**Upper bound.**
- **The point `v`.** Let `v ∈ α_x` be the point with `d(v, w_x) = δ + 1` between `x` and `w_x`. The
  segment `[v, w_x]` lies in `B_(9δ+1)(γ(t)) ⊆ W`, and on `W` we have `f = d(·,q) + c`. The segment
  drops `f` by `δ + 1`, so `d(v,q) = d(v,w_x) + d(w_x,q)`, i.e. `(v|q)_(w_x) = 0`.
- **The four-point condition.** `v` lies on the geodesic `α_x` from `w_x` back to `x`, so
  `(x|v)_(w_x) = δ + 1`. At base `w_x`, `(v|q) ≥ min((v|x), (x|q)) − δ`. This forces
  `(x|q)_(w_x) ≤ δ`.
- **The geodesic meets `W`.** Every geodesic `σ` from `x` to `q` passes within `5δ` of `w_x`, hence
  within `13δ ≤ k` of `γ(t)`. So `σ` meets `W` at some `σ_j`. Along `σ`, `c_q` does not decrease, so
  `c_q(x) ≤ c_q(σ_j) = c`.

**Conclusion.** Hence `c_q = c` on all of `F`, i.e. `f − f(1) = d(·,q) − d(1,q)` on `F`. `F` was arbitrary,
so `f ∈ K_h`. `∎`

## Remarks

- **No merging is needed, and none holds in general.** The fitting target `q` need not lie on any
  descending ray. Webster–Winchester (Trans. AMS 2006, arXiv:math/0309291; read at source) give
  counterexamples to merging:
  - Ex. 2.2: a 2-slim graph;
  - Ex. 3.1: the free group `⟨a,b,c,d | aba^(−1)dcd^(−1)⟩ ≅ F_3` with a redundant generator.

  Both have horofunctions that are not Busemann points. Their Thm. 2.2 and 2.3 identify "every boundary
  point is Busemann" with eventual tail-sharing of minimal paths, i.e. merging. So:
  - the criterion `f = b_γ` of part 4(b) of the bh-invent-13 node is sufficient but not necessary;
  - merging (the parent's sufficient condition) fails for some hyperbolic Cayley graphs;
  - (HL) holds for all of them.
- **Free and surface groups.** Both are covered for every finite generating set. Nothing specific to
  them is used.
- **Consequences.**
  - Every hyperbolic group has an SFT compactification: an isolated dense seed orbit with trivial
    stabilizer. This includes the Kazhdan ones (uniform lattices in `Sp(n,1)`, Żuk groups).
  - So bh-invent-13's (IE′) finite-type premise holds for them.
  - By Steps A–C of the tree-gluing node, `Γ * Z` carries a minimal, topologically free SFT for every
    hyperbolic `Γ`.
  - What is **not** proved: quantum rigidity of `Y_k`, the remaining condition for membership in the
    class `𝒞` of the tree-gluing node.

## Lesson for general BH

**Local targets propagate upstream.**
- For any locally genuine function, the defect `f − d(·,q)` to a local target `q` is monotone in two
  directions: it does not increase along descents and does not decrease along geodesics toward `q`.
- In hyperbolic geometry, every geodesic from an upstream point to `q` passes through the window
  where `q` fits. So the defect is squeezed to a constant on everything upstream.
- The finite-type question for horofunction compactifications is therefore settled by hyperbolicity
  alone, without Busemann points.
- The same squeeze works on any graph where geodesics from upstream to a local target are forced
  through its window, which is a "funnel" property. That is the property to look for in an fp overgroup
  of the canonical Kazhdan inputs. After it, rigidity is the only remaining condition for (★𝒞).

## Referee (bh-ref-hl, 2026-09-18): PASS

This is an adversarial line-by-line check of the proof, which is an internal lane review and not an external one.
- **Monotonicity.** `f` is 1-Lipschitz by part (0) of the parent. A descent step changes `c_q` by `−1 − Δd ≤ 0`, and a step toward
  `q` changes it by `Δf + 1 ≥ 0`. Correct.
- **Lower bound.** `α_x` is a descending path, hence a geodesic, and `w_x ∈ W` because `8δ ≤ k`. Correct.
- **Upper bound, the key step.**
  - `[v,w_x] ⊆ B_(9δ+1)(γ(t)) ⊆ W`. On `W`, `f` drops by `δ+1`, so `d(v,q) = d(v,w_x) + d(w_x,q)` and `(v|q)_(w_x) = 0`.
  - `v` lies on the geodesic `α_x` from `w_x` to `x`, so `(x|v)_(w_x) = δ+1`.
  - The four-point condition gives `0 ≥ min(δ+1, (x|q)) − δ`. So `(x|q)_(w_x) < δ + 1`, and with integer `δ` this means `≤ δ`.
  - The stipulated `d(w,[x,y]) ≤ (x|y)_w + 4δ` then puts every geodesic `x→q` within `5δ` of `w_x`, hence within
    `13δ < k` of `γ(t)`. So "every geodesic from an upstream point to `q` passes through the window" holds as written.
  - Along that geodesic `c_q` does not decrease. Correct.
- **Conclusion.** Every finite `F` is fitted by some `q_F`, so `f` is a pointwise limit of normalized `d(·,q_F)`. Correct.
- **The part (2) input** (all descending rays converge to one `ξ`) and **the part (3) input** (unique seed) are both checked in the
  parent's Referee section.
- **Webster–Winchester test.** I read the source at arXiv math/0309291 (tex) myself.
  - The 2-slim graph `N × {−1,0,1}` (their `eg:nonbusemannpoints`, which they call hyperbolic) has the non-Busemann point
    `γ_0`, with `h(k,±1) = −k`, `h(k,0) = −k+1`.
  - Descending rays run along rows `±1` and never merge. For `x = (1,−1)` and `q = (n,0)` fitting a far window at `(t,1)`,
    the unique geodesic `x→q` runs along row `−1` through `(t,−1) ∈ W`. So the squeeze works exactly as the proof says.
  - Their Cayley example `⟨a,b,c,d | aba^(−1)dcd^(−1)⟩` (`eg:nonbusemangroup`) is free of rank 3, since `b` occurs once. It is
    therefore hyperbolic and covered.
  - There is no tension: the proof never uses merging.
  - The node's "Ex. 2.2 / Ex. 3.1" numbering was not checked against the compiled PDF; the source uses labels.
- **Minor remarks** (no gap in substance):
  1. **Integrability.** `Y_k` as a gradient SFT needs every relator loop of some finite presentation to lie in a `k`-ball, so that
     locally genuine gradients integrate. That holds once `δ` is also chosen with relators of length `≤ 2k`, e.g. loops of
     length `≤ 16δ` generate (Bridson–Haefliger III.H.2.6, recalled). Please state it.
  2. **Recalled constants.** The asymptotic-rays constant (`8δ`, BH III.H.3.3) and `d(w,[x,y]) ≤ (x|y)_w + 4δ` are recalled. This
     is harmless, since `δ` is chosen large enough for all stipulations at once and the slack of 4 in `k` covers vertex
     rounding.

Credit: the horofunction framework is Coornaert–Papadopoulos (Glasgow Math. J. 43, 2001). The non-Busemann
examples are Webster–Winchester (Trans. AMS 2006, arXiv math/0309291).
