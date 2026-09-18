---
rg: 2
id: fpbs-planar-stretch-bounded-below-by-dual-piece-mass-proof
kind: route
title: Close a shortest open path with the axis segment, bound the winding area by the dual Cheeger constant, cover closed axis edges by dual pieces, and pass to p_u by Birkhoff and Fatou
target: fpbs-planar-stretch-bounded-below-by-dual-piece-mass
requires:
  - fpbs-regular-tiling-edge-isoperimetric-constant
  - fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu
---

Complete written proof. Notation as in the target. No computation is used.

**Standard facts used.**

- The Jordan curve theorem, and the fact that the winding number of a closed
  polygonal curve is zero on the unbounded component of its complement.
- Birkhoff's ergodic theorem for nonnegative functions: limits lie in
  `[0, infinity]`, obtained by truncation and monotone convergence.
- A Bernoulli product measure is ergodic under a translation of `Z` acting on
  the index set with infinite orbits.
- Fatou's lemma.

## 0. Geometry

- **The embedding.** `Gamma_g` acts on the hyperbolic plane by
  orientation-preserving isometries that preserve the `{4g,4g}` tiling `G`.
  Left multiplication is a graph automorphism mapping faces to faces. Every face
  is a bounded `4g`-gon, and `G†` is a `{4g,4g}` tiling.
- **The dual constant.** By `fpbs-regular-tiling-edge-isoperimetric-constant`
  with `d_(G†) = 4g` and face degree `4g`, every finite nonempty set `A` of faces
  satisfies `|∂_E A| >= h|A|`, with `h = sqrt((4g-2)^2 - 4) > 0`. Here
  `∂_E A` counts primal edges with one adjacent face in `A` and one outside.
- **The line.** `a` has infinite order, so the `a^k` are distinct and `L` is a
  simple bi-infinite path. Every compact set meets finitely many edges, so `L`
  is a properly embedded line. By the Jordan curve theorem on the sphere, the
  complement of `L` has exactly two components, `H_+` and `H_-`.
- **Sides are preserved.** Left multiplication by `a` preserves orientation
  and maps `L` to itself by the shift `k -> k+1`. So it maps `H_+` to `H_+`.
- **Faces and pieces.** Each face is an open disc disjoint from `L`, so it lies
  in one side. A primal edge `e` not on `L` has interior disjoint from `L`, and
  its two adjacent faces meet a small neighbourhood of an interior point of `e`.
  So both lie on the same side. Hence every piece `P_+(e)` lies in `H_+` and
  every `P_-(e)` lies in `H_-`. Two `+`-pieces are equal or disjoint, and a
  `+`-piece is disjoint from a `-`-piece.
- **Finiteness.** For `t >= p_u`, a piece is contained in a cluster of the dual
  process, which is bounded by `fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu`.
  So pieces are finite almost surely. Each piece is adjacent to finitely many
  edges of `L`, so `1 <= m_±(e) < infinity`.

## 1. Winding area bound

**Lemma 1.** Let `Gamma` be a finite closed edge path in `G` of length `N`.
Let `w(f)` be its winding number around an interior point of the face `f`.
Then `w` is finitely supported and

```text
h * sum_f |w(f)|  <=  sum_e |w(f_1(e)) - w(f_2(e))|  <=  N,
```

where `f_1(e)` and `f_2(e)` are the two faces adjacent to `e`.

*Proof.*

- **The jump across an edge.** It equals the signed number of traversals of
  `e` by `Gamma`, so its absolute value is at most the number of traversals.
  Summing over `e` gives the right inequality.
- **Finite support.** All but finitely many faces lie in the unbounded
  component of the complement of `Gamma`, where `w = 0`.
- **Layer cake.** An edge with adjacent values `u < v` lies in
  `∂_E {w > k}` for exactly the `v - u` integers `k in [u, v)`. So
  `sum_e |dw(e)| = sum_(k in Z) |∂_E {w > k}|`.
- **Nonnegative levels.** For `k >= 0`, `{w > k}` is finite, so
  `|∂_E {w > k}| >= h |{w > k}|`. Also `sum_(k >= 0) |{w > k}| = sum_f w^+(f)`.
- **Negative levels.** For `k < 0`, `∂_E {w > k} = ∂_E {w <= k}`, and
  `{w <= k}` is finite, with `sum_(k < 0) |{w <= k}| = sum_f w^-(f)`.

Adding the two ranges gives the left inequality. `□`

## 2. Deterministic area bound (item 1)

Fix `omega` and `n`. Assume `d_omega(o, a^n) < infinity`, since otherwise there
is nothing to prove. Let `gamma` be an open path from `o` to `a^n` of length
`d_omega(o, a^n)`. Let `g` be the segment `e_0, ..., e_(n-1)` of `L`. Apply
Lemma 1 to `Gamma = gamma` followed by `g` reversed, so `N = |gamma| + n`.

**Jumps.** Let `E_n` be the set of closed edges among `e_0, ..., e_(n-1)`.

- If `e in E_n`, then `gamma` does not traverse `e`, because `e` is closed, and
  `g` traverses it once. So `w(f_+(e)) - w(f_-(e)) = ±1`, and `w` is nonzero at
  `f_+(e)` or at `f_-(e)`.
- If `e` is closed and not on `L`, neither path traverses `e`, so `w` has equal
  values on the two faces of `e`.

So `w` is constant on every piece. Hence for each `e in E_n`, `w != 0` on all
of `P_+(e)` or on all of `P_-(e)`. So the set `C` of pieces on which `w != 0`
is a **cover**: it contains `P_+(e)` or `P_-(e)` for every `e in E_n`.

**Packing.** Put `y_e = y(e)` for `e in E_n`. For a `+`-piece `P`, at most
`m_+(e)` edges `e in E_n` have `P_+(e) = P`, all with the same `m_+(e) = m_P`,
and each has `y_e <= |P|/m_P`. So `sum_(e in E_n : P_+(e) = P) y_e <= |P|`, and
the same holds for `-`-pieces. The pieces in `C` are pairwise disjoint (§0), so

```text
sum_f 1[w(f) != 0]  >=  sum_(P in C) |P|
                    >=  sum_(P in C) sum_(e in E_n : P in {P_+(e), P_-(e)}) y_e
                    >=  sum_(e in E_n) y_e.
```

The last step holds because every `e in E_n` has at least one of its pieces in
`C`. Since `|w| >= 1[w != 0]`, Lemma 1 gives
`h * sum_(k<n) y(e_k) <= |gamma| + n`, which is item 1. `□`

The argument uses only that the pieces of edges in `E_n` are finite. That is
the hypothesis of item 1, and it holds almost surely for `t >= p_u` (§0).

## 3. Stretch bound at a fixed parameter (item 2)

Fix `t in [p_u, 1)` and put `mu = mu(t)`.

**Ergodic limit.** Let `theta` be the edge automorphism induced by left
multiplication by `a`.

- By §0, `theta` maps `L` to `L` with `theta(e_k) = e_(k+1)`, preserves sides
  and faces, and maps pieces to pieces.
- So `y(e_k)(omega) = y(e_0)(omega o theta^k)`.
- `theta` has infinite orbits on edges, so the Bernoulli measure is ergodic
  under `theta`.
- Birkhoff for the nonnegative measurable `y(e_0)` gives, almost surely,
  `(1/n) sum_(k<n) y(e_k) -> mu` in `[0, infinity]`.

**Conclusion.** Let `K` be a linear stretch constant at `t`, so some `c > 0`
has `P_t(d_omega(o, a^n) <= K(d(o, a^n) + 1)) >= c` for all `n`.

- Since `a in S`, `d(o, a^n) <= n`. So `P_t(d_omega(o, a^n) <= K(n+1)) >= c`.
- Suppose `h mu - 1 > K`, and choose `K'` with `K < K' < h mu - 1`.
- By item 1 and the ergodic limit, almost surely `d_omega(o, a^n) >= K' n` for
  all large `n`, which exceeds `K(n+1)` for large `n`.
- So `P_t(d_omega(o, a^n) <= K(n+1)) -> 0`, a contradiction.

Hence `K >= h mu - 1`, so `K_*(t) >= h mu(t) - 1`. If `mu = infinity`, no `K`
survives. `□`

## 4. Passage to `p_u` (item 3)

- **Monotone coupling.** Take `U_e` iid uniform on `[0,1]`, and let `e` be
  closed at `t` iff `U_e > t`. As `t ↓ p_u`, the closed sets increase to
  `{U_e > p_u}`. Write `y_t` for the weight at parameter `t`, and `y_(p_u)` for
  the weight computed from `{U_e > p_u}`.
- **The weight stabilises.** Almost surely all pieces at `p_u` are finite (§0).
  Fix such an `omega`.
  - If `U_(e_0) <= p_u`, then `e_0` is open at every `t >= p_u`, and
    `y_t = 0 = y_(p_u)`.
  - Otherwise let `P = P^(p_u)_+(e_0)` and `Q = P^(p_u)_-(e_0)`. Each is
    finite, spanned by a finite tree of dual edges with `U > p_u`, and adjacent
    to finitely many edges of `L`. Let `t_0 > p_u` be the minimum of `U` over
    `e_0`, the spanning edges of `P` and `Q`, and the `L`-edges adjacent to `P`
    or `Q` that are closed at `p_u`.
  - For `t in (p_u, t_0)`, `P^t_+(e_0) ⊆ P` (fewer closed edges) and
    `P ⊆ P^t_+(e_0)` (the spanning edges are still closed). So they are equal.
  - An edge `e'` of `L` closed at `t` with `P^t_+(e') = P` is closed at `p_u`,
    and its `p_u`-piece contains `P` and is a component, so it equals `P`.
    Conversely, an `e'` closed at `p_u` with `p_u`-piece `P` is closed at `t`,
    and `f_+(e') in P = P^t_+(e_0)`, so `P^t_+(e') = P`.
  - So `m^t_+(e_0) = m^(p_u)_+(e_0)`, and the `-` side is the same.
  - Hence `y_t(e_0) = y_(p_u)(e_0)` for all `t` close to `p_u`.
- **Conclusion.** `y_t(e_0) -> y_(p_u)(e_0)` almost surely, and Fatou gives
  `liminf_(t↓p_u) mu(t) >= mu(p_u)`.
- **Monotonicity.** `K_*` is nonincreasing. In the monotone coupling
  `d_(omega_s) >= d_(omega_t)` for `s <= t`, so a stretch constant at `s` is
  one at `t`. So by item 2
  `sup_(t>p_u) K_*(t) = lim_(t↓p_u) K_*(t) >= liminf_(t↓p_u) (h mu(t) - 1) >= h mu(p_u) - 1`. `□`
