---
rg: 2
id: braid-pure-single-edge-hexagons-always-have-a-centre-proof
kind: route
title: Z/2 face-boundary proof that arc unions through a common boundary point have separation Helly number 2, and the resulting centres for pure single-edge braid hexagons
target: braid-pure-single-edge-hexagons-always-have-a-centre
requires: []
---

This is a direct proof. It uses only standard surface topology:
- the change-of-coordinates principle;
- geodesic (minimal-position) representatives;
- mod-2 intersection theory on `S^2`.

Notation is as in the target.

## 1. The dictionary

**(a) Orbits.**
- Every arc `x` from a puncture to `d_0` lies in the `B_n`-orbit of `x_0`. Cutting `D` along `x` gives a disc with
  `n-1` punctures. Any two such cuttings are identified by a homeomorphism fixing `∂D` pointwise and matching the
  two sides of the cut.
- Every spider `y` with `k` legs from `d_1` to `k` distinct punctures lies in the orbit of `y_0`, by the same
  argument. The legs leave `d_1` in a linear order, and the identification respects it.
- Take `x` and `y` with disjoint closures. Cutting along `x ∪ y` gives a disc with `n-k-1` punctures. Hence the
  pair `(x, y)` is `f(x_0, y_0)` for some `f ∈ B_n`.

**(b) Stabilisers.**
- A mapping class fixing `x_0` can be isotoped to fix `x_0` pointwise. It is then a mapping class of the cut disc,
  so `Stab(x_0) = B_{n-1} = ⟨σ_1,…,σ_{n-2}⟩` in the standard placement.
- A mapping class fixing `y_0` fixes each leg, because it fixes `∂D` near `d_1` and so preserves the order of the
  legs there. Hence `Stab(y_0) = ⟨σ_{k+1},…,σ_{n-1}⟩`.
- This is the model already used in `h4-a2-fibred-shadows-are-a4-pure-braid-retractions` (C) and
  `h4-i25-shadow-centre-forms-hold-only-up-to-rotation-proof` §1.

**(c) Adjacency.**
- If `f ∈ gA_X ∩ hA_Y`, then `g x_0 = f x_0` and `h y_0 = f y_0` are disjoint.
- Conversely, if `g x_0` and `h y_0` are disjoint, then by (a) some `f` has `f x_0 = g x_0` and `f y_0 = h y_0`,
  so `f ∈ gA_X ∩ hA_Y`.

A *centre* of `x_1, x_2, x_3` is therefore a spider disjoint from all three arcs.

## 2. Minimal position

Give `D ∖ {punctures}` a complete hyperbolic metric with geodesic boundary, and treat `d_0`, `d_1` as cusps on the
boundary. Equivalently, double along `∂D` and use the punctured sphere.

Realise every arc and every leg by its geodesic. Then:
- distinct geodesics meet transversally, in finitely many points, and never near a cusp;
- the geometric intersection number of two isotopy classes equals the number of interior crossings of their
  geodesics (bigon criterion);
- in particular, `i(x, y) = 0` iff the geodesic arc `x` and the geodesic spider `y` meet only at shared
  endpoints. For an `x`-arc and a spider there are none.

Equal isotopy classes give equal geodesics. So we may assume that `x_1,…,x_m` are pairwise distinct, discarding
repeats (repeats do not change any `R`).

Then `X = ⋃ x_i` is a finite graph in `D`. Its vertices are:
- the crossings;
- the endpoints, including `d_0`, which lies on every `x_i`.

Each edge of `X` is contained in exactly one `x_i`.

Close up by gluing a disc `K` to `∂D`, which gives `S^2 = D ∪ K`. Fix `∞ ∈ int K`. The graph `X` meets `K` only in
`d_0`, so `K ∖ {d_0}` lies in a single component `Ω(X)` of `S^2 ∖ X`, the *`d_1`-region*.

A puncture `p` not on `X` lies in `Ω(X)` iff `X` does not separate `p` from `∞`. Then
`R(X) = {punctures in Ω(X)}`.

`R` is independent of the minimal-position representatives, because `p ∈ R(𝒳)` iff some arc from `p` to `d_1`
has zero geometric intersection with every class in `𝒳`.
- (⇒) Take an arc from `p` to `d_1` inside the connected region `Ω(X)`.
- (⇐) Realise that arc as a geodesic. It is then disjoint from the geodesics of `𝒳`, so `p ∈ Ω(X)`.

## 3. The Z/2 separation lemma

**Lemma.**
- Let `X = x_1 ∪ ⋯ ∪ x_m ⊂ S^2` be a finite graph. Each `x_i` is an embedded arc, and the arcs have a common point
  `t`. Each edge of `X` lies in a single `x_i`.
- Let `p, q ∉ X`.

If no union `x_i ∪ x_j` (`i ≤ j`) separates `p` from `q`, then `X` does not separate `p` from `q`.

*Proof.* Work with `ℤ/2` chains in a triangulation of `S^2` that contains `X` as a subcomplex. Take paths from `p`
to `q` in general position with respect to `X`: they avoid the vertices and cross the edges transversally.

For a 1-cycle `c` supported on `X` and a generic path `γ` from `p` to `q`, let `I(c, γ) ∈ ℤ/2` be the parity of
`|c ∩ γ|`.

*Step 0 (intersection is endpoint-determined).*
- `H_1(S^2; ℤ/2) = 0`, so `c = ∂Σ` for a 2-chain `Σ`.
- `I(c, γ) = I(Σ, ∂γ) = [p ∈ Σ] + [q ∈ Σ]`.
- So `I(c, γ)` does not depend on `γ`. If some generic path from `p` to `q` misses the support of `c`, then
  `I(c, γ) = 0` for every `γ`.

*Step 1 (face boundary).*
- Suppose `X` separates `p` from `q`. Let `F` be the component of `S^2 ∖ X` containing `p`, and let `Σ_F` be the
  2-chain of the triangles in `F`.
- Then `z := ∂Σ_F` is supported on `X`.
- By Step 0, `I(z, γ) = [p ∈ F] + [q ∈ F] = 1`.

*Step 2 (tails).*
- Write `z = z^1 + ⋯ + z^m`, where `z^i` is the part of `z` on the edges of `x_i`.
- For a vertex `v` of `X` on `x_i`, let `π_i(v)` be the 1-chain of the subarc of `x_i` from `v` to `t`, with
  `π_i(t) = 0`. Then `∂π_i(v) = v + t`.
- For any 1-chain `c` on the arc `x_i`, `c = Σ_{v ∈ ∂c} π_i(v)`. Indeed:
  - both sides have boundary `∂c + |∂c|·t = ∂c`, since `|∂c|` is even;
  - an arc carries no nonzero 1-cycle, so a 1-chain on it is determined by its boundary.
- Hence `z = Σ_i Σ_{v ∈ ∂z^i} π_i(v)`.

*Step 3 (pairing).*
- `Σ_i ∂z^i = ∂z = 0`. So for every vertex `v` the set `S_v = {i : v ∈ ∂z^i}` has even size.
- Split each `S_v` into pairs `{i, j}`. Then `z = Σ_v Σ_{{i,j}} (π_i(v) + π_j(v))`.
- Each summand `c_{ij}(v) = π_i(v) + π_j(v)` is a 1-cycle, since its boundary is `2v + 2t = 0`. It is supported on
  `x_i ∪ x_j`.

*Step 4.*
- Since `I(z, γ) = 1`, some `c_{ij}(v)` has `I(c_{ij}(v), γ) = 1`.
- By Step 0, every generic path from `p` to `q` meets `x_i ∪ x_j`. So `x_i ∪ x_j` separates `p` from `q`,
  contradicting the hypothesis. ∎

The lemma uses neither minimal position nor the punctures. Only the common point `t` matters. For `x`-arcs, take
`t = d_0`.

## 4. Proof of the theorem

**Part 1.**
- Realise `x_1,…,x_m` as distinct geodesics (§2).
- `R(X) ⊆ R(x_i ∪ x_j)` is clear, since `Ω(X) ⊆ Ω(x_i ∪ x_j)`.
- Conversely, let `p` lie in every `R(x_i ∪ x_j)`. Then `p` is not an endpoint of any `x_i`, and no pair union
  separates `p` from `∞`. The lemma, with `t = d_0` and `q = ∞`, shows that `X` does not separate them. So
  `p ∈ R(X)`.
- The pair and triple regions here are computed in one geodesic picture. That is legitimate because the geodesics
  of `x_i` and `x_j` are pairwise minimal, and the region `Ω(x_i ∪ x_j)` of two minimal-position arcs is
  well-defined up to isotopy.

**Part 2.**
- (⇐) Let `P ⊆ ⋂ R(x_i ∪ x_j)` with `|P| = k`. By Part 1, `P ⊆ R(X)`, so `P ⊂ Ω = Ω(X)`.
  - `Ω' = Ω ∩ int D` minus the punctures not in `P` is a connected open planar set. A thin collar of
    `∂D ∖ U(d_0)` lies in `Ω`, and `d_1` lies on its outer side.
  - Choose an embedded tree `T ⊂ Ω' ∪ {d_1}` with `T ∩ ∂D = {d_1}` that contains `P`. For example, join the
    points of `P` successively by generic paths in `Ω'` to the tree already built.
  - A regular neighbourhood of `T` is a closed disc `Δ ⊂ Ω' ∪ {d_1}` with `d_1 ∈ ∂Δ` and `P ⊂ int Δ`.
  - Inside `Δ`, take `k` disjoint straight legs from `d_1` to `P`, in a convex model of `Δ`.
  - This spider is disjoint from `X`, so by §1(c) it is a centre.
- (⇒) The legs of a centre `y` are disjoint from `X`. Realise `y` as a geodesic, which stays disjoint from the
  geodesic `X` by §2. A leg joins its puncture to `d_1 ∈ ∂D`, so it lies in `Ω(X)`, and its puncture lies in
  `R(X) = ⋂ R(x_i ∪ x_j)`. The spider has `k` distinct leg punctures.

**Part 3.**
- The geodesic `y_{ij}` is disjoint from the geodesics `x_i` and `x_j` (§2), and its legs run to `d_1`. So
  `P ⊆ R(x_i ∪ x_j)` for every pair.
- Part 2 then gives a centre with legs to `P`.
- If the hexagon's letters are pure braids, every `y_{ij} = h y_0` with `h` pure, so `P = {1,…,k}` for all three.
- If two `x_i` coincide, say `x_1 = x_2`, then `y_{23}` is already a centre.

∎

## 5. Remarks

- **Sharpness.** Part 2 is the exact criterion. Without a common leg set the triple intersection can be too small.
  Compare the unresolved `PA3` Garside candidates decoded by w7-042's `dec76.py`: their pair sets are
  `{q}, {q}, {b}`, which do not meet. This is consistent with the theorem, and it is not an `H_4` statement.
- **What the proof does not give.** It does not say that one of `y_{12}, y_{23}, y_{31}` is a centre (the
  vertex form (Y)), nor that the centre is of a prescribed algebraic form. It builds the centre inside `Ω(X)`.
  - One special case of (Y) is immediate, for `k = 1`. Suppose the three `y_{ij}` (arcs from `d_1` to `p`) are
    pairwise disjoint away from their endpoints. They leave `d_1` in an order `a, b, c`.
    - `a ∪ b` and `b ∪ c` bound discs, and `b` lies in the interior of their union.
    - The outer region `O` meets only `a` and `c`.
    - The `x`-vertex that avoids `a` and `c` must start in `O`, so it misses `b`. The other two `x`-vertices
      miss `b` by construction.
    - So the middle arc `b` is a centre.

## 6. Numerical cross-check

The scripts in `experiments/h4-pure-hexagon-z2-separation-2026-09-17/` are w7-042's arc-placement code,
parametrised by `ARCS_N = n`.
- They realise random pure `x`-arcs (braid words `|w| ≤ 6`) combinatorially.
- A hill-climb matches every pairwise crossing count to curver's `intersection`.
- They then compare the pair regions and the triple region.

| run | triples with a common pair puncture | violations of Part 1 | undetermined (hill-climb failed) |
|---|---|---|---|
| `n = 4` (w7-042, seeds 1, 2) | 937 + 973 | 0 | 70 + 93 |
| `n = 5` (`pl5_s1.log`) | 3663 | 0 | 234 |
| `n = 6` (`pl6_s1.log`) | 4223 | 0 | 272 |

`selftest.py` checks the placement code against curver. At `n = 4, 5, 6` it ran 100 trials each, with 0
mismatches (`selftest_n5.log`, `selftest_n6.log`; for `n = 4`, w7-042's `selftest_big.log`).

To run: `ARCS_N=5 PYTHONPATH=.:<curver-0.5.1>:<realalg-0.3.7> python3 pairlemma.py 30 6 1`.
