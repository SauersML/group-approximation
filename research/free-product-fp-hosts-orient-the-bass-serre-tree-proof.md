---
rg: 2
id: free-product-fp-hosts-orient-the-bass-serre-tree-proof
kind: route
title: A cut edge separates the Cayley graph, gluing across it splits difference sets, and monotonicity of the undetermined side orients the Bass–Serre tree
target: free-product-fp-hosts-orient-the-bass-serre-tree
requires: [fp-crossed-products-force-sft-over-any-group]
---

Notation as in the target. `Δ(x, y) = {p : x(p) ≠ y(p)}`. Part 1 of
`fp-crossed-products-force-connected-differences` gives: every `Δ(x, y)` with `x, y ∈ X` is
`2n`-connected. That is, it cannot be split into two nonempty parts at distance `> 2n`.

## 0. Cut edges

**(M) Every path in the Cayley graph from `side_1(h)` to `side_2(h)` passes through `h`.** So for
`a ∈ side_1(h)` and `b ∈ side_2(h)`, `d(a, b) = d(a, h) + d(h, b)`.

*Proof.* Let `g ∈ side_1(h)` and `s ∈ S`, and write `w = h^(-1) g`, a normal form whose first syllable
lies in `Q_1`.
- `s ∈ S_2`, `w` ends in a `Q_1` syllable: `ws` has a new last syllable. The first is unchanged.
- `s ∈ S_2`, `w` ends in a `Q_2` syllable: `w` has at least two syllables. `ws` changes or deletes
  the last one, and the first is unchanged.
- `s ∈ S_1`, `w` has at least two syllables: the first syllable is unchanged.
- `s ∈ S_1`, `w ∈ Q_1`: `ws ∈ Q_1`, so `gs = h` or `gs ∈ side_1(h)`.

So a neighbour of a point of `side_1(h)` lies in `side_1(h) ∪ {h}`. The same holds for `side_2`. ∎

**(U) For `i ∈ {1, 2}` and `g ∈ P`: `P = gQ_i ⊔ ∪_(q ∈ gQ_i) side_(3-i)(q)`, a disjoint union.**
- If `b ∉ gQ_i`, write `g^(-1) b = q w`, with `q ∈ Q_i` and `w` a nonempty normal form beginning in
  `Q_(3-i)`. Then `b ∈ side_(3-i)(gq)`.
- Uniqueness: for `q ≠ q'` in `gQ_i`, `side_(3-i)(q') ⊆ side_i(q)`.
- Write `π(b) = gq` and `π(q) = q` on `gQ_i`. By (M), `d(π(a), π(b)) <= d(a, b)`.

**(N) Nesting.** Let `h' ∈ side_(3-i)(h)`, and let `j` be the index with `h ∈ side_j(h')`. Then
`side_(3-j)(h') ⊆ side_(3-i)(h)`.

*Proof.* Let `b ∈ side_(3-j)(h')`. Then `b ≠ h`, since `h ∈ side_j(h')`. Suppose `b ∈ side_i(h)`.
- By (M) at `h'`, since `h ∈ side_j(h')` and `b ∈ side_(3-j)(h')`: `d(h, b) = d(h, h') + d(h', b)`.
- By (M) at `h`, since `h' ∈ side_(3-i)(h)` and `b ∈ side_i(h)`: `d(h', b) = d(h', h) + d(h, b)`.
- Adding gives `d(h, h') = 0`, a contradiction. ∎

## 1. Gluing across a cut edge

**Lemma G.** Let `y, z ∈ X` agree on `B_R(h)`. Define `w = y` on `side_1(h) ∪ B_R(h)` and `w = z` on
`side_2(h)`. Then `w ∈ X`.

*Proof.* The two definitions agree on the overlap. Take a window `g B_r`.
- If `d(g, h) < r`: `g B_r ⊆ B_(2r)(h) ⊆ B_R(h)`, where `w = y`.
- If `d(g, h) >= r` and `g ∈ side_1(h)`: every `b ∈ side_2(h)` has `d(g, b) >= d(g, h) + 1 > r` by
  (M). So `g B_r ⊆ side_1(h) ∪ {h}`, where `w = y`.
- The case `g ∈ side_2(h)` is symmetric, with `z`.

Every window is a window of `y` or of `z`, so `w ∈ X`. ∎

## 2. Part 1 (exit dichotomy)

**Not both sides.** Fix an extension `x` of `p`. Suppose `p` is undetermined on both sides. Then there
are extensions `y`, differing from `x` somewhere on `side_1(h)`, and `z`, differing from `x` somewhere
on `side_2(h)`. In each case, one of the two differing extensions differs from `x`.
- Apply Lemma G to `y` and `z`, which agree on `B_R(h)`.
- Then `Δ(x, w) = (Δ(x, y) ∩ side_1(h)) ∪ (Δ(x, z) ∩ side_2(h))`. Both parts are nonempty and lie
  outside `B_R(h)`.
- By (M), their distance is at least `2(R + 1) > 2n`. This contradicts part 1 of the connectivity
  theorem.

**Not neither.** Otherwise all extensions of `p` agree on `side_1 ∪ side_2 ∪ B_R(h) = P`, so the
cylinder `[p]` is a single point, which is then isolated.
- In a minimal system, the orbit of an isolated point is open and invariant.
- Its complement is closed and invariant, so it is empty.
- So `X` is one discrete compact orbit, hence finite. This contradicts `X` infinite.

The agreement statement is the definition of "undetermined". `σ` commutes with translation, so
`τ_(g x)(g h) = τ_x(h)`, and `τ_x(h)` is locally constant in `x`. ∎

## 3. Part 2 (orientation)

**Monotonicity.** Let `τ_x(h) = i` and `h' ∈ side_(3-i)(h)`, and let `h ∈ side_j(h')`. Suppose
`τ_x(h') = 3-j`.
- Pick `y ∈ X` extending `x|B_R(h')` and differing from `x` somewhere on `side_(3-j)(h')`.
- By Lemma G at `h'`, `w = x` on `side_j(h') ∪ B_R(h')` and `w = y` on `side_(3-j)(h')` lies in `X`.
  Also `∅ ≠ Δ(x, w) ⊆ side_(3-j)(h') \ B_R(h')`.
- For `b` in that set, (M) at `h'` gives `d(h, b) = d(h, h') + d(h', b) > R`. So `w = x` on
  `B_R(h)`, and `w` extends `x|B_R(h)`.
- By part 1, `w = x` on `side_(3-i)(h)`. That set contains `side_(3-j)(h')` by (N), which contains a
  point of `Δ(x, w)`. Contradiction.

So `τ_x(h') = j`: the edge `h'` points to its side containing `h`.

**Out-degree at most one.** Let `v = gQ_i`, and suppose `h ≠ h' ∈ gQ_i` both point away from `v`,
that is `τ_x(h) = τ_x(h') = 3-i`.
- Since `h^(-1) h' ∈ Q_i \ {1}`, `h' ∈ side_i(h) = side_(3-τ_x(h))(h)`.
- By monotonicity, `h'` points toward its side containing `h`, which is `side_i(h')`. So
  `τ_x(h') = i`. Contradiction.

**Sink or ray.** Suppose `v` is a sink, and let `e` be an edge not at `v`.
- By (U), `e ∈ side_(3-i)(q)` for the edge `q ∈ gQ_i` with `π(e) = q`.
- `τ_x(q) = i`, so monotonicity says `e` points toward `q`, that is toward `v`.
- A second sink `v'` would have its edge on the geodesic to `v` pointing away from `v'`. So the sink is
  unique.

Now suppose there is no sink.
- Every vertex has exactly one outgoing edge. From any vertex, following outgoing edges gives a path
  that never backtracks, since the arriving edge points in. So it is a ray `(h_0, h_1, ...)`.
- For another vertex `u'`, let `u_k` be the vertex of the ray nearest `u'`. The edges of the geodesic
  from `u'` to `u_k` lie behind `h_k`, so by monotonicity they all point toward `u_k`.
- So the ray from `u'` joins the first ray at `u_k`, and the end is common.

**The fibres.**
- `X_(gQ_i) = ∩_(q ∈ gQ_i) {x : τ_x(q) = i}` is an intersection of clopen sets, so it is closed.
- Equivariance of `τ` gives `X_(gv) = g X_v`.
- Disjointness is the uniqueness of the sink.
- The stabilizer of the vertex `Q_i` is `Q_i`. ∎

## 4. Part 3 (determinism)

(a) Let `y ∈ X` with `y = x` on `N_R(gQ_i)`.
- Then `τ_y(q) = τ_x(q) = i` for all `q ∈ gQ_i`.
- By part 1, `y|B_R(q) = x|B_R(q)` forces `y = x` on `side_(3-i)(q) ∪ B_R(q)`.
- By (U), these sets together with `gQ_i` cover `P`. So `y = x`.

(b) `τ_x(h_0) = 3-i`, so part 1 gives agreement of all extensions of `x|B_R(h_0)` on
`side_i(h_0) ∪ B_R(h_0)`. That set contains `gQ_i \ {h_0}`, and by (U) also every `side_(3-i)(q)` with
`q ∈ gQ_i \ {h_0}`. ∎

## 5. Part 4 (fibres)

**Empty interior.** Suppose `[p] ⊆ X_v` for a nonempty cylinder. By minimality the translates `g[p]`
cover `X`, so by compactness there is a finite `F ⊆ P` with `X = ∪_(f ∈ F) f[p]`.
- Fix `x ∈ [p]`. For every `g ∈ P` there is `f ∈ F` with `f^(-1) g^(-1) x ∈ [p] ⊆ X_v`, so
  `x ∈ X_(g f v)`.
- By disjointness `g f v = v`. So `P = Stab(v) · F^(-1)`, and `Stab(v)`, a conjugate of `Q_i`, has
  finite index.
- But the cosets `(q_2 q_1)^m Q_1`, for nontrivial `q_i ∈ Q_i` and `m >= 0`, are distinct, since their
  normal forms differ. So `Q_1` has infinite index, and symmetrically `Q_2` does. Contradiction.

Hence each closed set `X_v` is nowhere dense. There are countably many vertices, so by Baire `X_V` is
meagre, `X_∂` is comeagre, and in particular `X_∂ ≠ ∅`.

**Sink fibres.** Let `Q_1` be infinite. Take `x ∈ X_∂`. Its ray passes through a vertex `gQ_1`, with
exit `h_0 ∈ gQ_1`. Choose `g_m ∈ gQ_1` with `d(g_m, h_0) -> ∞`, and put `z_m = g_m^(-1) x`.
- The ray of `z_m` leaves the vertex `Q_1` through `g_m^(-1) h_0`, whose length tends to `∞`.
- So for each fixed `q ∈ Q_1`, eventually `τ_(z_m)(q) = 1`.
- A limit point `z` has `τ_z(q) = 1` for all `q ∈ Q_1`, by local constancy. So `z ∈ X_(Q_1)`.

`X_V` is nonempty and invariant, so it is dense by minimality. ∎

## 6. Part 5 (sheets record the exit)

- For `x`, `τ_x(h) = 2` and `τ_x(h') = 1`. For `y`, `τ_y(h) = 1` and `τ_y(h') = 2`. So
  `x|B_R(h) ≠ y|B_R(h)` and `x|B_R(h') ≠ y|B_R(h')`.
- By part 1 of the connectivity theorem, there is a chain `a_0, ..., a_m` in `Δ(x, y)` with
  `a_0 ∈ B_R(h)`, `a_m ∈ B_R(h')` and `d(a_t, a_(t+1)) <= 2n`.
- Project with `π` (for the coset `Q_1`). This gives a chain with steps `<= 2n` from `π(a_0)` to
  `π(a_m)`.
- `π` is 1-Lipschitz and fixes `h` and `h'`, so `π(a_0) ∈ B_R(h)` and `π(a_m) ∈ B_R(h')`.

Each `q_t = π(a_t)` lies in `K`.
- If `q_t ∈ {h, h'}`, this holds by the first bullet.
- If `a_t ∈ Q_1`, then `a_t = q_t` is itself a point of difference.
- If `a_t ∈ side_2(q_t)` with `q_t ∉ {h, h'}`: `τ_x(q_t) = τ_y(q_t) = 1`, so part 1 says
  `x|B_R(q_t)` and `y|B_R(q_t)` determine `x` and `y` on `side_2(q_t)`. They differ at `a_t`, so the
  patterns differ. ∎

## 7. Part 6 (end-space kill)

**Coding.** Let `A_0` be the finite set of components of `P \ B_1(1)`. For an end `ω` put
`λ_ω(g) = g^(-1) C`, where `C` is the component of `P \ B_1(g)` containing `ω`.
- `λ` is continuous and equivariant.
- **Injective.** Let `ω ≠ ω'`.
  - If some edge `h` has them on different sides, `λ` differs at `h`. Indeed `h ∈ B_1(h)`, so by (M)
    the two sides lie in different components.
  - Otherwise both ends lie on the same side of every edge.
    - By (U), at each vertex `gQ_i` at most one edge `q` has the end in `side_(3-i)(q)`, because those
      sets are disjoint.
    - Starting from a fixed vertex, follow such edges. The path is the same for both ends. It either
      stops at a vertex with no such edge (a common sink) or is an infinite ray with both ends on the
      forward side of every edge.
  - A common ray `(h_t)`: any finite `K` lies in `side_back(h_t) ∪ {h_t} ⊆ side_back(h_(t+1))` for
    large `t`. The connected set `side_forward(h_(t+1)) ∪ {h_(t+1)}` avoids `K` and contains both
    ends, so they are equal.
  - A common sink at a coset `gQ_i` with `Q_i` one-ended: for finite `K`, every component of `P \ K`
    other than the one containing the unique infinite component of `gQ_i \ K` meets `gQ_i` in a
    finite set. An end inside it lies in some `side_(3-i)(q)`, contrary to the sink. So both ends lie
    in that component, and they are equal.
  - A common sink at a coset `gZ` of `Q_2 = Z = <t>`: the line has two ends. For `g'` on the line,
    `P \ B_1(g')` puts the forward ray with its subtrees and the backward ray with its subtrees in
    different components. So `λ` separates the two ends there.
- So `Ends(P)` is conjugate to the subshift `E = λ(Ends(P)) ⊆ A_0^P`, and
  `LC(Ends(P), k) ⋊ P ≅ LC(E, k) ⋊ P`.

**Split difference set.** Suppose the latter is finitely presented, with relator length `n`.
- Let `c >= 2` bound the diameters of finite components of `Q_1 \ B_1(q)` and of `Q_1 \ {q}`. It
  exists by local finiteness and translation invariance, and `d_P` restricts to `d_(Q_1)` on `Q_1`.
- Pick `h, h' ∈ Q_1` with `L = d(h, h') > 2c + 2n`. Let `ω` be an end represented by a ray in
  `side_2(h)`, and `ω'` one in `side_2(h')`. Both exist, since `hQ_2 \ {h}` is infinite.
- Put `Z_h = ∪ ({q} ∪ side_2(q))` over `q ∈ Q_1 ∩ B_c(h)`, and define `Z_(h')` in the same way.

By (U) every `g ∈ P` lies in `Q_1` or in some `side_2(q)`. Outside `Z_h ∪ Z_(h')`:
- **`g ∈ Q_1`, far from `h` and `h'`.** `B_1(g)` meets `Q_1` in `B^(Q_1)_1(g)` and otherwise lies in
  `side_2(g)`. The union of the infinite component `C_∞` of `Q_1 \ B_1(g)` with all `side_2(q)`,
  `q ∈ C_∞`, is connected and avoids `B_1(g)`. It contains `h`, `h'` and rays for `ω` and `ω'`. So
  `λ_ω(g) = λ_(ω')(g)`.
- **`g ∈ side_2(q)`, `q ∈ Q_1` far from `h` and `h'`.** By (M), `B_1(g)` meets
  `Q_1 ∪ ∪_(q' ≠ q) side_2(q')` at most in `{q}`. The same union built from the infinite component of
  `Q_1 \ {q}` avoids `B_1(g)` and contains both ends. So `λ` agrees at `g`.

Hence `Δ(ω, ω') ⊆ Z_h ∪ Z_(h')`.
- At `g = h`, `ω` lies in a component inside `side_2(h)`, and `ω'` in one inside `side_1(h)`, because
  `side_2(h') ⊆ side_1(h)`. So `h ∈ Δ`, and likewise `h' ∈ Δ`.
- For `a ∈ Z_h` and `b ∈ Z_(h')` with feet `q` and `q'`, (M) forces every path to pass through `q` and
  `q'`. So `d(a, b) >= d(q, q') >= L - 2c > 2n`.

So `Δ(ω, ω')` is not `2n`-connected, which contradicts part 1 of
`fp-crossed-products-force-connected-differences`. ∎

**Calibration.** Over `F_2 = Z * Z` the sheets are lines. The two-ended line lets `λ` point toward
the exit along the segment between `h` and `h'`, so the difference set is connected, and
`boundary-crossed-product-is-a-leavitt-path-algebra` stands. The proof uses one-endedness of `Q_1`
exactly where `C_∞` contains both exits.
