# Helly groups have contractible Rips complexes (z4-07-type-f-rips, 2026-09-13)

Status: complete proof written by lane z4-07-type-f-rips; UNREVIEWED; novelty not yet
checked. Serves Zaremsky Problem 4.7 (`zaremsky-4-07-type-f-groups-have-contractible-rips`).

## 1. Statement

**Theorem H.** Let `X` be a connected locally finite Helly graph and let `G` act on `X` by
graph automorphisms with finite vertex stabilizers and finitely many orbits of vertices
(a geometric action; `G` is a *Helly group*). Fix a vertex `x_0`, let
`D = max_v d(v, G x_0)`, and put `ρ(g, h) = d(g x_0, h x_0)` on `G`. For every integer
`s ≥ D + 1`:

1. `T_s = {g ∈ G \ {1} : d(x_0, g x_0) ≤ 2s}` is a finite symmetric generating set of `G`;
2. the flag complex of `Cay(G, T_s)`, which is the Rips complex `VR_1(G, d_{T_s})` and also
   `VR_{2s}(G, ρ)`, is contractible.

So every Helly group has a contractible Rips complex for a suitable finite generating set;
a torsion-free Helly group acts freely, cocompactly and vertex-transitively on a contractible
locally finite flag complex (`group-rips-complexes-are-cayley-graph-flag-complexes`).

**Corollary H'.** If some Cayley graph `X = Cay(G, T)` is Helly, then `(G, T)` is of type R:
`VR_r(G, d_T)` is contractible for every `r ≥ 1`.

Conventions: a graph is *Helly* if every family of pairwise intersecting balls has a common
vertex. Balls are `B(v, r) = {u : d(u, v) ≤ r}` for integers `r ≥ 0`; in a connected graph
`B(u, r) ∩ B(v, r') ≠ ∅` iff `d(u, v) ≤ r + r'`. `Flag(Γ)` is the clique complex of a graph
`Γ`, and `Γ[W]` the induced subgraph on `W`.

## 2. Ball intersections

**Lemma A.** Let `W = B(v_1, r_1) ∩ ... ∩ B(v_p, r_p)` be nonempty (`p ≥ 1`). Then `X[W]` is
isometrically embedded in `X`, and `Flag(X[W])` is contractible.

*Proof.* `W` is finite since `X` is locally finite. Since `W ≠ ∅`, `d(v_i, v_j) ≤ r_i + r_j`
for all `i, j`.

Isometric: let `u, w ∈ W` with `d(u, w) = L ≥ 1`. The balls `B(u, 1)`, `B(w, L − 1)`,
`B(v_i, r_i)` pairwise intersect: `d(u, w) = L = 1 + (L − 1)`; `d(u, v_i) ≤ r_i ≤ 1 + r_i`;
`d(w, v_i) ≤ r_i ≤ (L − 1) + r_i`; `d(v_i, v_j) ≤ r_i + r_j`. A common vertex `u'` lies in `W`,
is within 1 of `u`, and satisfies `d(u', w) = L − 1` by the triangle inequality, so `u'` is a
neighbour of `u` in `W` one step closer to `w`. Induction gives a geodesic of `X` inside `W`.

Contractible: fix `b ∈ W` and put `W_m = W ∩ B(b, m)`, a nonempty ball intersection. For
large `m`, `W_m = W`, and `W_0 = {b}`. We show `Flag(X[W_{m−1}]) ≃ Flag(X[W_m])` for `m ≥ 1`
by deleting the vertices of `W_m` at distance `m` from `b` one at a time. Let `V` be the
current vertex set, `W_{m−1} ⊆ V ⊆ W_m`, and let `u ∈ V` with `d(b, u) = m`. Let `N` be the
set of neighbours of `u` in `X[V]`. The balls `B(b, m − 1)`, `B(u, 1)`, `B(z, 1)` for `z ∈ N`,
and `B(v_i, r_i)` pairwise intersect:

- `d(b, u) = m = (m − 1) + 1`;
- `d(b, z) ≤ m = (m − 1) + 1`, since `V ⊆ B(b, m)`;
- `d(u, z) = 1 ≤ 2` and `d(z, z') ≤ 2`;
- every centre `b, u, z` lies in `W`, so its distance to `v_i` is `≤ r_i`, at most the sum
  of the radii; and `d(v_i, v_j) ≤ r_i + r_j`.

By the Helly property there is a common vertex `u'`. Then `u' ∈ W` and `d(b, u') ≤ m − 1`, so
`u' ∈ W_{m−1} ⊆ V` and `u' ≠ u`; `u'` is adjacent to `u`; and every `z ∈ N` equals or is
adjacent to `u'`. So `u'` dominates `u` in `X[V]`.

In the flag complex `K = Flag(X[V])`, the star of `u` is the cone `u * Flag(X[N])` and meets
`K' = Flag(X[V \ {u}])` exactly in the link `Flag(X[N])`. Since `u' ∈ N` is adjacent to every
other vertex of `N`, the link is a cone with apex `u'`, hence contractible. Gluing the
contractible star to `K'` along a contractible subcomplex does not change the homotopy type,
so `K' ↪ K` is a homotopy equivalence. After all vertices at distance `m` are deleted the
vertex set is `W_{m−1}`. By induction `Flag(X[W])` is homotopy equivalent to a point. ∎

**Lemma B.** `Flag(X)` is contractible, and so is `Flag(X^r)` for every `r ≥ 1`, where `X^r`
joins vertices at distance `≤ r`.

*Proof.* A map of a sphere into `Flag(X)` has image in a finite subcomplex, which lies in
`Flag(X[B(b, R)])` for some `R`, contractible by Lemma A. So all homotopy groups vanish and
`Flag(X)` is contractible by Whitehead's theorem. For `X^r`: balls of `X^r` are balls of `X`
(`B_{X^r}(v, t) = B_X(v, rt)`), so `X^r` is Helly (Chalopin–Chepoi–Genevois–Hirai–Osajda,
*Helly groups*, arXiv:2002.06895v3, Lemma 5.28: "Rips complexes R_δ(G) of a Helly graph G are
Helly"), and it is connected and locally finite; apply the first part. ∎

## 3. Proof of Theorem H

*(1)* `T_s` is finite: `g x_0` lies in the finite ball `B(x_0, 2s)`, and each fibre of
`g ↦ g x_0` is a coset of the finite stabilizer of `x_0`. It is symmetric since
`d(x_0, g^{-1} x_0) = d(g x_0, x_0)`. It generates: for `g ∈ G` take a path
`x_0 = p_0, ..., p_M = g x_0` in `X` and `g_i` with `d(p_i, g_i x_0) ≤ D`, `g_0 = 1`,
`g_M = g`. Then `d(g_i x_0, g_{i+1} x_0) ≤ 2D + 1 ≤ 2s`, so `g_i^{-1} g_{i+1} ∈ T_s ∪ {1}`.

*(2)* `ρ(g, h) ≤ 2s` iff `g^{-1} h ∈ T_s ∪ {1}`, so `VR_{2s}(G, ρ) = Flag(Cay(G, T_s)) =
VR_1(G, d_{T_s})` (item 1 of `group-rips-complexes-are-cayley-graph-flag-complexes`).

For `g ∈ G` let `F_g = Flag(X[B(g x_0, s)])`, a full subcomplex of `Flag(X)`.

- *Cover.* Every simplex `C` of `Flag(X)` is a clique; for `c ∈ C`,
  `C ⊆ B(c, 1) ⊆ B(g x_0, D + 1) ⊆ B(g x_0, s)` for some `g`. So `Flag(X) = ⋃_g F_g`.
- *Intersections.* For finite `σ ⊆ G`, `⋂_{g ∈ σ} F_g = Flag(X[W_σ])` with
  `W_σ = ⋂_{g ∈ σ} B(g x_0, s)`. If nonempty, it is contractible by Lemma A.
- *Nerve.* `⋂_{g ∈ σ} F_g ≠ ∅` iff `W_σ ≠ ∅` iff (Helly) the balls `B(g x_0, s)`, `g ∈ σ`,
  pairwise intersect, iff `ρ(g, h) ≤ 2s` for all `g, h ∈ σ`. So the nerve of the family
  `(F_g)_{g ∈ G}` is exactly `VR_{2s}(G, ρ)`. Repeated subcomplexes (`g x_0 = h x_0`) are
  allowed as separate members of the family.

By the Nerve Theorem for a simplicial complex covered by a family of subcomplexes all of whose
nonempty finite intersections are contractible (Borsuk 1948; Björner, *Topological methods*,
Handbook of Combinatorics, 1995, Theorem 10.6(i); statement quoted from memory, to be checked
by the verifier), `VR_{2s}(G, ρ) ≃ Flag(X)`, which is contractible by Lemma B. The family is
locally finite (a vertex lies in `F_g` only for the finitely many `g` with
`d(g x_0, v) ≤ s`) and every member is a finite complex. ∎

*Proof of Corollary H'.* `d_T(g, h) ≤ r` iff `g, h` are at distance `≤ r` in `X`, so
`VR_r(G, d_T) = Flag(X^r)`, contractible by Lemma B. ∎

## 4. Model tests

- `Z` acting on the path graph `P_∞` (Helly) with `x_0 = 0`, `D = 0`, `s = 1`: `T_1 =
  {±1, ±2}` and `Flag(Cay(Z, {±1, ±2}))` is the "strip" of triangles `{n, n+1, n+2}`,
  contractible. ✓
- `Z` acting on the same path by translation by 2 (two vertex orbits), `D = 1`, `s = 2`:
  `T_2 = {g : |2g| ≤ 4} \ {0} = {±1, ±2}`, same complex. ✓
- The hypothesis that `X` is Helly is used in the nerve identification and Lemma A. The
  4-cycle `C_4` is not Helly (the balls `B(v, 1)` of opposite vertices pairwise meet but the
  four have no common vertex) and `Flag(C_4)` is a circle, so Lemma B fails without Helly. ✓
- Torsion is allowed: a finite group acting on a single vertex gives `D = 0`, `s = 1`,
  `T_1 = G \ {1}`, and `Flag(Cay(G, G \ {1}))` is a simplex. ✓

## 5. Scope

Groups covered (read from arXiv:2002.06895v3, Theorems 1.1 and 1.3 and p. 4): Gromov hyperbolic
groups; CAT(0) cubical groups (geometric actions, not only vertex-transitive ones); finitely
presented graphical C(4)–T(4) small cancellation groups; type-preserving uniform lattices in
Euclidean buildings of type `C_n`; free products and HNN extensions of Helly groups over finite
subgroups; graph products of Helly groups; quotients by finite normal subgroups; finite-index
subgroups; and, by Huang–Osajda as reported there, FC-type Artin groups and weak Garside groups
of finite type (e.g. braid groups). The torsion-free ones are of type F.

Not covered: Helly groups are biautomatic (arXiv:2002.06895v3, Theorem 1.5(1)), so a group of
type F whose Dehn function is not quadratic, such as `BS(1,2)` or the integral Heisenberg group,
is not Helly. Theorem H gives only reading (W) of Problem 4.7 (some generating set), not type R
for a prescribed generating set, except in Corollary H'.

Relation to earlier work.

- Zaremsky (arXiv:1812.10976v3, Proposition 6.1 and Theorem 6.2) proves that an orbit of a
  geometric action on a space with the Arbitrarily Pinched Strong Link Criterion, e.g. an
  asymptotically CAT(0) space, has a contractible Vietoris–Rips complex. For torsion-free
  groups that orbit complex is a Cayley clique complex
  (`torsion-free-asymptotically-cat0-groups-have-contractible-rips`).
- Those pinched criteria are Euclidean-type, and ℓ∞-type spaces fail them: in `(Z^2, d_∞)`,
  `B_t(x) ∩ B_t(y)` has diameter `2t` when `d(x, y) = t`.
- Zaremsky's later small-ball criterion (arXiv:2410.11993v2, Theorem 3.1) does apply to
  orbits in coarsely injective spaces. That gives a second proof for torsion-free Helly groups
  and extends to hierarchically hyperbolic groups
  (`coarsely-injective-groups-have-contractible-rips-complexes`).
- The nerve proof above is independent of both, allows torsion, and gives the explicit scales
  `2s ≥ 2D + 2`.
- Novelty of the ℓ∞-type statements has not been checked beyond the sources read (Zaremsky
  1812.10976 and 2410.11993; Li–Sánchez Saldaña 2608.24279; Hulbert–Zaremsky 2608.25614,
  abstract only).
