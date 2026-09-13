# BNSR invariants of graph braid groups, part 2: hyperplane-affine characters and the matching-complex criterion

Lane z1-08-graph-braid, 2026-09-13. Notation as in part 1. `Γ` is
sufficiently subdivided, and `X = UD_nΓ` with universal cover `X̃`, a CAT(0)
cube complex on which `B_nΓ` acts freely and cocompactly.

## 1. Moves, links, hyperplane classes

A vertex of `X` is a configuration `S`: a set of `n` vertices of `Γ`. A
**move** at `S` is a triple `(v, e, w)` with `v ∈ S`, `e = [v,w]` an edge of
`Γ` and `w ∉ S`. The edges of `X` at `S` are exactly the moves at `S`.

The cubes of `X` containing `S` are the sets of moves
`{(v_i,e_i,w_i)}` whose edges have pairwise disjoint closures. For moves at
the same `S` this holds iff the sources `v_i` are distinct and the targets
`w_i` are distinct. (`w_i ≠ v_j` is automatic, since targets are unoccupied.)

**Lemma 1 (links are matching complexes).** Let `B(S)` be the bipartite
graph with parts `S` and `V(Γ) \ S`, and one edge per move at `S`. Then
`lk_X(S)` is the matching complex of `B(S)`: its simplices are the sets of
pairwise disjoint edges of `B(S)`. ∎

**Parallelism.** In a square spanned by moves `(v,e,w)` and `(v',f,w')`,
opposite edges move the same particle along the same edge of `Γ`, and differ
only by the position of the other particle, which moves along `f`, an edge
disjoint from `ē`. The hyperplane class of an edge `(e, S∖{v})` of `X` is
determined by `e` and the class of the parked set `S∖{v}` under moves of
single particles along edges of `Γ_e := Γ − {v,w}` (delete both endpoints of
`e` and all incident edges). With sufficient subdivision, unordered
configurations in a connected graph are connected by such moves. So:

**Lemma 2.** Hyperplane classes of `X` correspond to pairs `(e, κ)`. Here
`e` is an edge of `Γ`, and `κ` assigns to each component of `Γ_e` a number
of particles, with `Σκ = n − 1` and each component holding at most its
number of vertices.

A function `c` on oriented hyperplane classes with
`c(e reversed, κ) = −c(e, κ)` defines a cellular 1-cochain on `X`: the value
on an oriented edge is the value on its class. It is a cocycle, because the
boundary of a square is `a + b − a − b` with the opposite values equal. Call
such cocycles **affine**. An affine cocycle `c` defines a character
`χ_c: B_nΓ → ℝ`, and a `χ_c`-equivariant height `h_c: X̃ → ℝ` that is affine
on each cube.

Examples:

- `c(e, κ) = a(e)` for a 1-cochain `a` on `Γ` gives the circulation
  characters, the image of `H^1(Γ;ℝ) → H^1(B_nΓ;ℝ)`.
- Cochains depending on `κ` see how particles are distributed around the
  moving edge. These include the exchange characters of tree braid groups,
  for which `H^1(Γ) = 0`.

Whether every character of `B_nΓ` is `χ_c` for some affine `c` is recorded
as open (`graph-braid-characters-are-hyperplane-affine`).

Lemma 2 describes the classes and is used only for examples and for the
open inputs below. Theorem M uses only that `c` is constant on hyperplane
classes.

## 2. Theorem M (sufficient criterion)

Call `c` **generic** if `c(e, κ) ≠ 0` for every class. At a configuration
`S`, the **ascending move graph** `B↑_c(S)` is the subgraph of `B(S)` of
moves `(v,e,w)` with `c > 0` on their class.

**Theorem M.** Let `c` be a generic affine cocycle on `UD_nΓ`, and `m ≥ 1`.
Suppose that for every configuration `S` the matching complex of `B↑_c(S)`
is `(m − 1)`-connected (for `m = 1`: nonempty and connected). Then
`[χ_c] ∈ Σ^m(B_nΓ)`.

**Proof.**

1. `h = h_c` is affine on cubes and nonconstant on edges, because `c` is
   generic. So it is a Morse function in the sense of Bestvina–Brady
   (Invent. Math. 129 (1997), §2).
2. For a vertex `x̃ ∈ X̃` over `S`, a cube at `x̃` has `x̃` as its lowest
   vertex iff all its edges at `x̃` ascend. So the ascending link of `x̃` is
   the full subcomplex of `lk(S)` on ascending moves. By Lemma 1 this is the
   matching complex of `B↑_c(S)`.
3. By the Bestvina–Brady Morse lemma (their §2, applied to `−h`): for
   `s < t`, `X̃_{≥s}` is homotopy equivalent to `X̃_{≥t}` with cones attached
   along the ascending links of the vertices at heights in `[s, t)`. Cones
   attached along `(m−1)`-connected subcomplexes make the inclusion
   `X̃_{≥t} ↪ X̃_{≥s}` `m`-connected.
4. `X̃ = ⋃_s X̃_{≥s}` is contractible, and homotopy groups commute with this
   increasing union. So each `X̃_{≥t}` is `(m − 1)`-connected.
5. By the geometric criterion for BNSR invariants (Bieri–Geoghegan; for a
   free cocompact action on a contractible complex with equivariant height,
   `[χ] ∈ Σ^m` iff the filtration `(X̃_{≥t})_t` is essentially
   `(m−1)`-connected; see Bux–Gonzalez, J. London Math. Soc. 60 (1999), and
   Witzel–Zaremsky, arXiv:1501.06682, §1), `[χ_c] ∈ Σ^m(B_nΓ)`. ∎

**Calibration, `n = 1`.** `UD_1Γ = Γ` and `B_1Γ = F_r`. `B↑(v)` is the star
of ascending edges at `v`. Its matching complex is a discrete set of
vertices, and it is connected and nonempty iff exactly one edge ascends from
every vertex. Then `|E| = |V|`, i.e. `r = 1`. So Theorem M yields `Σ¹` only
for `ℤ` (the cycle, with the rotation cocycle), consistent with
`Σ¹(F_r) = ∅` for `r ≥ 2`.

**RAAG comparison.** For the Salvetti complex, ascending links are flag
complexes on living positive directions, and Meier–Meinert–VanWyk
(arXiv:math/9310202 for `Σ¹`) prove the matching negative direction. Here
the links are matching complexes of bipartite graphs, which are not joins.
So the negative direction does not follow formally. It is recorded as open
(`graph-braid-ascending-matching-complex-criterion-is-exact`).

## 3. What would finish Problem 1.8

Three inputs:

- (A) every character is hyperplane-affine;
- (B) the exact converse: `[χ] ∈ Σ^m(B_nΓ)` implies that some generic
  affine representative, or a limiting horizontal version à la Bux–Gonzalez,
  satisfies the matching-complex condition;
- (C) a closed description of `(m−1)`-connectivity of matching complexes of
  bipartite move graphs, e.g. via chessboard-complex connectivity bounds
  (Björner–Lovász–Vrećica–Živaljević).

These give an explicit criterion in terms of `Γ`, `n` and the values of `c`,
i.e. `graph-braid-group-sigma-invariants-explicit-formula`. Part 1's
Euler-characteristic obstruction constrains (B): when `e(UD_nΓ) ≠ 0` no
antipodal pair survives at level `d = min(n, k(Γ))`.
