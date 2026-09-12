# Every Cayley graph of F_2 x Z: how far nonunimodular lifts reach, and where they stop

Lane `bs-f2xz-all-generating-sets`, 2026-09-12.

## 1. The question, from source

Choi–Seo arXiv:2508.08932v2, `perc.tex` (fetched as the arXiv e-print on MSI,
2026-09-12), Question 1.3 (`\label{ques:f2z}`), verbatim:

> Does every Cayley graph of $F_{2} \times \Z$ have a nonuniqueness phase?

The paragraph after it says that there is currently no strategy for free-by-cyclic
groups whose monodromy has finite order, and that Hutchcroft's nonunimodular theorem
covers `T_k x Z^d` for `k >= 3`. The acknowledgements record that Hutchcroft told the
authors the question is still unanswered.

## 2. Tree-projected sets: the lifted-tree method, classified

Let `S` be a generating set of `F_n x Z` with `pi(S) ⊆ {1} ∪ B ∪ B^(-1)` for a free
basis `B`. The *oriented shapes* are the `2n` sets `D_s`, `-D_s`, up to translation.
A fibre-affine automorphism `(g,m) -> (phi g, eps m + h(g))` must send each oriented
edge to one whose shape is `eps` times its own, up to translation
(Section 3, step 2). So the local freedom
is exactly the partition of the four edge-ends at a vertex per letter into
equal-shape classes. There are three cases.

| shape coincidence | what may move | result |
|---|---|---|
| `D_s = c - D_s` for one letter | reverse that letter | `fpbs-tree-projected-reversible-letter-nonunimodular` (3 orbits, ratio 1/2) |
| `D_t = D_s + c` or `D_t = c - D_s` for two letters | exchange them, keep orientations | `fpbs-tree-projected-letter-exchange-nonunimodular` (3 orbits, ratio 1/2), new today |
| none: all oriented shapes distinct (*rigid*) | nothing beyond `Gamma ⋊ Z/2` | obstruction, Section 3 below |

**Why the exchange case works.** Exchanges keep orientation, so the covering tree is
the directed tree with two outgoing and two incoming exchange edges at each vertex.
For a transitive group the mass transport principle forces unimodularity: every
modular ratio on an edge is 1, because the two in-neighbours must have ratios summing
to 2 with values in `{1/2,1,2}`. With three orbits that fails. The directed
edge-indexed graph

```text
u->w (2:1), w->x (1:2), x->w (1:1), x->u (1:1), w->u (1:1)
```

has tail and head index sums 2 at each vertex, and its Bass–Kulkarni equations have
no positive solution. Its modular ratio around `w -> x -> w` is 1/2.

**Covered now, previously listed as open:**
`{(a,0),(a,1),(a,3),(b,0),(b,1),(b,3),(1,1)}`, since `D_a = D_b`.

**Smallest rigid shapes.** Sets of at most two heights are symmetric. Among 3-sets,
the gap types up to reversal are `(1,1)` (symmetric), `(1,2)`, `(1,3)`, `(2,3)`, and so
on. So the smallest rigid pair uses gap types `(1,2)` and `(1,3)`:
`D_a = {0,1,3}`, `D_b = {0,1,4}`.

## 3. The rigid example has a discrete automorphism group

`X_rig = Cay(F_2 x Z, {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}^±)`, degree 14.
Write `D(epsilon)` for the height changes of `X`-edges over an oriented tree edge
`epsilon`: `D_s` along `s`, `-D_s` against it. Let `theta` invert every basis letter
and `alpha(g,m) = (theta g, -m)`; `alpha(S) = S^(-1) = S`, so `alpha in Aut(X_rig)`.

1. **Fibre preservation.** No triangle meets three vertical lines, since the tree has
   none, and none lies in one line. A vertical edge `(g,m)–(g,m+1)` lies in one
   triangle per consecutive pair of an adjacent shape; `D_a, -D_a, D_b, -D_b` have one
   each, so 4 triangles. A horizontal edge over shape `E` at height `d` lies in
   `2|{d-1,d+1} ∩ E|` triangles: `2, 2, 0` for `D_a` at `0, 1, 3` and for `D_b` at
   `0, 1, 4`. So automorphisms keep vertical edges, hence vertical lines.
2. **Affine fibre maps and the shape equation.** A fibre-preserving `Psi` induces
   `phi in Aut(T)` and line automorphisms `m -> eps_g m + h(g)`. `eps` is constant,
   because heights along an edge stay bounded. Counting the `|D(epsilon)|` edges at a
   vertex over `epsilon` gives `D(phi epsilon) = eps D(epsilon) + h(g') - h(g)`.
3. **Rigidity.** The gap types `(1,2), (2,1), (1,3), (3,1)` of the four oriented
   shapes are distinct. So for `eps = +1` every label and orientation is kept, and for
   `eps = -1` every orientation is reversed and labels are kept. In both cases the
   translation is 0 and `h` is constant. Hence `phi = L_gamma` or `L_gamma o theta`,
   and `Psi in Gamma ⋊ <alpha>`.
4. **Unimodular.** Vertex stabilizers have order at most 2. For a closed subgroup `H`
   and `y = hx`, `H_y = h H_x h^(-1)`, so `|Stab_x y| = |Stab_y x|`.

Item 2–3 hold for every tree-projected set with vertical part `{(1,±1)}` whose `2n`
oriented shapes are pairwise distinct: every fibre-preserving automorphism lies in
`Gamma ⋊ <alpha>`. Item 1 is specific to `X_rig`. So:

* no closed nonunimodular subgroup exists, and Hutchcroft arXiv:1711.02590 Theorem 1.2
  is unavailable;
* any proof of `p_c < p_u` for `X_rig` must work on a unimodular transitive graph;
* the open reduction for it is the critical sphere-bubble estimate
  `fpbs-tree-projected-critical-sphere-bubble-below-one`, equivalently the L2 gap
  (`fpbs-tree-projected-sphere-bubble-l2-equivalence`);
* the large-rank adjacency criterion does not apply at rank 2
  (`fpbs-tree-projected-large-rank-strict-thresholds`).

Check script: `research/artifacts/fpbs/scripts/letter_exchange_rigid_check.py` (MSI
run, 2026-09-12: all four exchange lifts gave 0 bad edges; the rigid controls broke
edges for every shift; triangle census 4 vs 0/2; only the identity and the
reverse-all type maps).

## 4. Generating sets that are not tree-projected

Q1.3 quantifies over all generating sets. After applying `Aut(F_2 x Z)`, a set is
tree-projected iff `pi(S) \ {1}` lies in a free basis and its inverses. Two
qualitatively different kinds remain.

1. **Projected graph with cut vertices.** Example: `{(a,0),(b,0),(ab,1)}` (degree 6).
   It generates, because `(ab,1)(b,0)^(-1)(a,0)^(-1) = (1,1)`. `Cay(F_2,{a,b,ab})`
   should be a tree of triangles: in the presentation `<a,b,c | a b c^(-1)>` each
   letter occurs once in the relator, so each edge lies in exactly one triangle
   2-cell. This was not checked beyond that count. Every decoration here is a single height, so every
   oriented shape is symmetric. Lifts must preserve the height holonomy `-1` of each
   oriented triangle. Automorphisms of the block tree that keep the cyclic orientation
   of triangles lift, but local actions on a triangle are only rotations, so orbit
   sizes on a triangle are 1 or 3. A nonunimodular quasi-transitive subgroup looks
   possible, using at least two vertex classes of different incidence counts. **Not
   carried out; no claim is made.**
2. **Two-connected projected graph.** For a generic finite generating set of `F_2`
   the projected Cayley graph has no cut vertex, and with generic decorations
   `Aut(X)` is expected to be `Gamma` up to a finite group. Then, as for `X_rig`, no
   nonunimodular argument exists. This is expected, not proved.

## 5. What this means for Q1.3

The nonunimodular route can settle at most the Cayley graphs with some local shape
coincidence. `X_rig` shows that some Cayley graphs of `F_2 x Z` have discrete
automorphism groups, so Q1.3 is not reducible to Hutchcroft's theorem. The open core
is a unimodular argument on graphs like `X_rig`: the critical sphere-bubble or
relative-susceptibility estimates already recorded under
`fpbs-tree-projected-cayley-graphs-strict-thresholds`.

Novelty was checked only against Cairn. The exchange construction is an elementary
variant of the reversible-letter one.
