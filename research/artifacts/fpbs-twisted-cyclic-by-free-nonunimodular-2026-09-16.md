# Twisted cyclic-by-free groups: a nonunimodular automorphism subgroup for every tree-projected Cayley graph

Date: 2026-09-16. Supports `fpbs-tree-projected-twisted-cyclic-by-free-nonunimodular`
through the route `fpbs-twisted-cyclic-by-free-nonunimodular-proof`, and the
reduction `fpbs-tree-projected-reduce-to-rigid-decorations`.

**Result.** Let `Gamma` be finitely generated, with an infinite cyclic normal
subgroup `H` that is not central, and `Gamma/H ≅ F_n` with `n >= 2`. Let `S` be a
finite symmetric generating set whose image in `F_n` lies in `{1} ∪ B ∪ B^(-1)`
for a free basis `B`. Then `Aut(Cay(Gamma,S))` contains a closed nonunimodular
subgroup with four vertex orbits. So `p_c < p_(2->2)` and `p_c < p_u` by Hutchcroft.
No condition is placed on the decoration sets.

Contents:
1. Normal form
2. The shape lemma
3. Lifting without a height potential
4. The edge-indexed graph and its covering tree
5. Identification of the covering tree with the structured free tree
6. The lifted group
7. Counting and nonunimodularity
8. Conclusion
9. Remarks: what fails over `F_n x Z`, the unimodular structure group, abelian
   coefficients, relation to known theorems, and the reduction of the root
10. Computational check

## 1. Normal form

Let `z` generate `H`, and let `pi : Gamma -> F_n` be the quotient map.

*Splitting.* For each `s in B` choose `sigma(s) in pi^(-1)(s)`. Since `F_n` is free
on `B`, `sigma` extends to a homomorphism `sigma : F_n -> Gamma` with
`pi o sigma = id`.

*Action.* Conjugation on `H ≅ Z` gives `Gamma -> Aut(Z) = {±1}`. It is trivial on
the abelian group `H`, so it factors as `chi o pi` with `chi : F_n -> {±1}` a
homomorphism, and `sigma(g) z sigma(g)^(-1) = z^(chi(g))`.

*Isomorphism.* Every element of `Gamma` is uniquely `z^m sigma(g)`, with
`g = pi(element)` and `m` determined because `H ∩ sigma(F_n) = 1`. We have

```text
z^m sigma(g) z^(m') sigma(g') = z^m (sigma(g) z^(m') sigma(g)^(-1)) sigma(g) sigma(g')
                              = z^(m + chi(g) m') sigma(g g').
```

So `Gamma ≅ Z ⋊_chi F_n`, written as pairs `(m,g)` with

```text
(m,g)(m',g') = (m + chi(g) m', g g'),     (m,g)^(-1) = (-chi(g) m, g^(-1)).
```

*Central kernel.* `H` is central iff `sigma(F_n)` commutes with `z`, iff `chi = 1`.
If `chi = 1`, then `Gamma ≅ F_n x Z`. If `chi ≠ 1`, the centre of `Gamma` is
trivial:
* a central `(m,g)` projects to the centre of `F_n`, which is trivial, so `g = 1`;
* `(m,1)` commutes with `(0,s)` for all `s` iff `m = chi(s) m` for all `s`, which
  forces `m = 0`.

Conversely, an infinite cyclic normal subgroup `<(g,k)>` of `F_n x Z` satisfies
`h g h^(-1) = g^(±1)` for every `h in F_n`, so `g = 1` since `n >= 2`, and it is
central. So the non-central case is exactly the case that `Gamma` is not `F_n x Z`.
This is what `fpbs-tree-projected-cayley-graphs-strict-thresholds` calls
"non-split groups". Every such extension splits, so the phrase can only mean
"not a direct product".

*Generating set.* Since `pi(S)` generates `F_n` and lies in `{1} ∪ B ∪ B^(-1)`,
and `S` is symmetric, every `s in B` has `s` and `s^(-1)` in `pi(S)`. Put

```text
D_s = {d in Z : (d,s) in S}  (s in B),        V = {v in Z : (v,1) in S}.
```

Then each `D_s` is finite and nonempty, and `V = -V`. The elements of `S` over
`s^(-1)` are `(d,s)^(-1) = (-chi(s) d, s^(-1))` for `d in D_s`. So `S` is determined
by `(D_s)_(s in B)` and `V`. The sets `D_s` and `V` are otherwise arbitrary, subject
only to `S` generating `Gamma`.

Fix `s_0 in B` with `chi(s_0) = -1`, and put `O = B \ {s_0}`, which is nonempty.

## 2. The shape lemma

`X = Cay(Gamma,S)` has edges `{gamma, gamma sigma}` for `sigma in S`. Let
`T = Cay(F_n,B)`. Colour `g in F_n` by `c(g) = chi(g) in {+,-}`.

*Vertical edges.* `(m,g)(v,1) = (m + chi(g) v, g)`. Since `V = -V`, the vertical
neighbours of `(m,g)` are `(m+v,g)` for `v in V`.

*Horizontal edges.* Every edge between the fibres over `g` and `gs` (`s in B`) comes
from a generator over `s` at `(m,g)`, or over `s^(-1)` at `(m',gs)`:

```text
(m,g)(d,s)               = (m + chi(g) d, gs),
(m',gs)(-chi(s) d, s^(-1)) = (m' - chi(gs) chi(s) d, g) = (m' - chi(g) d, g).
```

Both give the same edge set:

```text
E(g,s) = { (m,g)–(m + chi(g) d, gs) : m in Z, d in D_s }.
```

**Lemma 2.1 (shape).** Orient the tree edge `{g,gs}` as `p -> q`, with
`(p,q) = (g,gs)` if `c(g) = +` and `(p,q) = (gs,g)` if `c(g) = -`. Then

```text
E(g,s) = { (m,p)–(m+d,q) : m in Z, d in D_s }.
```

*Proof.* If `c(g) = +` this is the formula above. If `c(g) = -`, the edge
`(m,g)–(m-d,gs)` is `(m',gs)–(m'+d,g)` with `m' = m-d`, and `m'` runs over `Z`.

**Lemma 2.2 (local structure).** Let `g in F_n`.
* If `chi(s) = -1`, the `s`-edges at `g` are `{g,gs}` and `{gs^(-1),g}`. Both
  neighbours have the other colour. Every `s`-edge points from its `+` end to its
  `-` end, so at a `+` vertex both `s`-edges point out, and at a `-` vertex both
  point in.
* If `chi(s) = +1`, both neighbours have the colour of `g`. At a `+` vertex,
  `{g,gs}` points out of `g`, and `{gs^(-1),g}` has `c(gs^(-1)) = +` and points
  into `g`. At a `-` vertex, `{g,gs}` points into `g` and `{gs^(-1),g}` points
  out. So each vertex has exactly one outgoing and one incoming `s`-edge.

*Proof.* `c(gs) = c(g) chi(s)`. The orientation rule of Lemma 2.1 takes the tail to
be the `+` end when the colours differ. When they agree it takes the tail to be `g`
if `c(g) = +` and `gs` if `c(g) = -`.

Call colours, labels and these orientations the *structure* of `T`. The
orientations determine the colours, since `s_0` is twisted.

## 3. Lifting without a height potential

**Lemma 3.1.** Let `phi` be an automorphism of `T` that preserves labels and
orientations, and let `k in Z`. Then

```text
Psi_(phi,k)(m,g) = (m + k, phi g)
```

is an automorphism of `X`.

*Proof.*
* Vertical edges `(m,g)–(m+v,g)` go to `(m+k,phi g)–(m+k+v,phi g)`, which are
  edges.
* A horizontal edge over the `s`-edge `p -> q` is `(m,p)–(m+d,q)` with `d in D_s`
  (Lemma 2.1). Its image is `(m+k,phi p)–(m+k+d,phi q)`. Since `phi` preserves
  labels and orientations, `phi p -> phi q` is an oriented `s`-edge of `T`, so the
  image lies in `E` over it by Lemma 2.1 again.
* `Psi_(phi,k)` is a bijection with inverse `Psi_(phi^(-1),-k)`, which is of the
  same form. So both directions preserve adjacency.

*Contrast with `F_n x Z`.* There `chi = 1`, so every vertex of `T` has one
outgoing and one incoming `s`-edge for **every** letter. An automorphism fixing `g`
and exchanging `{g,gs}` with `{gs^(-1),g}` reverses an orientation. It lifts only
if `-D_s` is a translate of `D_s`, with a height potential absorbing the
translation, as in `fpbs-reversible-letter-nonunimodular-proof`. In the twisted
group, the two `s_0`-edges at a vertex carry the same outgoing (or incoming) shape
`D_(s_0)`. So exchanging them costs nothing, whatever `D_(s_0)` is.

## 4. The edge-indexed graph and its covering tree

**The graph `A`.** Vertices `u, w` of colour `+` and `x, y` of colour `-`. An edge of
`A` has a label in `B` and a positive integer index at each end. For untwisted labels
it also has a distinguished tail.

| label | edges (index at first end : index at second end) |
|---|---|
| `s_0` | `e_1 = {u,x}` `2:1`, `e_2 = {x,w}` `1:1`, `e_3 = {w,y}` `1:2` |
| `r in O`, `chi(r) = -1` | `{u,x}`, `{x,w}`, `{w,y}`, `{y,u}`, all `1:1` |
| `o in O`, `chi(o) = +1` | `u -> w`, `w -> u`, `x -> y`, `y -> x`, all `1:1` |

*Index sums.* For a twisted label `r`, the indices of the `r`-edge ends at each
vertex sum to 2.
* For `s_0`: at `u`, `e_1` gives 2; at `x`, `e_1` and `e_2` give `1+1`; at `w`,
  `e_2` and `e_3` give `1+1`; at `y`, `e_3` gives 2.
* For other twisted `r`, the 4-cycle `u–x–w–y–u` meets every vertex twice with
  index 1.

For an untwisted label `o`, every vertex has one outgoing `o`-end of index 1 and
one incoming `o`-end of index 1. Twisted edges join a `+` vertex to a `-` vertex,
untwisted edges join vertices of equal colour, and `A` has no loops.

**The covering tree `Y`.** A tree `Y` with a map `p : Y -> A` on vertices and
edges is a *covering tree* if, for every `y in Y` over `a` and every edge end
`epsilon` of `A` at `a`, exactly `i(epsilon)` edges at `y` lie over the edge of
`epsilon` (with `y` at the end `epsilon`, which is automatic since `A` has no
loops). Such a tree exists: start from `y_0` over `u`, and at every new vertex
entered through an edge over the end `eta`, attach `i(epsilon) - [epsilon = eta]`
new edges over each end `epsilon`, with new far ends over the other end vertex of
`epsilon`. Every fibre of `p` is nonempty, because `e_1, e_2, e_3` connect
`u, x, w, y`.

**Lemma 4.1 (extension).** Let `y, y' in Y` lie over the same vertex, and let
`beta` be a bijection from the edges at `y` to the edges at `y'` with
`p o beta = p`. Then some `phi in Aut(Y)` with `p o phi = p` and `phi y = y'`
extends `beta`.

*Proof.* Define `phi` on the ball of radius `r` by induction. Suppose `z` is at
distance `r >= 1` from `y`, has been mapped to `phi z`, and was entered through an
edge over the end `eta` at `p(z)`. Then `z` has `i(epsilon) - [epsilon = eta]`
further edges over each end `epsilon` at `p(z)`. So does `phi z`, entered through
the image edge, which lies over the same end. Any `p`-preserving bijection between
these further edges extends `phi` to the next sphere. Both `Y` and its image are
trees, so the result is an automorphism.

**Consequences.** Let `G_A = {phi in Aut(Y) : p o phi = p}`.
1. `G_A` is closed in the pointwise topology, since `p o phi = p` is a pointwise
   condition.
2. `G_A` is transitive on each fibre of `p`, because the counts at two vertices over
   one vertex agree, so some `beta` exists. So `G_A` has exactly four vertex orbits.
3. For `y` over `a` and an end `epsilon` at `a`, the stabilizer `(G_A)_y` permutes
   the `i(epsilon)` edges at `y` over `epsilon` transitively, by Lemma 4.1 with
   `y' = y`.

## 5. Identification of the covering tree with the structured free tree

Give `Y` the following structure:
* the colour of `y` is the colour of `p(y)`;
* the label of an edge is the label of its image;
* an edge over a twisted edge of `A` points from its `+` end to its `-` end;
* an edge over an untwisted `a -> b` points from its end over `a` to its end over
  `b`.

**Lemma 5.1.** Every vertex of `Y` has the local structure of Lemma 2.2.
* For each twisted `r`, a `+` vertex has two outgoing `r`-edges to `-` vertices,
  and a `-` vertex has two incoming `r`-edges from `+` vertices.
* For each untwisted `o`, every vertex has one outgoing and one incoming `o`-edge
  to vertices of its own colour.

*Proof.* Directly from the index sums of Section 4 and the covering property.

**Lemma 5.2.** There is a graph isomorphism `iota : Y -> T` with `iota(y_0) = 1`
that preserves colours, labels and orientations.

*Proof.* Define `iota` sphere by sphere. The *type* of an edge at a vertex is its
label `r` if `r` is twisted, and the pair (label, in/out) if it is untwisted. By
Lemmas 2.2 and 5.1, a vertex of `Y` and a vertex of `T` of the same colour have the
same number of edges of each type: 2 for each twisted label, 1 for each untwisted
(label, direction). The type of an edge and the colour at one end determine the
colour at the other end, on both sides.
* `y_0` has colour `+` and `1 in F_n` has `chi(1) = +1`. Match the edges at `y_0`
  to the edges at `1` by any type-preserving bijection.
* At a later matched vertex `z -> g`, the parent edges have the same type. Match
  the remaining edges type by type, and send far ends to far ends. The colours
  agree by the observation above.

The resulting map is a bijection on every star. A connected graph mapping onto a
tree by a map that is bijective on stars is isomorphic to it, because trees are
simply connected. So `iota` is an isomorphism, and it preserves the structure by
construction.

**Lemma 5.3.** Every `phi in G_A` preserves colours, labels and orientations of `Y`.
Hence `phi' = iota phi iota^(-1)` is an automorphism of `T` satisfying Lemma 3.1.

*Proof.*
* Colours and labels are read from `A`, and `p o phi = p`.
* A twisted edge is oriented through colours, which are preserved.
* An edge over the untwisted `a -> b` is mapped to an edge over the same edge of
  `A`, and its end over `a` goes to the end over `a`.

## 6. The lifted group

Let

```text
L = { Psi_(phi',k) : phi in G_A, k in Z } ⊆ Aut(X).
```

1. *Group.* `Psi_(phi',k) Psi_(psi',l) = Psi_((phi psi)',k+l)` and
   `Psi_(phi',k)^(-1) = Psi_((phi^(-1))',-k)`. So `L ≅ G_A x Z`.
2. *Closed.* Suppose `Psi_j = Psi_(phi'_j,k_j) -> Psi` pointwise on the discrete
   vertex set `Z x F_n`. For each `g`, `Psi_j(0,g) = (k_j, phi'_j g)` is eventually
   constant. So `k_j` is eventually a constant `k`, and `phi'_j -> phi'` pointwise,
   where `phi'` is a bijection because `Psi` is. Then `phi_j -> phi = iota^(-1) phi' iota`
   pointwise, and `phi in G_A` by closedness. So `Psi = Psi_(phi',k) in L`.
3. *Orbits.* `(m,g)` and `(m',g')` lie in one `L`-orbit iff `iota^(-1) g` and
   `iota^(-1) g'` lie in one `G_A`-orbit, since `k` is free. So `L` has four vertex
   orbits and is quasi-transitive.
4. *Stabilizers.* `Psi_(phi',k)(m,g) = (m,g)` iff `k = 0` and `phi' g = g`. So
   `phi -> Psi_(phi',0)` is an isomorphism from `(G_A)_(iota^(-1) g)` onto
   `L_((m,g))`. For two vertices it maps the intersection of the two
   `G_A`-stabilizers onto the intersection of the two `L`-stabilizers. So

   ```text
   |L_((m,g)) (m',g')| = [L_((m,g)) : L_((m,g)) ∩ L_((m',g'))]
                       = [(G_A)_(iota^(-1) g) : (G_A)_(iota^(-1) g) ∩ (G_A)_(iota^(-1) g')].
   ```

## 7. Counting and nonunimodularity

Pick `t in O`. Walk in `Y` from `y_0` (over `u`) along the following ends of `A`.

| case | walk from `y_0` | forward indices | backward indices |
|---|---|---|---|
| `chi(t) = +1` | `t`-edge over `u -> w` to `z_1` (over `w`); `e_2` to `z_2` (over `x`); `e_1` to `y_1` (over `u`) | `1, 1, 1` | `2, 1, 1` |
| `chi(t) = -1` | `t`-edge over `{u,x}` to `z_2` (over `x`); `e_1` to `y_1` (over `u`) | `1, 1` | `2, 1` |

Here "forward indices" are the indices of the ends used when leaving each vertex
from `y_0`, and "backward indices" are those used when leaving each vertex from
`y_1`. Consecutive steps use different edges of `A`, so the far end of a step is
never the vertex just left.

**Lemma 7.1.** `|(G_A)_(y_0) y_1| = 1` and `|(G_A)_(y_1) y_0| = 2`.

*Proof.*
* Let `phi in (G_A)_(y_0)`. At each vertex of the walk, the next edge is the only
  edge at that vertex over the given end, since the forward index is 1. `phi` fixes
  the current vertex and preserves `p` on edges, so it fixes the next vertex. By
  induction `phi y_1 = y_1`.
* Let `phi in (G_A)_(y_1)`. The first backward step leaves `y_1` over the end of
  `e_1` at `u`, which has index 2. By consequence 3 of Section 4, `(G_A)_(y_1)`
  moves `z_2` over both of these edges' far ends. All later backward steps have
  index 1, so `phi z_2` determines `phi y_0` as in the first bullet. Conversely,
  `phi z_2` is the neighbour of `y_1` on the geodesic from `y_1` to `phi y_0`,
  since `Y` is a tree. So the orbit of `y_0` has exactly 2 elements.

**Nonunimodularity.** Put `x_0 = (0, iota y_0)` and `x_1 = (0, iota y_1)`. Both `y_0`
and `y_1` lie over `u`, so they are in one `G_A`-orbit, and `x_0, x_1` are in one
`L`-orbit. By item 4 of Section 6 and Lemma 7.1,

```text
|Stab_(x_0) x_1| = 1,        |Stab_(x_1) x_0| = 2.
```

Section 1 of Hutchcroft arXiv:1711.02590v3 defines a subgroup `Gamma' ⊆ Aut(G)` to
be unimodular if `|Stab_v u| = |Stab_u v|` for all `u, v` in one orbit, where
`Stab_v u` is the orbit of `u` under the stabilizer of `v`. So `L` is
nonunimodular. For the closed group `L` this agrees with the Haar-measure
definition, since `|L_(x_0) x_1| / |L_(x_1) x_0| = mu(L_(x_0)) / mu(L_(x_1))`.

The modular ratio `1/2` is the product of the ratios (index at the near end) /
(index at the far end) along the walk from `y_0` to `y_1`, in the Bass-Kulkarni
normalization. The script checks this product.

## 8. Conclusion

`L` is a closed, quasi-transitive (four orbits), nonunimodular subgroup of
`Aut(X)`, where `X = Cay(Gamma,S)` is connected and locally finite. Two imported
theorems apply.
* `fpbs-hyperbolic-and-nonunimodular-nonuniqueness`, item 2: arXiv:1711.02590v3
  Theorem 1.2, "Let G be a connected, locally finite graph, and suppose that Aut(G)
  has a quasi-transitive nonunimodular subgroup. Then p_c(G)<p_u(G)." So
  `p_c(X) < p_u(X)`.
* `fpbs-hyperbolic-nonunimodular-critical-l2-gap`, via the citation route
  `fpbs-hyperbolic-nonunimodular-critical-l2-gap-citation`: arXiv:1804.10191
  `thm:nonunimodular`, "Let G be a connected, locally finite graph, and suppose
  that Aut(G) has a quasi-transitive nonunimodular subgroup. Then
  p_c(G)< p_{q→q}(G) for every q∈(1,∞)." With `q = 2`, `p_c(X) < p_(2->2)(X)`.

## 9. Remarks

### 9.1 The structure group is unimodular; the covering structure is essential

Let `𝒢` be the group of automorphisms of `T` that preserve labels and orientations.
By Lemma 3.1 all of them lift, so `𝒢 x Z` acts on `X`.
* Orientations determine colours, so `𝒢` has two vertex orbits, and `ker chi` acts
  transitively on each colour.
* At a vertex, `𝒢_g` exchanges the two twisted `r`-edges freely and fixes each
  untwisted edge.
* So its quotient edge-indexed graph has two vertices `+, -`, one edge `2:2` for
  each twisted label, and a loop at each vertex for each untwisted label.

Every edge has equal indices at its two ends, so the modular function is trivial
on the generators and `𝒢` is unimodular. The nonunimodular `G_A` is a closed
subgroup of `𝒢`, by Lemma 5.3. The asymmetric indices `2:1`, `1:2` of `e_1, e_3`
come from `A`, not from `T`. This mirrors the reversible-letter and letter-exchange
constructions over `F_n x Z`, whose ambient groups are also unimodular.

### 9.2 Abelian coefficients (remark, not claimed)

Let `M` be a finitely generated abelian group and `chi : F_n -> {±1}` nontrivial,
acting on `M` by `m -> chi(g) m`. Take `Gamma = M ⋊_chi F_n` and a tree-projected
`S` with decoration sets `D_s ⊆ M` and vertical set `V = -V ⊆ M`. Then Sections 2 to
8 go through verbatim, with `Z` replaced by `M`. Examples are `Z^d ⋊_(-1) F_n` for
`d >= 1`. When `M` is finite, `Gamma` is virtually free and Hutchcroft's hyperbolic
theorem already applies. This remark is not recorded as a claim.

### 9.3 Relation to known theorems

* **Choi-Seo arXiv:2508.08932** proves strict thresholds on every Cayley graph of
  an acylindrically hyperbolic group. `Z ⋊_chi F_n` has the infinite amenable
  normal subgroup `H`. By a theorem of Osin (unverified here), acylindrically
  hyperbolic groups have no infinite amenable normal subgroup, so that theorem does
  not apply.
* **Lyons**, groups without fixed price 1: by Gaboriau's theorem (unverified
  here), groups with an infinite amenable normal subgroup have fixed price 1, so
  the fixed-price route does not apply either.
* **Large rank** (`fpbs-tree-projected-large-rank-strict-thresholds`) covers
  non-central kernels, but only when `v + 2m sqrt(2n-1) < 2n-1`, never in rank 2.
* The groups here form a special case of the open
  `fpbs-amenable-wq-normal-class-nonuniqueness` (infinite amenable wq-normal
  subgroup), restricted to tree-projected generating sets.

### 9.4 Reduction of the root

For `F_n x Z` and tree-projected `S`, consider the `2n` oriented shapes `D_s`,
`-D_s` (`s in B`) up to translation. Either two of them coincide or all are
distinct.
* `D_s ~ -D_s` means `D_s` is symmetric up to translation:
  `fpbs-tree-projected-reversible-letter-nonunimodular`.
* `D_s ~ D_t` or `D_s ~ -D_t` for `s ≠ t` means `D_t = D_s + c` or `D_t = c - D_s`:
  `fpbs-tree-projected-letter-exchange-nonunimodular`.
* `-D_s ~ -D_t` is the same as `D_s ~ D_t`.
* Otherwise the decorations are rigid: `fpbs-tree-projected-rigid-decorations-strict-thresholds`.

With Section 1 and the present claim for `chi ≠ 1`, the root
`fpbs-tree-projected-cayley-graphs-strict-thresholds` follows from these three
`F_n x Z` claims and the twisted claim. Route:
`fpbs-tree-projected-reduce-to-rigid-decorations`.

## 10. Computational check

Script: `experiments/fpbs-twisted-cyclic-by-free-2026-09-16/twisted_lift_check.py`.
Run single-threaded with `timeout 600 python3 twisted_lift_check.py` on 2026-09-16;
it takes a few seconds. For each case it does the following.

1. **Part 1.** It computes, from the group law alone, the set of heights `m'` with
   `(m',gx)` adjacent to `(0,g)` for every `g` in the radius-4 ball of `F_n` and
   every letter `x`. It compares this with Lemma 2.1 (`D_s` if `g` is the tail,
   `-D_s` otherwise) and checks the vertical neighbours `V`.
2. **Part 2.** It builds a ball of radius 9 of `Y` and checks the index sums of `A`.
   It builds `iota` sphere by sphere and checks the colours and type counts of
   Lemma 5.2, and injectivity. It then draws random `p`-preserving automorphisms of
   `Y`, alternately fixing `y_0` and moving `y_0` to `y_1`, as in the proof of
   Lemma 4.1. It transports them to `T` and tests Lemma 3.1 with `k = 0` and **no
   height potential**: every oriented tree edge `g -> gx` of the radius-4 ball must
   go to a tree edge with the same change set.
3. **Part 3.** It counts the lifts of the walks of Section 7 from `y_0` and from
   `y_1`, and the near/far index product.
4. **Control.** It transports the same automorphisms, built from the twisted
   `chi = (a: -1, b: +1)`, but tests them against the group law of `F_2 x Z` with
   the rigid data `D_a = {0,1,3}`, `D_b = {0,1,4}`, `V = {±1}`. No translate of `D_a`
   equals `-D_a`.

Output (abridged):

```text
n=2 chi={'a': -1, 'b': 1}  D_a=(0,1,3) D_b=(0,1,4) V=(1,)
  part1 bad 0; A index-sum defects 0; iota defects 0, injective
  |Stab_y0 y1| = 1  |Stab_y1 y0| = 2  near/far product 0.5
  lift check: 0 bad of 7728 oriented tree edges (zero height potential, 12 automorphisms)
n=2 chi={'a': 1, 'b': -1}  same data              -> part1 0, iota 0, counts 1 and 2, 0 bad of 7728
n=2 chi={'a': -1, 'b': -1} same data              -> part1 0, iota 0, counts 1 and 2, 0 bad of 7728
n=2 chi={'a': -1, 'b': -1} D_a=(0,2,7) D_b=(1,6,8) V=()
                                                  -> part1 0, iota 0, counts 1 and 2, 0 bad of 7728
n=3 chi=(-1,+1,+1) D_c=(0,2,3,7) V=(1,2)          -> part1 0, iota 0, counts 1 and 2, 0 bad of 6732
n=3 chi=(+1,-1,-1) D_c=(0,2,3,7) V=(1,)           -> part1 0, iota 0, counts 1 and 2, 0 bad of 6732
control F_2 x Z: shifts c with D_a + c = -D_a: []
CONTROL (tree from chi=(-1,+1), group law F_2 x Z): lift check: 248 bad of 1272
```

The check is finite, so it only supports Lemmas 2.1, 3.1 and 5.2 and the counts.
The proofs above do not depend on it. The control shows the lift test is not
vacuous: the automorphisms that work for the twisted group fail on the direct
product with the same decoration data.
