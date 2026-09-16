# One-letter models for the (2,4,6) Kac--Moody lattice (2026-09-16)

Artifact for the claim `irs-rigid-triangle-colimit-sofic-iff-one-letter-model` and its route
`irs-rigid-triangle-colimit-one-letter-model-proof`. Unreviewed. No novelty is claimed. The
theorem and its proof are in the two nodes. This file records the instance data, the standard
facts that make condition (e) concrete, the consequences for any search, and where Caprace--Remy's
no-quotient argument stops.

Script: `experiments/km-246-lattice-is-sofic-2026-09-16/one_letter_models_checks.py`
(single-threaded, seconds, output ends with `all checks passed`).

## 1. What the theorem changes in the gate

`km-246-lattice-is-sofic` records three things.
- The free-or-trivial soficity test.
- The Levi form, in which vertex actions are free off `o(d_n)` points and edges agree off `o(d_n)`.
- A *sufficient* one-stable-letter certificate.

The route proves three sharpenings for every triangle colimit satisfying (S1)-(S3).
1. *Exact freeness.* Every vertex chart can be made exactly free. Rounding (Lemma A) makes each
   chart an honest action, and padding (Lemma C) adds at most `lcm |X_ij|` points.
2. *Two exact edges.* Two of the three edge identifications can be made exact by conjugating
   whole vertex charts (Lemma B, cost controlled by (F2)). The whole defect then sits on one edge.
3. *Necessity.* The one-letter certificate is necessary as well as sufficient, with the
   explicit constants stated in the claim.

So the gate becomes a search inside one fixed virtually free group. The only approximate quantity
left is the size of one support, `|supp rho(t)|` in `K`, or equivalently the defect set `D` of
the one inexact edge.

## 2. Instance data (conditional)

**Assumptions, none read at source in this session.**
- `Lambda_q` is the colimit of the Levi triangle recorded in `km-246-lattice-is-sofic`
  (Abramenko--Muhlherr 1997, identified through Caprace--Remy).
- `L_ij = T.G_ij(q)` with `G_ij` simply connected of type `A_1 x A_1`, `C_2`, `G_2`, and
  `G_ij n T` a split torus of rank 2. The edge groups are `T.SL_2(q)`, and `T = (F_q^*)^3`.
- `Z` is the common kernel on `T` of the three simple roots. Its order is then the number of
  solutions of `v A = 0` in `(Z/(q-1))^3`, where `A = [[2,0,-1],[0,2,-1],[-2,-3,2]]` and
  `det A = -2`.

**Order formulas.**
- `|T| = (q-1)^3`.
- `[L_i : T] = q(q+1)`.
- `[L_ij : T] = |G_ij(q)|/(q-1)^2`.

**Script output, Part 1** (`L`-groups; the `X`-groups are `L/Z`).

| q | order of `L_i` | order of `L_12` | order of `L_13` | order of `L_23` | lcm of vertex orders | order of `Z` |
|---|---|---|---|---|---|---|
| 4 | 540 | 10800 | 2937600 | 754790400 | 12831436800 | 1 |
| 5 | 1920 | 57600 | 37440000 | 23436000000 | 609336000000 | 2 |
| 7 | 12096 | 677376 | 1659571200 | 3986256830976 | 199312841548800 | 2 |
| 8 | 24696 | 1778112 | 7396945920 | 30305173635072 | 1969836286279680 | 1 |
| 9 | 46080 | 4147200 | 27545702400 | 180754563225600 | 14821874184499200 | 2 |

At `q = 4`, `lcm = 2^12 . 3^4 . 5^2 . 7 . 13 . 17`.

**Relator ranks.** `r = 1 + [L_ij:T] - [L_ij:L_i] - [L_ij:L_j]` is the rank of the free kernel of
`L_i *_T L_j -> L_ij`, by (TC2) of `triangle-colimit-llp-reduces-to-relator-local-splitting`.
- At `q = 4` the three vertex values are `361`, `97921` and `25159681`.
- Given actions of the two edge groups inside a vertex group, agreeing on `T`, the vertex chart
  extends them iff the `r` free generators of this kernel act trivially (assuming the Levi
  intersection and generation facts (H1)-(H2) of that node).
- In an `epsilon`-model all three vertex charts are exact. The defect is not in these relations.
  It is in the identification of the two copies of `X_2`.

**Triangle Euler characteristic.** `chi . |T| = 1 - 3/[L_i:T] + sum 1/[L_ij:T]` is `0.852509` at
`q = 4` and increases with `q` in the table (`0.9011`, `0.9467`, `0.9585`, `0.9668`). This is the
orbifold Euler characteristic of the triangle complex of groups, times `|T|`.

## 3. Condition (e) is a statement about free subgroups (standard)

**Remark.** Let `K_0 = (X_12 *_{X_1} X_13) *_{X_3} X_23`, and let `M <= K_0` have finite index.
- `M` meets every conjugate of every vertex group trivially iff `M` is torsion-free.
- In that case `M` is free of rank `1 - [K_0:M] chi(K_0)`, where
  `chi(K_0) = 1/|X_12| + 1/|X_13| + 1/|X_23| - 1/|X_1| - 1/|X_3|`.

*Proof.* `K_0` is the fundamental group of the tree of groups
`X_12 -- X_1 -- X_13 -- X_3 -- X_23`, with injective edge maps. It acts without inversions on
the Bass--Serre tree `Y`. Vertex stabilizers are the conjugates of the `X_ij`, and edge
stabilizers are the conjugates of `X_1` and `X_3`.
- *Torsion.* A finite subgroup `F` has a finite orbit of vertices. The finite subtree they span
  is `F`-invariant, so its centre is `F`-invariant. The centre is a vertex, or the midpoint of an
  edge. There are no inversions, so in the second case `F` fixes both endpoints. So `F` lies in a
  conjugate of a vertex group, which proves the forward direction. The converse holds because the
  vertex groups are finite.
- *Freeness.* If `M` meets every vertex stabilizer trivially, then `M` acts freely on `Y`: an
  element fixing an edge fixes its endpoints. So `M` is the fundamental group of the finite graph
  `M\Y`, and is free.
- *Rank.* The `M`-orbits on vertices of type `ij` correspond to the double cosets `M k X_ij`.
  These are the orbits of `X_ij` acting on the right on the `[K_0:M]` right cosets `Mk`. The
  stabilizer of `Mk` is `X_ij n k^(-1) M k = 1`, so there are `[K_0:M]/|X_ij|` such orbits. The
  same count for edges gives `[K_0:M]/|X_e|` edges of type `e`. So `M\Y` is a finite connected
  graph with Euler characteristic `[K_0:M] chi(K_0)`. Since `M` acts freely on the tree `Y`, it
  is the fundamental group of `M\Y`, of rank `1 - [K_0:M] chi(K_0)`. QED

**Script output, Part 3** (with `|Z|` as in section 2).

| q | `chi(K_0)` | lcm of the orders of the `X_ij` | rank of `M` at index `lcm` | order of `X_2` |
|---|---|---|---|---|
| 4 | `-3.610769e-03` | 12831436800 | 46331360 | 540 |
| 5 | `-2.048558e-03` | 304668000000 | 624129950 | 960 |
| 7 | `-3.277341e-04` | 99656420774400 | 32660802902 | 6048 |
| 8 | `-8.042225e-05` | 1969836286279680 | 158418657152 | 24696 |
| 9 | `-8.632323e-05` | 7410937092249600 | 639736026030 | 23040 |

**The finite search, stated at `q = 4`** (conditional on section 2). `S_4` is sofic iff for
every `epsilon > 0` there is a torsion-free subgroup `M` of `K_0` with the following properties.
- Its index is a multiple of `12831436800` and at least `540/epsilon`.
- Its free rank is `1 + 0.003610769... [K_0:M]`.
- For all but `epsilon [K_0:M]` cosets `kM`, every `k^(-1) n_x k` with `x in X_2` lies in `M`.

For torsion-free `M`, divisibility of the index and the rank are automatic (freeness and the
Remark). The lower bound `540/epsilon` follows from the third item by (N1). So the third item is
the only condition.
Equivalently, with `N_k = k M k^(-1)`: `N_k` contains the finite set `{n_x : x in X_2}` for most
`k`. By (N2), `M` cannot be normal.

## 4. Consequences for any search

- **(N1) One orbit is enough, and the defect is spread thin.** By averaging, some orbit carries a
  defect proportion at most `epsilon`, so single-orbit models (condition (e)) lose nothing. On
  every orbit the defect set is a nonempty union of free `X_2`-orbits.
- **(N2) No uniform defect.** Whether the coset `kM` is defective depends only on whether
  `{n_x} c kMk^(-1)`. For normal `M` this is all or nothing, and "nothing" is excluded by (N1).
  So for `epsilon < 1` no finite quotient of `K_0` gives a model in its regular action. The same
  holds for any action in which the stabilizers along an orbit all contain, or all miss, the
  `n_x`.
- **(N3) The defect normally generates.** In the permutation group `Q_0 = rho_0(K_0)`, the
  elements `rho_0(n_x)` have support at most `epsilon d`, and their normal closure is all of
  `Q_0`. Every nontrivial vertex element is fixed-point free, so it needs at least `1/epsilon`
  conjugates of the `rho_0(n_x)^(+-1)`. The group `Q_0` may contain `Alt(d)`. Nothing recorded
  excludes that, and small-support elements in primitive groups push towards it (classical
  minimal-degree results of Jordan type, not re-read here).
- **(N4) Nonsoficity is a support gap.** `S_q` is not sofic iff some `epsilon_0 > 0` bounds
  `|supp rho(t)|/d` from below over all finite actions of the virtually free group `K` that are
  free on the three vertex groups.
- **Asymptotic freeness of fixed words.** Take `epsilon_n`-models with `epsilon_n -> 0` and the
  almost actions `sigma_n` of step (c) => (a) of the route, whose global fixed sets are empty.
  - By (AF2) of `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`, for every word
    `w` in the vertex groups with nontrivial image in `S`, `|Fix rho_n(w)|/d_n -> 0`.
  - In particular, if `w` has infinite order in `S`, the order of `rho_n(w)` tends to infinity:
    a bounded order `o` along a subsequence would make `rho_n(w^o) = 1`, while `w^o` is
    nontrivial in `S`.
  - No rate is available. (AF2) is a limit statement obtained from invariant random subgroups,
    so it gives no bound on the order in terms of `epsilon`.

## 5. Caprace--Remy, Theorem 15, and where its argument stops

**Source.** P.-E. Caprace and B. Remy, *Simplicity and superrigidity of twin building lattices*,
arXiv:math/0607664v2 (26 Sep 2006). Section 4.1, Theorem 15 and Corollary 16 were read
on 2026-09-16 from a local text extraction of the arXiv PDF. The extraction lost most Greek
symbols, so the root-level details below are paraphrased, not quoted.

**Statement (paraphrase).**
- *Hypotheses.* `(W,S)` is irreducible, non-spherical and non-affine, and the root groups are
  nilpotent.
- *Conclusion.* For a normal subgroup `H` such that `N/T.(N n H)` is finite, the image of the
  subgroup generated by the root groups modulo `H` is nilpotent. It is the image of the product
  of the simple root groups.
- *Corollary 16.* With finite root groups, the corollary gives the restriction on finite-index
  subgroups that the graph records as "no finite quotients for `q > 3`".

**Mechanism (paraphrase).**
- The proof sets `h = [N : T.(N n H)]`. It uses products of two reflections in disjoint roots,
  which have infinite order in `W`, with their Theorem 14 supplying a suitable second root.
- Raising such an element to the power `h` lands in `T.(N n H)`. Modulo `H` it acts like an
  element of `T`, so it identifies the images of root groups whose roots are far apart.
- Pairwise disjoint roots generate nilpotent groups (their Proposition 3(iii)). A rank-one lemma
  (their Lemma 10) then finishes the proof.

**Where it stops for models.** The step that needs a finite quotient is "`tau^h` lies in `T`
modulo `H`, for one fixed `h`". Its analogue for `epsilon_n`-models would be: for a lift `w` of
`tau` and one fixed `h`, the permutation `rho_n(w^h)` agrees with some `rho_n(s)`, `s in T`, on a
proportion of points bounded below. That fails for every fixed `h`.
- `tau^h` is not in `T`, since it maps to a nontrivial element of `W`.
- So `w^h s^(-1)` is nontrivial in `S` for every `s in T`.
- By the asymptotic-freeness item of section 4, each `rho_n(w^h s^(-1))` has `o(d_n)` fixed
  points. Since `T` is finite, the union over `s` is still `o(d_n)`.

Letting `h = h(n)` grow does not help. The identities the argument then uses are relations of `S`
that depend on `h`. By (F1), a model satisfies such a relation up to `epsilon_n` times the number
of `X_2`-edge relators needed to derive it, and that number grows with `h`. Nothing bounds it
against `1/epsilon_n`. This is the quantitative form of the entry "Quantifying Caprace--Remy's
Theorem 15" in the target's Attempts.

## 6. Unverified items

- The Abramenko--Muhlherr presentation of `Lambda_q` as the colimit of the Levi triangle (not read
  at source).
- The centre `Z` is contained in `T` and equals the common kernel of the simple roots, so the
  `|Z|` column is conditional. The instance paragraph of the claim needs only `Z <= T`.
- The Levi order formulas, which assume simply connected rank-two semisimple parts meeting `T` in
  a rank-two split torus.
- Classical minimal-degree theorems for primitive groups (only mentioned, not used).
- The standard Bass--Serre facts in section 3, for which the proofs are given in full above.
