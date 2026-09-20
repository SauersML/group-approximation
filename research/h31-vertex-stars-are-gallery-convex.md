---
rg: 2
id: h31-vertex-stars-are-gallery-convex
kind: claim
title: In the CAT(-1) triangle complex of H_31 every vertex star is convex in the chamber graph (every geodesic gallery between two chambers of star(v) stays in star(v)), equivalently every coset of a vertex group is geodesically convex in the Cayley graph for the 12 nontrivial edge-group elements; the proof is a pivot-path reduction to a link-isometry lemma (edge paths avoiding v are at least as long as the link distance), proved by combinatorial Gauss-Bonnet with angles pi/5, pi/4, pi/2; the same reduction shows the strong form of lemma G fails at C-type apexes of A-B edges
distinct_from:
  star-chains-along-fixed-trees-are-gallery-convex: that is lemma (G) for unions of stars along a geodesic edge path (the open crux); this proves the one-star case (G_star), shows the strong union form is false at C-type apexes of A-B edges, and reduces the union case to junctions between consecutive stars.
---

**ESTABLISHED (lane proof, bh-lemmaG, 2026-09-19; refereed PASS by bh-ref-d, review
`h31-vertex-stars-gallery-convex-review`, 118d2b8aa7).** Theorem S, Corollary S′ and Lemma Σ only; the
union statements below stay OPEN. No priority
claimed: this is the triangle-complex analogue of convexity of residues in buildings (Tits), proved here
without walls; a statement of this kind may be folklore for Gersten–Stallings triangles of groups.

## Setting

`X` is the CAT(−1) triangle complex of `𝓗_31` (Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276, Thm 1.2),
as used in `star-chains-along-fixed-trees-are-gallery-convex`:
- `X` is simplicial and simply connected; every triangle (chamber) has one vertex of each type `A`, `B`, `C`.
- Links: `L_A` has girth 10, `L_B` girth 8, `L_C = K_{5,5}` girth 4; all links are 5-regular bipartite.
- Angles: `α_A = π/5`, `α_B = π/4`, `α_C = π/2`, so girth × angle = `2π` at every type and every chamber
  has angle sum `19π/20`, i.e. curvature `−δ` with `δ = π/20`.
- `𝒞` is the chamber graph (chambers adjacent iff they share an edge). `𝓗_31` acts simply transitively on
  chambers, so `𝒞` is the Cayley graph for the 12 nontrivial elements of the three edge groups `⟨a⟩, ⟨b⟩, ⟨c⟩`,
  and `star(v)` is a coset of the vertex group `G_v` (`PSL_2(31)`, the group of order 625, or `C_5 × C_5`).

## Statement

**Theorem S (star convexity).** For every vertex `v`, every geodesic gallery of `𝒞` between two chambers of
`star(v)` lies in `star(v)`.

**Corollary S′.** For `g ∈ 𝓗_31` and a vertex group `G_v`, every geodesic word (in the 12 edge-group
letters) between two elements of `gG_v` uses only letters of `G_v`. In particular word length restricted to
`G_v` is the word length of `G_v` in its own 8 letters, a finite computation (14880, 625 or 25 elements).

**Lemma Σ (link isometry).** Let `v` be a vertex and `p, q` neighbours of `v`. Every edge path in
`X^{(1)} ∖ {v}` from `p` to `q` has at least `d_{L_v}(p, q)` edges.

## Proof of Theorem S from Lemma Σ (pivot paths)

Let `γ` be a geodesic gallery between chambers of `star(v)` that leaves `star(v)`. Take a maximal excursion
`D_0, D_1, …, D_k` with `D_0, D_k ∈ star(v)`, `D_1, …, D_{k−1} ∉ star(v)`, `k ≥ 2`. It is geodesic, so
`k = d_𝒞(D_0, D_k)`.
- Let `f_i = D_{i−1} ∩ D_i` (`i = 1, …, k`). For `1 ≤ i ≤ k` the edge `f_i` lies in a chamber `D_i` or
  `D_{i−1}` with index in `1..k−1`, which avoids `v`; so no `f_i` contains `v`.
- For `1 ≤ i ≤ k−1`, `f_i` and `f_{i+1}` are two edges of `D_i`, so they meet in one vertex `p_i` (the pivot).
  If `p_i ≠ p_{i+1}` then both lie on `f_{i+1}`, so `f_{i+1} = p_i p_{i+1}`.
- Deleting repetitions, the pivots give an edge path `P` from `p_1` to `p_{k−1}` avoiding `v`, with at most
  `k − 2` edges (there are `k − 1` pivots).
- `p_1 ∈ f_1 ⊂ D_0` and `p_{k−1} ∈ f_k ⊂ D_k`, and both are neighbours of `v`. Going around `v` along a
  shortest path `p_1 = t_0, …, t_d = p_{k−1}` in `L_v` gives the gallery
  `D_0, (v,t_0,t_1), …, (v,t_{d−1},t_d), D_k` (consecutive chambers share an edge through `v`), so
  `d_𝒞(D_0, D_k) ≤ d + 1`, where `d = d_{L_v}(p_1, p_{k−1})`.
- Lemma Σ gives `k − 2 ≥ |P| ≥ d`, so `k ≥ d + 2 > d + 1 ≥ d_𝒞(D_0, D_k) = k`. Contradiction. ∎

## Proof of Lemma Σ (combinatorial Gauss–Bonnet)

Suppose `p ≠ q` and let `P = (z_0 = p, z_1, …, z_m = q)` be a shortest edge path from `p` to `q` avoiding `v`.
The loop `Z = v, p, P, q, v` is a simple cycle (P is a shortest path avoiding `v`). Among all such `P` and all
disc diagrams for `Z` choose one, `Δ`, of minimal area `F`. Then `Δ` is a reduced disc; each interior vertex has
a non-backtracking closed link walk, so its angle sum is at least girth × angle `= 2π`.

Two standard facts are used (stated at the referee's request): a minimal-area disc diagram for a simple
cycle is a nonsingular disc, and each piece of `Δ′` below is a disc.

**Facts about `Δ`.**
1. *Fan at `v`.* The faces at `v` form a fan `(v, s_{j−1}, s_j)`, `j = 1..N`, with `s_0 = p`, `s_N = q`, and
   `N ≥ d_{L_v}(p, q)` (the fan is a walk in `L_v` from `p` to `q`). Let `Q = (s_0, …, s_N)`.
2. *Interior vertices of `P` carry at least three corners.* One corner at `z_i` means the face
   `(z_{i−1}, z_i, z_{i+1})`, and the edge `z_{i−1}z_{i+1}` shortens `P` while avoiding `v`. Two corners with
   middle vertex `s ≠ v` means faces `(z_{i−1},z_i,s), (z_i,z_{i+1},s)`; then `s ∉ P` (else `P` would have a
   shortcut) and `s` is interior, so replacing `z_i` by `s` keeps `|P|` and lowers the area by 2, against
   minimality. If the middle vertex is `v`, then `z_{i−1}, z_i, z_{i+1}` lie on `Q` (a touching point, below).
3. *Pieces.* Remove the fan. What is left, `Δ′`, has boundary `P` followed by `Q` reversed. Cut `Δ′` at the
   vertices where `P` meets `Q`; the pieces are discs (or single shared edges) whose boundary is a segment
   `z_a…z_b` of `P` and a segment `s_c…s_e` of `Q` with the same endpoints, meeting only there. It suffices to
   show `b − a ≥ e − c` for every piece; summing gives `m ≥ N ≥ d_{L_v}(p, q)`. Shared edges give equality.

**Curvature in a disc piece `Π`** (units of `π`; `κ(u) = 1 − θ(u)/π` at boundary vertices). Gauss–Bonnet:
`Σ_{∂Π} κ + Σ_{int} κ = 2 + F_Π/20`, and interior vertices have `κ ≤ 0`, so `Σ_{∂Π} κ ≥ 2 + F_Π/20`.
Write `M = e − c` (the `Q`-side has `M` edges) and `m′ = b − a`.
- *`Q`-side interior vertices* `s` are interior vertices of `Δ` (they are not on `P` and not `v`), so their
  angle in `Δ` is at least `2π`, of which the fan used two corners: `κ_Π(s) ≤ 2α_s/π − 1`, which is
  `−3/5` (A), `−1/2` (B), `0` (C). Such an `s` also carries at least `g_s − 2` faces of `Π`: 8 (A), 6 (B), 2 (C).
- *`P`-side interior vertices* `z` keep all their corners (none contains `v`), so by Fact 2
  `κ_Π(z) ≤ 1 − 3α_z/π`: `2/5` (A), `1/4` (B), `−1/2` (C). Adjacent vertices have different types, so a
  `P`-segment with `r` interior vertices has `Σ κ ≤ S(r) = 0.4⌈r/2⌉ + 0.25⌊r/2⌋`.
- *The two endpoints* are neighbours of `v`, carry at least one face of `Π`, so `κ ≤ 1 − α/π ≤ 4/5`.
- The `Q`-side vertices alternate between the two types other than the type of `v`.

Suppose `m′ ≤ M − 1` (so the `P`-side has at most `M − 2` interior vertices).
- **`v` of type `A`** (`Q` alternates `B, C`). Let `β ≥ ⌊(M−1)/2⌋` be the number of `B`-type interior
  `Q`-vertices. Faces at distinct `B`-vertices are distinct (a face has one `B`-vertex), so `F_Π ≥ 6β`.
  Endpoints are `B`/`C`, so `κ ≤ 3/4` each. Gauss–Bonnet gives `1.5 + S(M−2) − 0.5β ≥ 2 + 0.3β`, i.e.
  `S(M−2) ≥ 0.5 + 0.8β`. For `M − 2 = 2t`: `0.65t ≥ 0.5 + 0.8t`, false. For `M − 2 = 2t+1`:
  `0.65t + 0.4 ≥ 0.5 + 0.8(t+1)`, false.
- **`v` of type `B`** (`Q` alternates `A, C`). With `a ≥ ⌊(M−1)/2⌋` interior `A`-vertices, `F_Π ≥ 8a`,
  endpoints `≤ 4/5`: `1.6 + S(M−2) − 0.6a ≥ 2 + 0.4a`, i.e. `S(M−2) ≥ 0.4 + a`; false in both parities.
- **`v` of type `C`** (`Q` alternates `A, B`, all interior `Q`-vertices negative). With `a + β = M − 1`,
  `F_Π ≥ 4a + 3β` (a face holds at most one `A`- and one `B`-vertex): `S(M−2) ≥ 0.4 + 0.8a + 0.65β`, false.

So `m′ ≥ M` on every piece, hence `m ≥ N ≥ d_{L_v}(p,q)`. ∎

(`M ≤ 2` is covered by the same count; `M = 2, m′ = 1` is also impossible directly, since `s_c, s_e` have
the same type and cannot be adjacent.)

## Consequences for lemma (G) (`star-chains-along-fixed-trees-are-gallery-convex`)

Let `ρ = (w_0, …, w_n)` be a geodesic edge path and `U_ρ = ⋃ star(w_i)`.

1. **No excursion returns to the same star.** A geodesic gallery between chambers of `U_ρ` whose maximal
   excursion outside `U_ρ` starts and ends in the same `star(w_i)` contradicts Theorem S. So every
   excursion runs from `star(w_i)` to `star(w_j)` with `i ≠ j`, and its pivot path avoids all of `V(ρ)`.
2. **The strong form of (G) is false at every `A`–`B` edge.** Let `w_i w_{i+1}` be an `A`–`B` edge of `ρ` and
   `u` a `C`-type apex, so `(u, w_i, w_{i+1})` is a chamber and `L_u = K_{5,5}`. Choose a `B`-neighbour
   `x_c ≠ w_{i+1}` and an `A`-neighbour `x_d ≠ w_i` of `u`, both off `ρ`. Such choices exist: `u ∉ ρ`, since a
   geodesic edge path never contains three vertices of one chamber (the angle at the middle one would be below
   `π`); and `ρ ∩ star(u)` is a geodesic segment of length at most `diam star(u) ≤ 2·0.63 < 1.3`, while edges have
   length at least `0.53`, so at most two `ρ`-vertices besides `w_i, w_{i+1}` lie in `star(u)`, leaving at least
   two of the four candidates on each side. Then `T_1 = (u, w_i, x_c)` and `T_2 = (u, x_d, w_{i+1})` lie in
   `U_ρ`, share only `u`, and are joined by
   the two galleries `T_1, (u, w_i, w_{i+1}), T_2` (inside) and `T_1, (u, x_d, x_c), T_2` (outside). Both have
   length `2 = d_𝒞(T_1, T_2)`, and `(u, x_d, x_c)` contains no `ρ`-vertex. So a geodesic gallery leaves `U_ρ`.
   This is the gallery form of bh-ref-d's `K_{5,5}` counterexample to G0 (15b37f96f8). The weak form
   (`U_ρ` isometrically embedded, i.e. *some* geodesic stays inside) holds in this configuration.
3. **Where the union case can fail (sketch).** Run the Lemma Σ argument for a pivot path from `N(w_i)` to
   `N(w_j)` avoiding `V(ρ)`, removing the fans at all `ρ`-vertices. A `Q`-side vertex `s` then loses `c_s`
   corners and has `κ ≤ c_s α_s/π − 1`. Using that `ρ` is a CAT(0) geodesic (angle `≥ π` at each `w_l`, unique
   geodesics), a case check gives `c_s ≤ 4` for types `A, B` (so `κ ≤ 0`) and `c_s ≤ 3` for type `C`, with
   `c_s = 3` exactly at `C`-type apexes of `A`–`B` edges (`κ = +1/2`). So the only positive curvature on the
   inner side sits at those apexes, matching item 2. This case check is a sketch, not a proof.
4. **The corrected target.** What is still needed is not (G) as stated but one of:
   - **(G_w)** `U_ρ` is isometrically embedded in `𝒞` (every pair of its chambers has *some* geodesic gallery
     inside `U_ρ`); or
   - **(G⁺)** `U⁺_ρ = U_ρ ∪ ⋃ star(u)`, over the `C`-type apexes `u` of the `A`–`B` edges of `ρ` (5 per edge,
     25 chambers each), is convex in the strong sense.

   Either would make the event computation exact. What is missing is the junction count: an excursion from
   `star(w_i)` to `star(w_j)` must be compared with the in-union gallery, whose length is (fan faces) + 1,
   i.e. `|Q| + (j − i) + 1`. Lemma Σ's surplus (`m ≥ 1.2 N` roughly, from the face term) suggests the apex
   terms `j − i` are absorbed, but this is not proved.

## What this gives now

- Exact gallery distances inside any single star (Corollary S′), and the fact that no geodesic gallery
  between chambers of `U_ρ` ever leaves and re-enters the same star.
- The periodic model of the crux node needs (G_w) or (G⁺); its size is essentially unchanged by the apex
  thickening (see the (G⁺) attempt below). Nothing was computed.

## Attempt on (G⁺): the junction count (bh-lemmaG, 2026-09-19; OPEN)

Set `V⁺ = V(ρ) ∪ {C-type apexes of A–B edges of ρ}` and `U⁺_ρ = ⋃_{v∈V⁺} star(v)`. Take an excursion
`D_0 … D_k` from `star(w_i)` to `star(w_j)` (`i < j`, by Theorem S) avoiding `V⁺`, its pivot path `P`, and a
minimal diagram `Δ` for the loop `w_i, p, P, q, w_j, w_{j−1}, …, w_i`. Its faces at `w_l` form fans of `N_l`
faces; consecutive fans share exactly the face on `w_l w_{l+1}` (non-consecutive `ρ`-vertices are never
adjacent, by uniqueness of geodesics). The fans give an in-`U_ρ` gallery `D_0 → D_k` of length
`Σ_l N_l − (j − i) + 1`, so strong convexity follows from `k > Σ_l N_l − (j − i) + 1`.

1. **The one-star count does not extend (checked).** Using only `k ≥ |P| + 2`, one needs
   `|P| ≥ |Q′| + (j − i)`, with `Q′` the outer boundary of the fans. In the tight `A–C` periodic chain
   (`N_A = 6`, `N_C = 2`), per period the `Q′`-side offers curvature plus face budget `≈ 1.0π`, while a `P`
   one edge too short can still carry `≈ 1.6π` of positive curvature. So no contradiction arises; the extra
   `+1` per junction is what breaks the Lemma Σ argument.
2. **The missing coupling: excursion length.** Counting chambers at pivots gives exactly
   `k − 1 = Σ_{z∈P} e_z − |P|`, where `e_z` is the number of excursion chambers at `z`. Assuming the combined
   link walk at each pivot is non-backtracking (NB, not proved), `e_z ≥ g_z − c_z` at interior pivots and
   `e_z ≥ g_z − c_z − 1` at the two ends (`D_0`, `D_k` also contain them; `−2` if `P` is one vertex), with
   `c_z` the corners of `Δ` at `z`. So a positively curved `P` makes the excursion long.
   - Tight `A–C` chain with `P = Q′`: per period the excursion costs `14 − 4 = 10` against the in-union `6`.
   - One-pivot excursions: a `B`- or `A`-type apex pivot gives `k ≥ 6` or `8` against in-union `2`. A `C`-type
     pivot next to two `ρ`-vertices must be adjacent to consecutive ones (geodesic uniqueness and
     `|BC| < |AC| < |AB|`), i.e. is an apex of an `A–B` edge, which `V⁺` excludes. This assumes `X` is flag
     (every 3-cycle bounds a chamber), which was not checked. It matches the counterexample: only `g = 4`
     pivots are cheap.
3. **Still open for (G⁺).**
   - (NB) at pivots, or a replacement.
   - The general inequality `Σ_{z∈P}(g_z − c_z − 1) ≥ Σ_l N_l − (j − i)`, which must be combined with
     Gauss–Bonnet even though the weights `1/α_z` differ by type.
   - Excursions that start or end in an apex star.
   - Flagness of `X`.
4. **Size of the computation if (G⁺) holds.** Each apex star adds 16 chambers not already in `U_ρ` (25 minus
   the 9 through `w_i` or `w_{i+1}`), so 80 per `A–B` edge. A period `A–B` of a ray of `Fix(a)` then has about
   `14880 + 625 + 160 ≈ 1.57·10⁴` chambers, and six periods about `10⁵`, as before (the apex thickening adds
   about 1%). The BBMZ window thickening at the front, from the crux node, is still needed. Events (A)/(B) and
   the fiber question stay finite periodic computations. Not run.
