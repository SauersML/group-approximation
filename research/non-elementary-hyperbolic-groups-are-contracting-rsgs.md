---
rg: 2
id: non-elementary-hyperbolic-groups-are-contracting-rsgs
kind: claim
title: Every non-elementary hyperbolic group is isomorphic to a contracting rational similarity group (BBMZ-hyperbolic Question 1.1)
distinct_from:
  hyperbolic-groups-embed-in-contracting-rsgs: that is the established embedding of every hyperbolic group into a contracting RSG; this asks for an isomorphism with no free factor added.
  free-products-with-a-finite-factor-are-contracting-rsgs: that is the case of a finite free factor, established; this is the whole question.
  free-products-of-hyperbolic-groups-are-contracting-rsgs: that is the freely decomposable case, established; this is the whole question.
  virtually-free-product-hyperbolic-groups-are-contracting-rsgs: that is the virtually freely decomposable case, established; this is the whole question.
  sft-irreducible-core-iff-unique-recurrent-component: that is the graph-theoretic form of obstacle (ii), established; this is the whole question.
  surface-group-atoms-are-wall-arrangement-cells: that computes the atoms of closed surface groups and verifies every BBMZ hypothesis except the irreducible core; this is the whole question.
  virtually-free-groups-are-contracting-rsgs: that is a second proof of the virtually free case, with trivial nucleus; this is the whole question.
  contracting-rsgs-closed-under-products-with-finite-groups: that is a closure lemma used for the known cases; this is the question itself.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**OPEN.** This is Question 1.1 of Belk--Bleak--Matucci--Zaremsky, *Hyperbolic groups satisfy
the Boone--Higman conjecture*, arXiv:2309.06224v3 (§1, `ssec:open`, read in the TeX):
"Is every non-elementary hyperbolic group isomorphic to a contracting RSG?"

## Known cases (on main)

- **`G * Z`** for every hyperbolic `G` (BBMZ `thrm:FreeProductBoundary` together with
  `thrm:contracting`; BBMZ state this as "if `G` has `Z` as a proper free factor then the RSG
  is contracting").
- **`A * B`** for any two nontrivial hyperbolic groups, not both of order 2:
  `free-products-of-hyperbolic-groups-are-contracting-rsgs`, a lane proof. It generalizes
  both the `G * Z` case and the finite-factor case
  `free-products-with-a-finite-factor-are-contracting-rsgs`. So every freely decomposable
  non-elementary hyperbolic group is covered.
- **Finite-index overgroups** of any of the above:
  `contracting-rsgs-closed-under-finite-index-overgroups`, a lane proof (induced action). In
  particular `virtually-free-product-hyperbolic-groups-are-contracting-rsgs`: every
  non-elementary virtually free group, such as `SL_2(Z)` and `GL_2(Z)`, and every virtually
  torsion-free hyperbolic group with infinitely many ends. Direct products with finite groups,
  such as `F_2 × Z/2`, are the special case `contracting-rsgs-closed-under-products-with-finite-groups`.
  For virtually free groups there is also a second, elementary proof with trivial nucleus
  (`G ≤ V_{Γ,E}`): `virtually-free-groups-are-contracting-rsgs`, by a Bass--Serre normal-form
  coding.

## What remains

By the finite-index closure, `G` is covered as soon as one finite-index subgroup is. What
remains:
- **one-ended hyperbolic groups** (closed surface groups, closed hyperbolic 3-manifold groups,
  Kazhdan hyperbolic groups), where no finite-index subgroup splits freely; and
- **infinitely-ended hyperbolic groups none of whose finite-index subgroups splits freely.** Any
  such group is not virtually torsion-free, and whether such hyperbolic groups exist is open.

## Attempts

1. **2026-09-18 (lane `bh-free-23`).** The two BBMZ obstacles, re-examined.
   - (i) Finite normal subgroups: not intrinsic. Contracting RSGs can have nontrivial finite
     centers (`V_{Γ,E} × Z/2`). For direct products `H × N` with `N` finite, relabelled copies
     of the address space realize `N` faithfully. For a generating set not closed under `N`,
     even the horofunction boundary can see `N`. For example, `F_2 × Z/2` with generating set
     `{a, b, c}` has `∂_h ≅ ∂F_2 × {0,1}`, and `c` swaps the two copies.
   - (ii) Irreducible core: for every free splitting `A * B`, the shadows of points just past
     a syllable change have a single type, and translating a factor branch into such a shadow
     copies every atom type (`free-products-of-hyperbolic-groups-are-contracting-rsgs`). So
     obstacle (ii) disappears for all freely decomposable groups. For one-ended groups there is
     no cut vertex, and a new mechanism is needed.
   - A proposal, not attempted: for a finite normal subgroup `N` that is not a direct factor,
     look for a continuous `N`-valued cocycle on the germ groupoid of `G/N ↷ ∂_h(G/N)` that
     realizes the extension. `G` would then act on `∂_h(G/N) × N` by a skew product, and the
     finite-product construction would apply to that skew product.
2. **2026-09-18 (lane `bh-free-23`), the one-ended case.**
   - **Reduction.** By `contracting-rsgs-closed-under-finite-index-overgroups`, it is enough to
     realize one finite-index subgroup. For closed surface groups every finite-index subgroup is
     again a closed surface group, so a genuinely one-ended mechanism is needed.
   - **Markov codings already give RSG moves.** Let a Fuchsian group `Γ` act on `S^1` with a
     Bowen--Series-type Markov map `T`, such that `T|_{I_a} = g_a ∈ Γ` on each Markov interval.
     Blow up a countable invariant set to get a Cantor model, and code points by their
     `T`-itineraries. Then `T^{|α|}` restricted to the cylinder `C_α` is one group element `g_α`,
     and `g_α(αω) = ω`. So `g_β^{-1} g_α` maps `C_α` onto `C_β` by the canonical similarity
     whenever `t(α) = t(β)`. That is the RSG condition, with no hyperbolic-group geometry.
   - **What is unverified:**
     - rationality of the generators at the blown-up points;
     - finiteness of the nucleus (the analogue of the BBMZ contracting lemma);
     - irreducibility of the transition graph, which is expected from topological mixing of the
       Bowen--Series map.

     Bowen--Series (Publ. IHES 50, 1979) was not read at source. The nucleus cannot consist only
     of identity maps unless the surface group embeds in `V_{Γ,E}`, which is not known (compare
     survey Question 4.7). So a proof should expect to control non-identity local actions
     `g_β s g_α^{-1}`.
3. **2026-09-18 (lane `bh-free-23`), what the one-ended case requires.**
   - **Reformulation (proved).** By `sft-irreducible-core-iff-unique-recurrent-component`, for
     a hyperbolic `G` with `∂_h G` without isolated points, obstacle (ii) says exactly this: the
     atom-type graph has a single strongly connected component containing a cycle. Such a
     component is then automatically a sink and not a single cycle.
   - **Recurrent components come with loxodromics (proved, elementary).** Let `c` be a cycle
     at a node `v` of a recurrent component `S`, and let `C_α` be a proper cone of type `v`.
     The RSG property gives `h ∈ G` mapping `C_{αc}` onto `C_α` by the canonical similarity.
     Then `h^{-1}(αω) = αcω`, so `h` has infinite order. Its attracting fixed point `αc^∞` has
     its tail in `S`. So a second recurrent component would be carried by a second family of
     loxodromic elements whose attracting rays can never pass into the first component.
   - **Missing geometric input.** Exact agreement of distance germs. By BBMZ
     `prop:MakeMorphisms`, `g` is a morphism from an atom `A` to an atom `A'` as soon as `g`
     carries the finite entrance data of `A` onto that of `A'`: `N̂(A)`, the profile of `d_A`
     on it, and the cone types there. That holds, for example, when `d(·,1) − d(·,g)` is
     exactly constant on a ball of radius `R(δ)` around the relevant points, and `1`, `gx`,
     `gz` are aligned.
   - **Target.** Uniqueness of the recurrent component would follow from this: for any two
     entrance configurations that recur along geodesic rays, some `g` exists with this exact
     germ agreement at a point deep inside the first configuration's subtree. In free products
     the cut vertices supply such `g`. For one-ended groups this exact-gate property is the
     open point.
4. **2026-09-18 (lane `bh-free-52`), splittings over finite subgroups without a cut vertex.**
   - **Virtually free groups, directly.** Code the ends of the Bass--Serre tree by
     left-normalized normal forms `g_0 e_1 s_1 e_2 s_2 ⋯`, keeping the vertex-group head `g_0`.
     Left multiplication is then a prefix replacement, and `β̂ α̂^{-1}` matches same-type cones.
     Minimal non-elementary tree dynamics give the irreducible core. The nucleus is trivial.
     A finite normal subgroup `N` fixes the tree pointwise and acts on the head, so it acts
     faithfully even when it does not split. With the standard generating set, the center of
     `SL_2(Z)` acts trivially on `∂_h`. See `virtually-free-groups-are-contracting-rsgs`.
   - **Gates in the horofunction picture (not landed as a result).** For `A *_C B` with `C`
     finite, a coset `yC` separates the Cayley graph. It plays the role of the cut vertex of
     `free-products-of-hyperbolic-groups-are-contracting-rsgs`, and the following holds:
     - **Gate lemma.** Let `n` be large enough that `yC` and its far-side neighbours lie in
       `B_n`. Then atoms of level `n` do not straddle `yC`. An atom beyond `yC` is determined
       by its profile on `B_n ∩ (D_{yC} ∪ yC)`. So `y'y^{-1}` is a morphism between atoms
       beyond `yC` and beyond `y'C` when both gates have the same side and the same incoming
       profile `c ↦ |yc| − min_{c'} |yc'|`.
     - **The obstruction.** The copying step (`lem:atoms_in_atoms`) needs a gate whose
       incoming profile equals that of the base gate `C`, namely `c ↦ |c|`. That means a point
       `u ∉ C` with `d(u, c) = d(u, 1) + |c|` for all `c ∈ C`. In `SL_2(Z)` no such `u` exists:
       `z` is central, and it is absorbed into any syllable (`az = a^{-1}`, `bz = b^{-2}`), so
       `|zw| ≤ |w| + 1 < |w| + |z|` for all `w ≠ 1`. This is the same mechanism that makes `z`
       act trivially.
   - **What is left for the infinitely-ended case.** Graphs of groups with finite edge groups
     and infinite vertex groups, none of whose finite-index subgroups splits freely. The
     normal-form coding would need an infinite alphabet at the infinite vertex groups. The
     gate approach needs the incoming profiles to recur, together with a separate faithful
     treatment of the finite radical.
5. **2026-09-18 (lane `bh-free-23`), closed surface groups made explicit.**
   - **Landed (`surface-group-atoms-are-wall-arrangement-cells`).** With the regular `4g`-gon
     generators:
     - word length counts the separating tiling walls;
     - the atoms of `B_n` are the unbounded cells of the finite arrangement `𝒲_n`;
     - `∂_h` has no isolated points, so the BBMZ image is an RSG with finite nucleus;
     - no cell is a half-plane, because every wall of `𝒲_n` is crossed by another wall of `𝒲_n`
       (corrected: the first landing stated a gate lemma that turned out to be vacuous).
   - **Remaining.** A single recurrent type component. Atoms near the ideal boundary are bounded
     by at least two crossing walls, so the open step concerns sector cells at tiling vertices.
   - **Comparison with Attempt 4.** The coset gates of Attempt 4 need a separating finite set.
     One-ended groups have none, and here that shows up concretely: no cell is cut off by a single
     wall.
6. **2026-09-18 (lane `bh-partials`), the one-ended case through the Bowen–Series coding.**
   - **The new node.** `closed-surface-groups-are-contracting-rsgs`, with route
     `closed-surface-groups-contracting-rsg-via-bowen-series` (OPEN).
   - **Proved there from Katok–Ugarcovici (arXiv:1610.00167), read at source.** The Bowen–Series map of the right-angled
     `(8g−4)`-gon gives an explicit SFT on `2(8g−4)` arc states. Canonical similarities are group elements `g_{w'}^{-1}g_w`
     (Attempt 2's observation). Exactness of the map makes the graph primitive. So the irreducible core, the obstacle of
     Attempts 3 and 5, is automatic in this coding.
   - **Still open there.**
     - `Γ`-invariance of the cut set (the wall endpoints must all reach `Π`);
     - a finite nucleus, via a bounded level defect under generators. This is the same shape of lemma as step 3 of
       `pisot-stein-groups-are-contracting-rsgs-proof`.
   - **Lesson.** The irreducible core belongs to the coding, not to the group. Question 1.1 is now a contraction question.
7. **2026-09-18 (lane `bh-partials`), the closed-surface case is settled (lane proof, not reviewed).**
   - `closed-surface-groups-are-contracting-rsgs` is now ESTABLISHED through its Bowen–Series route.
   - **Step 4.** `Γ` acts on the Cantorized circle. This follows from Bowen–Series Lemma 2.4, read at source: orbit
     equivalence except the pairs `(Q_i, g_{i−1}Q_i)`, which lie in `Π`.
   - **Step 5.** The nucleus is finite. Itineraries are directed geodesic tile rays. The level of a cut point equals the
     time its ray enters the carrier of its wall. Fellow travelling then matches the level defect to the Busemann shift.
   - **Coverage.** This covers every closed hyperbolic surface group and every cocompact Fuchsian group.
   - **What remains of Question 1.1.** One-ended groups without a Bowen–Series-type coding (3-manifold groups, Kazhdan
     groups), and infinitely-ended groups that are not virtually torsion-free.
8. **2026-09-18 (lane `bh-partials`), right-angled 3-dimensional reflection groups and their commensurability classes
   (lane proof, not reviewed).**
   - `right-angled-reflection-groups-in-h3-are-contracting-rsgs` covers:
     - the right-angled dodecahedral reflection group `W`;
     - every finite-index subgroup of `W`, including closed hyperbolic 3-manifold groups;
     - every group commensurable with `W`;
     - more generally, every compact right-angled polyhedron satisfying three face-graph conditions.
   - **The coding.** The greedy map "reflect in the smallest-labelled separating face plane" on the Roller boundary,
     with states the cells of one tile's face-circle arrangement, refined by cosets for subgroups.
   - **What remains for 3-manifold groups.** Commensurability classes without right-angled reflection groups. There the
     walls are only quasiconvex (Bergeron–Wise), so a "quasiconvex greedy coding" is the missing tool.
9. **2026-09-19 (lane `bh-partials`), all hyperbolic right-angled Coxeter groups with spread nerves (lane proof, not
   reviewed).**
   - **Landed.** `hyperbolic-racgs-with-spread-nerves-are-contracting-rsgs`, and the fully written proof of
     `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs` (heights over carriers, injectivity, the map to `∂G`,
     and the finite nucleus with the surface referee's repairs).
   - **Coverage.** Let `W_L` be hyperbolic with `|S| ≥ 3`, suppose no simplex's vertex stars cover `L`, and suppose the
     complement graph is connected. Then `W_L` is a contracting RSG. With an odd cycle in the complement graph, so is
     every group commensurable with `W_L`.
   - **Consequences.** This reproves the surface case (pentagon group) and contains the H³ right-angled case.
   - **(NA) comes from Coxeter theory.** Disjoint walls cannot share an infinite stabilizer, because the product of the
     two reflections translates the walls.
   - **What remains for cubulated groups.** Groups that are only virtually special, i.e. quasiconvex subgroups of RACGs
     such as generic hyperbolic 3-manifold groups. Contracting RSGs pass to finite-index overgroups, not to subgroups,
     and for their own cubulations (NA) and (IRR) are open.
10. **2026-09-19 (lane `bh-partials`), finite-index subgroups and quasiconvex subgroups (lane proofs, not reviewed).**
   - **Finite-index subgroups.** `contracting-rsgs-pass-to-finite-index-subgroups-via-loops`. Coset
     refinement makes every finite-index subgroup of a contracting RSG an RSG with finite nucleus. It is contracting iff
     the loop group of the coding acts transitively on the reachable cosets, for example when the loop labels generate
     `G`. For hyperbolic RACGs with spread nerves the loop labels always generate `W`, so the old condition (c) is
     dropped.
   - **Why this does not give Agol ⇒ Question 1.1.** Virtual specialness gives a quasiconvex, infinite-index embedding
     into a right-angled Artin or Coxeter group, usually a non-hyperbolic one. Closure under finite-index subgroups does
     not cover that.
   - **Quasiconvex subgroups.** `convex-cores-inherit-greedy-coding-na`: (NA) passes from any (NA) cubulation to the
     convex core of a quasiconvex subgroup, by Helly. So quasiconvex subgroups of hyperbolic RACGs need only (IRR).
   - **Open.** (NA) for a general hyperbolic 3-manifold group's own cubulation (parallel surfaces with commensurable
     stabilizers). Also (IRR) for convex cores.
11. **2026-09-19 (lane `bh-q11-beyond`), every hyperbolic right-angled Coxeter group (lane proof, not reviewed).**
   - **Landed.** `hyperbolic-racgs-are-contracting-rsgs`, via `hyperbolic-racgs-contracting-rsg-via-min-star-order`.
     Every non-elementary hyperbolic RACG, and every group commensurable with one, is a contracting RSG. The spread
     condition (a) and the connectivity condition (b) of attempt 9 are dropped.
   - **Mechanism.** Split off cone vertices, which form a finite direct factor. Then order the generators as
     `u_1 < S ∖ St(u_1) < lk(u_1)`, where `St(u_1)` is inclusion-minimal. A no-square lemma shows every simplex is
     reachable from a singleton, so the greedy state graph is strongly connected.
   - **Lesson.** (IRR) depends on the order. A bad order on a hexagon-disk nerve gives a second recurrent component.
   - **What remains.** Non-right-angled hyperbolic Coxeter groups (via Niblo–Reeves cubulations), virtually special
     groups not commensurable with a RACG, and Kazhdan groups.
12. **2026-09-19 (lane `bh-q11-beyond`), where right-angledness enters, and the Niblo–Reeves plan (analysis, no new
   theorem).**
   - **Right-angled only through the Davis cube complex.** Attempt 11 uses right angles in three places, all in the cube
     structure:
     - vertex links are the nerve `L`, so the states are the simplices of `L`;
     - Tits' commuting-letter criterion for reduced words and left descents;
     - wall transport in the transition rule: the edge labelled `t` at `s_0` lies on `H_t` because `s_0ts_0 = t`.
   - **What is combinatorial.** The rest is nerve combinatorics and carries over to any cubulation whose state graph can
     be computed:
     - the cone splitting, whose general form splits off the finite irreducible components, since a hyperbolic `W` has at
       most one infinite component;
     - Lemma K;
     - the reachability induction.
   - **Hexagon disk, rechecked.** The example of attempt 11 checks out by hand: 8 vertices, 15 edges and 8 triangles; a flag
     disk with hexagonal boundary; no induced square; one-ended; `{a,b}` not spread; `St(y_1)` inclusion-minimal.
     - An explicit path under the good order is `{c_2} → {y_1,c_1} → {x_1,c_1} → {y_1,a,c_1} → {a,b,c_1}`.
     - Under the bad order, the only predecessor of each of `{a,b,c_1}` and `{a,b,c_2}` is the other one. The 2-cycle is an
       extra strongly connected component with a cycle. It is not a sink, since it leaks to `{a,b}`.
   - **Niblo–Reeves for non-right-angled hyperbolic `W`.**
     - **What transfers.** The cube complex is cocompact when `W` has no affine reflection subgroup of rank `≥ 3`
       (Caprace–Mühlherr, recalled), which holds for hyperbolic `W`. Hyperplanes are the walls of `W`, so the (NA) argument
       of the spread-nerve proof, Step 1, carries over verbatim.
     - **The blocker.** The vertex action is not free. For `m_{st} = 3` the three pairwise crossing walls of `⟨s,t⟩`
       span a 3-cube with two non-chamber vertices fixed by the rotation `st`. So no `W`-equivariant edge order exists at
       those vertices.
     - **Route.** Pass to a torsion-free finite-index `Γ` (Selberg), which acts freely, and finish with
       `contracting-rsgs-closed-under-finite-index-overgroups`. The state graph then has `Γ`-orbits of chamber and
       non-chamber vertices as states. Its (IRR) is a covering question over a "`W`-state graph modulo stabilizers", which
       is not yet defined.
     - **Next step.** Compute the Niblo–Reeves state graph for one compact non-right-angled Coxeter polyhedron in `H³`
       that is not commensurable with a right-angled one. Only then attempt a general (IRR) argument.
