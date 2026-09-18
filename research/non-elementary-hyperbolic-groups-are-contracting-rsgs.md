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
