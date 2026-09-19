---
rg: 2
id: special-cube-complex-groups-lie-in-fp-members-of-class-c
kind: claim
title: Groups with median Cayley graphs (RAAGs, RACGs, Z^n, F_n and their products) and closed surface groups lie in the class 𝒞 of groups with a quantum-rigid SFT compactification, so every compact special group lies in a finitely presented member of 𝒞 and in a finitely presented group carrying a minimal topologically free quantum-rigid SFT (gates E1′ and E2, the CARRIER of the minimal route), and every virtually compact special group, including cubulated hyperbolic and hyperbolic 3-manifold groups, has a finite-index subgroup that does
distinct_from:
  wall-chamber-distance-sfts-are-quantum-rigid: that proves quantum rigidity on chamber graphs whose distance counts walls; this assembles it with the Roller SFT, tree gluing, Haglund–Wise and Agol into the carrier statement for special groups, and records what it gives toward Boone–Higman.
  roller-compactifications-of-cube-complexes-are-quantum-rigid: that proves rigidity of the Roller SFT for every free cocompact cube action, an independent proof of the rigidity input; this uses the vertex-transitive case, where the Roller SFT is an SFT compactification, to get membership in 𝒞 and the carrier.
  tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts: that is the gluing theorem; this applies it to RAAGs, where the glued SFT is the Roller boundary of another RAAG.
  virtually-torsion-free-cubulated-groups-satisfy-boone-higman: that is Boone–Higman for cubulated groups, already known for virtually special ones through linearity over Z; this is the rigid-seed carrier (E1′ + E2), which does not by itself give Boone–Higman and gives no new instance of it.
  decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts: that is the open premise for every decidable group; this proves it for compact special groups.
---

**ESTABLISHED** (assembly by lane bh-ref-hl, 2026-09-19). Every lane input below was refereed PASS by
bh-ref-hl, and the published inputs are cited on main or marked as recalled. The node adds no new
mathematics except the Remark, which is not used in the proof. No priority is claimed.

## Setting

- **The class 𝒞.** 𝒞 is as in `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`. A group `Λ` is in 𝒞 if it carries an
  SFT `Y` with a seed `π` such that:
  - (C1) the seed isolates one point `y_*`, with trivial stabilizer;
  - (C2) the orbit of `y_*` is dense;
  - `Y` is `D`-quantum rigid over every field for all large `D`, with (Q1)–(Q3) as in
    `fp-v-times-subshift-full-groups-force-quantum-rigidity`.
- **Median Cayley graphs.** A finite symmetric `S ⊆ Γ` gives a *median Cayley graph* if `Cay(Γ,S)` is the 1-skeleton of a locally
  finite CAT(0) cube complex. Equivalently, `Γ` acts simply transitively on the vertices and `S` is the set of edge labels.
- **Special groups.** A *compact special group* is `π_1` of a compact special cube complex (Haglund–Wise). It is *virtually compact
  special* if it has a finite-index subgroup of this kind.

## Theorem

1. **Median Cayley graphs.** If `Cay(Γ,S)` is median, then `Γ ∈ 𝒞` through its distance-gradient SFT `Y_R` for any `R ≥ 6`, with seed
   `∇d(·,1)`. This SFT is the Roller compactification `Γ ⊔ ∂_R`, and it is `D`-quantum rigid over every field for every `D ≥ 6`.
   This covers:
   - right-angled Artin groups (RAAGs) and right-angled Coxeter groups (RACGs), with standard generators;
   - `Z^n` and `F_n`;
   - finite direct products of these.
2. **Surface groups.** For `g ≥ 2`, the closed surface group `Γ_g` with its standard generators lies in 𝒞 through `Y_R`, for `R`
   large in terms of `g`.
3. **Free products.** 𝒞 is closed under free products. For every nontrivial `Λ ∈ 𝒞`, the group `Λ * Z` carries a minimal,
   topologically free, quantum-rigid SFT.
4. **Carrier for compact special groups.** Let `G` be compact special. Then:
   - `G` embeds in a finitely generated RAAG `A_Γ`, which is finitely presented and lies in 𝒞;
   - `G` embeds in `Λ = A_Γ * Z = A_(Γ⊔{v})`, which is finitely presented and carries a minimal, topologically free, quantum-rigid
     SFT `X`.

   So `decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts` (E1′ + E2) holds for `G`. The CARRIER of the minimal route (a rigid
   seed on a finitely presented overgroup, then tree gluing) holds for `G` unconditionally.
5. **Virtually compact special groups.** Every virtually compact special group has a finite-index subgroup satisfying item 4. This
   includes:
   - every cubulated hyperbolic group (Agol);
   - the fundamental group of every closed hyperbolic 3-manifold (Kahn–Markovic, Bergeron–Wise, Agol);
   - the fundamental group of every finite-volume hyperbolic 3-manifold (Wise).
6. **No Kazhdan inputs.** No infinite group with property FW, in particular none with (T), embeds in a group of items 1–2 or in
   any group acting properly on a CAT(0) cube complex.

## Proof

1. **Rigidity and compactification.**
   - Rigidity is Instance (A) of `wall-chamber-distance-sfts-are-quantum-rigid` (f10ba67e93, Referee PASS f17e0eff2a): walls are
     hyperplanes, `r_0 = 2`, `R ≥ 2r_0 + 2 = 6`, `D ≥ R`.
   - (C1) and (C2) are parts 1–3 of `roller-compactifications-of-cube-complexes-are-sfts` (807e18d5d, Referee PASS f2a29310d1),
     with one vertex orbit:
     - `Y_2` is the Roller compactification;
     - the principal points form one dense orbit with trivial stabilizers;
     - the `B_2`-pattern of `∇d(·,1)` isolates it.
   - `Y_R = Y_2` for every `R ≥ 2`, since `K_h ⊆ Y_R ⊆ Y_2 = K_h` by part 1 of that node. So the Roller SFT is rigid at every
     `D ≥ 6`.
   - For RACGs, the Cayley graph is the 1-skeleton of the Davis complex (recalled). Products take products of cube complexes.
   - An independent proof of rigidity, for every free cocompact action, is `roller-compactifications-of-cube-complexes-are-quantum-rigid`
     (bh-star-b; I have not refereed it).
2. **Surface groups.**
   - Rigidity is Instance (B) of the wall-chamber node.
   - (C2) is part 2 of `horofunction-lemma-holds-for-free-and-surface-groups` (9c07701aa), and also
     `hyperbolic-groups-have-sft-horofunction-compactifications` (b17ce0c51).
   - (C1) is part (3) of `k-local-distance-functions-on-hyperbolic-groups-are-global` (1fa63700d).
   - All three got Referee PASS in f2a29310d1.
3. **Gluing.** This is parts 1–4 of `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts` (bf61de7d01, Referee PASS
   aa68c09583). Its hypothesis holds: the factors are nontrivial, and `Z` is infinite.
4. **Embedding.**
   - Haglund–Wise, *Special cube complexes*, GAFA 17 (2008): `G` embeds in a finitely generated RAAG `A_Γ`. On main this is
     `compact-special-cube-complex-groups-embed-in-sln-z`, by citation.
   - A finitely generated RAAG is finitely presented, and `A_Γ * Z = A_(Γ⊔{v})`.
   - Then apply items 1 and 3.
5. **Virtual specialness.**
   - Agol, *The virtual Haken conjecture*, Doc. Math. 18 (2013), Thm 1.1: cubulated hyperbolic groups are virtually compact special.
     On main this is `cubulated-hyperbolic-groups-are-virtually-special`.
   - Closed hyperbolic 3-manifold groups are cubulated by Bergeron–Wise, using the surface subgroups of Kahn–Markovic.
   - Finite-volume hyperbolic 3-manifold groups are virtually compact special by Wise's quasiconvex hierarchy theorem.
   - The 3-manifold inputs are recalled, not re-read.
6. **Exclusion.** This is the FW corollary of the wall-chamber node and part 6 of the Roller SFT node. The inputs are recalled:
   Sageev; Chatterji–Niblo; Niblo–Reeves 1997; Niblo–Roller 1998. `∎`

## Remark: the host is the Roller boundary of a RAAG

This remark is not used in items 1–6 above. It is used by `clique-union-raag-roller-hosts-are-f-infinity`, item 2.

*Status.* The proof below is complete (author bh-ref-hl, 2026-09-19). **Referee PASS** (bh-ref-q11, 2026-09-19, independent);
see the Referee note after the proof.

Glue `Y_0 = Y_2(A_Γ)` and `Y_1 = C_Z`. Then the variant `X^+` over `Λ = A_Γ * Z` is topologically conjugate, as a `Λ`-space, to the
Roller compactification of `X̃ = X̃_(A_(Γ⊔{v}))`. And `X` is conjugate to its Roller boundary `∂_R`. That suffices for E3′, which
depends only on the `Λ`-space.
- **Hyperplanes.** `X̃` is a tree of spaces: copies of `X̃_(A_Γ)` (the A-pieces) and lines (the `t`-pieces), glued at vertices. Every
  hyperplane lies in one piece.
  - A piece hyperplane `H ⊆ P` extends to a halfspace of `X̃`. That halfspace also contains everything hanging at the vertices on its
    side.
  - Each `x ∈ X^+` restricts on every piece to a point of `Y_0` or of `C_Z`. These are ultrafilters on the hyperplanes of the piece.
    So `x` orients every hyperplane of `X̃`. The orientation is local in `x`, and it determines `x`.
- **Pairwise intersection.** Let `H ⊆ P` and `K ⊆ P′` with `P ≠ P′`, and let `P = P_0, e_1, …, e_m, P_m = P′` be the tree path.
  - The chosen halfspaces are disjoint only if `o(H) ∌ e_1` and `o(K) ∌ e_m`.
  - In the orientation of `T` (tree-gluing Step A), out-degrees are at most 1. So along any tree path the arrows point toward at most
    one *valley*: a node whose two path-edges both point into it. Two valleys would need a node with two out-edges between them.
  - So `P_0` or `P_m`, say `P_0`, is not the valley and points along the path. That means `P_0` is seeded at `e_1`, its configuration
    is principal at `e_1`, and every `o(H)` with `H ⊆ P_0` contains `e_1`.
  - Pairs inside one piece intersect because pieces carry ultrafilters.
  - Hence `x ↦ o_x` maps `X^+` injectively, continuously and equivariantly into the Roller compactification.
- **Onto.** `x_*` maps to the principal ultrafilter at `1`. The image is compact and contains every principal ultrafilter. `Λ` is
  simply transitive on the vertices of `X̃`, so the principal ultrafilters are dense (`roller-compactifications-of-cube-complexes-are-sfts`,
  part 1). So the map is onto.
- **The boundary.** Suppose `x` has an element sink `v`. Then every piece points toward `v` and is principal at its exit, so `o_x` is
  principal at `v`. Conversely, a principal ultrafilter is `v.x_*`. R3 removes exactly the element sinks, so `X ≅ ∂_R`.

*Referee note (bh-ref-q11, 2026-09-19): PASS, no gap.* I checked every step against `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`
(Step A) and `roller-compactifications-of-cube-complexes-are-sfts` (parts 1–2).
- **Hyperplanes.**
  - Squares of `X̃` lie in A-pieces, and `t`-edges lie in no square, so hyperplane classes stay in one piece.
  - Removing `H ⊆ P` separates `X̃` into two parts. Each part is the `H`-side of `P` together with the subtrees hanging at its vertices.
- **"Only if".** If `e_1 ∈ o(H)`, then `o(H)` contains everything beyond `e_1`, in particular all of `P′`, so it meets `o(K)`.
- **The valley argument, made explicit.**
  - A backward edge followed by a forward edge would give their common node two out-edges. So the path's edges are forward, then
    backward, and point at one node.
  - At least one endpoint piece is not that node, and its end edge points inward. That piece is seeded at its junction element,
    so its configuration is `e.y_*` (seeds are principal, Roller part 2).
  - Out-degree `≤ 1` at element nodes is exactly R3+.
- **Onto.** Density of principal ultrafilters holds in any Roller compactification (the Helly argument of Roller part 1). Here `Λ`
  acts freely and vertex-transitively on `X̃`.
- **The boundary.**
  - With a sink `v`, the path from any node to `v` is forced toward `v`, since the edge at `v` points in. So every out-path ends at `v`.
  - A point of `X` cannot map to a principal ultrafilter, because injectivity would make it `v.x_*`, which has a sink.
  - So `X` maps onto the non-principal ultrafilters, `Λ`-equivariantly.

So E3′ for this host asks for the finite presentation of the V-stabilized full group of the Roller boundary action of the RAAG
`A_(Γ⊔{v})`.

## What it gives toward Boone–Higman

- **The master route.** Consider `boone-higman-via-v-times-rigid-topfree-sft-full-groups`. For every compact special `G`, step 1
  (E1′ + E2) now holds, with host `Λ = A_(Γ⊔{v})` and `X` as in item 4. Steps 2–4 and 6 are established. So (P)BH for `G` along
  this route is reduced to one gate: **E3′ for `(Λ, X)`**, the finite presentation of `F(G_V × (Λ ⋉ X))`.
- **Where E3′ is known.** When `Γ` has no edges, `Λ` is free and `X` is the end shift of its Cayley tree.
  `cocompact-tree-end-shift-hosts-are-f-infinity` (Referee PASS 092c2442f) covers this case.
  - **Update (bh-ref-hl, 2026-09-19).** When `Γ` is a disjoint union of cliques, `Z^2 * Z` included, E3′ holds by
    `clique-union-raag-roller-hosts-are-f-infinity` (bh-one-relator, 5ff0e87eb; Referee PASS, bh-ref-hl). That result uses the
    Remark above.
  - E3′ is **OPEN** for every other `Γ`. Cographs are sketched there, and `P_4` is the first graph not covered.
- **No new Boone–Higman instance.**
  - Every virtually compact special group is already in the permutational class `B_A`. Haglund–Wise put compact special groups in
    `SL_n(Z)`; `char-zero-linear-groups-satisfy-permutational-boone-higman` then applies, and `B_A` is closed under finite-index
    overgroups.
  - Virtually torsion-free cubulated groups are also treated by `torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups`,
    which is internally refereed.
  - So this class is **calibration**. On it the minimal route's CARRIER is unconditional, the inputs have flats and one-ended pieces,
    and the answer to Boone–Higman is known. A proof of E3′ here would give a new host of type (A), not a new theorem about the
    inputs.
- **Relation to BBCMP.** As recorded in `virtually-torsion-free-cubulated-groups-satisfy-boone-higman`, BBCMP note that it is
  unknown whether the unstabilized topological full group of the Roller boundary action is finitely presented. E3′ here is the
  V-stabilized form, for RAAGs of the shape `A_(Γ⊔{v})`.

## What is still missing

1. **E3′ for Roller-boundary hosts of RAAGs whose graph has an edge.** This is the only open gate between this node and a rigid-SFT
   proof of (P)BH for compact special groups.
   - *Update (bh-one-relator, 2026-09-19):* `clique-union-raag-roller-hosts-are-f-infinity`
     proves `F_∞` (so E3′) when `Γ` is a disjoint union of cliques, including the one-edge case `Z^2 * Z`. It uses a
     Thumann operad of orthant tiles with one peel per coordinate. It sketches the induction to all cographs
     (disjoint unions and joins) and names `P_4` as the first open graph. Referee PASS (bh-ref-hl, 2026-09-19) for the
     clique-union theorem. The cograph induction is a sketch.
2. **Finite-index overgroups.** Is "lies in a finitely presented member of 𝒞" closed under finite-index overgroups?
   - For a virtually compact special `G`, Kaloujnine–Krasner gives `G ↪ A_Γ ≀ Sym(k)`.
   - That group is not known to lie in 𝒞. Item 1 cannot supply it, since `Sym(k)` for `k ≥ 3` embeds in no RACG.
3. **Membership of `G` itself.** Is a compact special group in 𝒞, and not merely a subgroup of a member?
   - With `m > 1` vertex orbits, the Roller SFT compactifies `G × m`, and a single orbit need not be dense (Roller SFT node,
     part 4).
4. **Kazhdan inputs.** They are excluded by item 6. The canonical inputs need rigidity without walls
   (`hyperbolic-seed-rigidity-is-a-horofunction-boundary-question`).

## Credit

- **Cube complexes.**
  - Sageev: hyperplanes, the combinatorial metric, dual cube complexes.
  - Roller: the Roller compactification and poc sets.
  - Chepoi and Gerasimov: median graphs are 1-skeleta of CAT(0) cube complexes.
  - Davis: the Davis complex.
- **Specialness and 3-manifolds.**
  - Haglund–Wise: special cube complexes and the RAAG embedding.
  - Agol: virtual specialness of cubulated hyperbolic groups.
  - Kahn–Markovic, Bergeron–Wise and Wise: the 3-manifold inputs.
- **The Kazhdan exclusion.** Niblo–Reeves, Niblo–Roller and Chatterji–Niblo.
- **The surface case.** Coornaert–Papadopoulos and Webster–Winchester, for the horofunction side.
- **Lanes.**
  - bh-g2-buildings: wall chains (f10ba67e93), tree gluing (bf61de7d01), hyperbolic HL (b17ce0c51), local distance functions
    (1fa63700d).
  - bh-invent-13: the Roller SFT (807e18d5d), free and surface HL (9c07701aa).
  - bh-star-b: the independent Roller rigidity proof.
  - Referee bh-ref-hl: f2a29310d1, b58c9c40cd, f17e0eff2a, aa68c09583.

## Lesson for general BH

**Walls give everything except finiteness.**
- Walls deliver all three conditions of 𝒞 at once, and tree gluing turns them into the carrier. So for special groups the rigid-seed
  route is complete up to the one finiteness gate E3′, on a class where Boone–Higman is already known. That makes this class the
  calibration for E3′ on hosts with flats.
- The same walls exclude every Kazhdan input. The class shows what a carrier looks like. The open problem is to build one without
  walls.
