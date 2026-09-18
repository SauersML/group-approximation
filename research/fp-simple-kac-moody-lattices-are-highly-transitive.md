---
rg: 2
id: fp-simple-kac-moody-lattices-are-highly-transitive
kind: claim
title: The finitely presented simple Kac--Moody lattices over finite fields are highly transitive (BFFHZ Question 3.6)
root: true
distinct_from:
  burger-mozes-simple-lattices-are-highly-transitive: that is the established Burger--Mozes case of BFFHZ Remark 3.5; this is their open Question 3.6 for the other known source of finitely presented simple groups.
  simple-kazhdan-kac-moody-lattices-exist: that records that these lattices are finitely presented, simple and Kazhdan; this asks whether they are highly transitive, which by Theorem C would put them and all their subgroups in the permutational Boone--Higman class.
---

**OPEN.** BFFHZ, arXiv:2503.21882v2, extracted PDF text on MSI
(`bh-reviewer/2503.21882.txt`), l.762--767:

> "To the best of our knowledge, the only existing source of finitely presented
> infinite simple groups for which PBH remains open is non-affine Kac–Moody
> groups over finite fields [CR09]. These are closely related to Burger–Mozes
> groups in some aspects, but with key differences. One of these differences is
> the behavior of the action on the boundary, which in turn is responsible for
> the difference in their second bounded cohomology [CF10, Theorem 1.8]. In the
> above proof that Burger–Mozes groups are highly transitive, this was the main
> input, so a different argument would be needed.
> Question 3.6. Are finitely presented simple Kac–Moody groups highly
> transitive? Are they MIF? Do they satisfy PBH?"

**If yes.** Highly transitive finitely generated simple groups are MIF [HO16,
Theorem 5.9], and Theorem C (iii) puts them and all their subgroups in the
permutational class (`fp-simple-highly-transitive-groups-satisfy-pbh`). This
would remove the last known family of test cases for
`bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`.

**Parts two and three settled (2026-09-13).** Rybak, arXiv:2605.14159v3,
Proposition A, makes these groups MIF (`fp-simple-kac-moody-lattices-are-mif`), and
BFFHZ Theorem C then gives permutational Boone--Higman for them and all their
subgroups (`fp-simple-kac-moody-lattices-satisfy-pbh`). What stays open is the first
part, high transitivity, which this node asks.

**Explicit members.** `simple-kazhdan-kac-moody-lattices-exist` and
`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`: the (2,4,6) lattices
`Λ_q/Z` for `q ≥ 4` are finitely presented, simple and Kazhdan.

## Attempts

1. **Hull--Osin through acylindrical hyperbolicity: killed.** Hull--Osin make
   acylindrically hyperbolic groups with trivial finite radical highly
   transitive. But acylindrically hyperbolic groups are SQ-universal
   (Dahmani--Guirardel--Osin), and an infinite simple group is not, so no
   simple Kac--Moody lattice is acylindrically hyperbolic. Kazhdan members also
   cannot embed in V or in any Haagerup group, so the "embeds in V" pattern
   that rescues T does not apply to them.
2. **Le Boudec's Burger--Mozes argument on the building boundary: unclear,
   sketch only (2026-09-13, lane solve-bh-pbh-equiv).** Take a hyperbolic Weyl
   group type such as (2,4,6), so the positive building `X+` is a locally
   finite Gromov-hyperbolic building.
   - **Faithfulness:** `Λ/Z` is simple and acts nontrivially on `∂X+`.
   - **Minimality and extreme proximality (sketch):** `Λ` is dense in its
     completion `Ḡ+`, which is its closure in `Aut(X+)` by definition. `Ḡ+`
     acts cocompactly on `X+`, and hyperbolic elements have densely many
     fixed-point pairs with north--south dynamics. By continuity of the action,
     any `g ∈ Ḡ+` with `gC ⊂ V` (C compact, V open) has a neighbourhood with
     the same property, which meets `Λ`. Not checked against sources:
     continuity of `Ḡ+ ↷ ∂X+`, density of hyperbolic fixed-point pairs for
     this locally compact action, and minimality.
   - **Missing: topological freeness.** Suppose `λ ≠ 1` acts trivially on a
     nonempty open set. Extreme proximality gives, for every `k`, `k`
     translates of an open set containing its support, with pairwise disjoint
     closures. So `Λ` contains `k` pairwise commuting conjugates of `λ` with
     disjoint supports.
     - If `λ` has infinite order, this gives `Z^k ≤ Λ` for every `k`. The flat
       rank bound for the discrete action on `X+ × X−` should exclude it; not
       verified for a non-uniform lattice.
     - If `λ` has finite order, this gives finite subgroups of unbounded order.
       That is not a contradiction if `Λ` is a non-uniform lattice with
       unbounded finite subgroups (root groups over `F_q`); to be checked
       against [CR09].
     BFFHZ's cohomological-dimension step does not transfer, because `Λ` has
     torsion. The remaining test: does a nontrivial root-group element `u ∈
     U_α(F_q)` act trivially on a nonempty open subset of `∂X+`?
   - **Criterion not pinned.** FLMMS22 Theorem B is for groups acting on trees.
     The general criterion that would turn "minimal, extremely proximal,
     topologically free" into high transitivity (possibly Le Boudec--Matte
     Bon, *Confined subgroups and high transitivity*, Ann. H. Lebesgue 2022)
     was not read; the arXiv API was rate-limited.

3. **Through Rybak's hyperbolic curtain model: gives MIF and PBH, not high
   transitivity (2026-09-13, lane solve-bh-kac-moody).**
   - Rybak (arXiv:2605.14159v3, Proposition A and its proof, TeX l.1548--1558) makes
     `G(F)` faithful weakly hyperbolic through the curtain model of the Davis
     building. Its action on the limit set is topologically free, so it is MIF by
     her Theorem A.
   - The criterion that turns topological freeness into high transitivity is proved
     only for trees. Fima--Le Maître--Moon--Stalder, arXiv:2003.11116, TeX
     `HTacttrees-DAJ-final.tex` l.413--416: "Let $\Gamma\curvearrowright\mathcal{T}$
     be a minimal action of general type of a countable group $\Gamma$ on a tree
     $\mathcal{T}$. If the action on the boundary $\Gamma\curvearrowright \partial\mathcal{T}$
     is topologically free, then $\Gamma$ admits a highly transitive and highly
     faithful action; in particular, $\Gamma$ is highly transitive." Their
     equivalence theorem (l.503--512), which BFFHZ cite as Theorem B, makes
     `td ≥ 4`, high transitivity, MIF and topological freeness on `∂T` equivalent for
     faithful minimal general-type tree actions.
   - Rybak extends only the MIF ⇔ topologically free part to hyperbolic spaces, and
     proves no high-transitivity statement for lim-free groups.
   - The Kazhdan members have property (T), hence property FA (standard, not
     re-read), so they have no general-type tree action and the tree criterion cannot
     apply to them.
   - Missing input: a hyperbolic-space analogue of the FLMMS criterion, i.e. that a
     faithful general-type action on a hyperbolic space that is topologically free on
     the limit set yields a highly transitive action.

4. **Extending the FLMMS criterion to hyperbolic spaces: the method does not
   transfer, and no known tool decides the case (2026-09-13, lane
   solve-bh-ht-hyperbolic).**
   - **Where FLMMS use the tree.** In arXiv:2003.11116 (TeX
     `HTacttrees-DAJ-final.tex`, on MSI at `/scratch.global/sauer354/km-ht/2003.11116.d/`)
     high transitivity is built from the Bass--Serre decomposition of `Γ`. A partial
     bijection is extended by a "free globalization" of a *pre-action* of an HNN extension
     or amalgam through its Bass--Serre graph (l.739--745; sections on free globalizations
     for HNN extensions, l.1462ff, and for amalgams, l.2456ff), followed by the Baire
     category theorem in the Polish space of actions (l.702; Theorem
     `ThmGroupsHTHNNBaire`, l.2345). The tree enters only through that splitting.
   - **So the method has no input for the Kazhdan members.** A group with property (T)
     has property FA, hence no nontrivial amalgam or HNN splitting (standard, not
     re-read). What is missing is not a hyperbolic version of the statement but a new
     globalization mechanism for actions that do not come from splittings; north--south
     boundary dynamics do not supply pre-actions.
   - **The other positive tools miss these groups.** Hull--Osin needs acylindrical
     hyperbolicity (Attempt 1). Gelander--Glasner--Soifer treat unbounded subgroups of
     `SL_2(k)` over local fields (as cited in FLMMS l.405--407 and Le Boudec--Matte Bon,
     Ann. H. Lebesgue 5 (2022), p. 493). A Kazhdan group has bounded image in every such
     `SL_2(k)`, since isometric actions of (T) groups on trees and real hyperbolic spaces
     have bounded orbits (standard, not re-read).
   - **No known obstruction bites either.** Le Boudec--Matte Bon §2.4 (p. 498, read from
     the PDF): a highly transitive group that is not partially finitary is MIF, has
     trivial centralizers of nontrivial normal subgroups, and has every finite group as a
     subquotient. `S_q` is simple, finitely generated and infinite, so not partially
     finitary; it is MIF by `fp-simple-kac-moody-lattices-are-mif`; and it contains free
     subgroups from two loxodromics with disjoint fixed points in Rybak's general-type
     action, so every finite group is a subquotient. Rybak's rigidity of 3-transitive
     actions (arXiv:2605.14159v3, TeX l.263--273) is only for faithful weakly hyperbolic
     groups that are *not* lim-free, while `S_q` is lim-free (her Proposition A), so it
     gives no bound on the transitivity degree.
   - **The only obstruction template.** Le Boudec--Matte Bon Corollary 1.4 (p. 493): if
     some confined subgroup of `S_q` had no faithful highly transitive action, neither
     would `S_q`. No confined subgroup of `S_q` is known here; stabilizers for the
     building actions are the natural candidates to test.
   - **Gap.** Either a globalization mechanism turning a faithful general-type hyperbolic
     action, topologically free on the limit set, into a highly transitive action without
     using a splitting, or a confined subgroup of `S_q` with no faithful highly transitive
     action.
5. **Confined-subgroup obstructions cannot work with the known tests (2026-09-13,
   lane solve-ht-confined).**
   - **Theorem** (`confined-subgroups-of-lim-free-actions-have-full-limit-set`): if a
     group acts on a hyperbolic space with general type and topologically freely on
     the limit set, every confined subgroup is of general type with the full limit
     set, fixes no boundary point, and is lim-free.
   - **For `S_q`** (`kac-moody-lattice-confined-subgroups-are-lim-free-and-mif`), with
     Rybak's action on `E(X_D)`, every confined subgroup:
     - is lim-free and MIF;
     - satisfies no identity and is not partially finitary;
     - has trivial centralizers of nontrivial normal subgroups;
     - has every finite group as a subquotient.

     A subgroup is not confined if it has a bounded orbit, a smaller limit set, or a
     fixed limit point.
   - **Consequence for route (b).**
     - Le Boudec--Matte Bon Theorem 1.1 and Corollary 1.4, combined with the
       obstructions of their §2.4 (the only ones they know), cannot show that `S_q` is
       not highly transitive.
     - The natural candidates are not confined at all: stabilizers of points of the
       curtain model and of limit points. This covers stabilizers of chambers and of
       spherical residues, given that the curtain model has the same points as the
       building (Petyt--Spriano--Zalloum, not re-read).
     - A negative answer needs a new obstruction that some lim-free MIF group
       satisfies.
   - **Gap.** Either a positive globalization mechanism for lim-free weakly hyperbolic
     groups without splittings, or a new obstruction to high transitivity beyond LBMB
     §2.4. Pins and search record: `research/artifacts/solve-ht-confined-2026-09-13.md`.
6. **Curtis--Tits coverings: a generic-action reduction, and the finiteness
   constraint from FFKLZ (2026-09-18, lane bh-free-24; two elementary lemmas plus a
   proposal, not reviewed).**
   - **Why a new mechanism is needed.** The `S_q` have property FA (each is generated by
     the finite rank-one Levi groups, and any two of these generate a finite group, so
     Serre's criterion gives a global fixed point; standard, not re-read). So they have no
     splitting, and every known high-transitivity proof that goes through a splitting
     (FLMMS, Moon--Stalder free products) or through acylindrical hyperbolicity (Attempt 1)
     is unavailable. What they do have is a presentation by finitely many *finite* groups.
   - **Input (cited, not read at source).** Caprace--Rémy, arXiv:math/0607664v2, TeX
     `SimplSuperrigid.tex` l.1819--1820: "Finite presentation follows from \cite{AbrMu}
     under the hypothesis that $q_{\min} > 2$." [AbrMu] is Abramenko--Mühlherr,
     *Présentations de certaines BN-paires jumelées comme sommes amalgamées* (C. R. Acad.
     Sci. Paris 1997; paywalled, not read). In its standard reading, for 2-spherical `W` the
     group `Λ` is the amalgamated sum of the finite groups `L_J = P_J^+ ∩ P_J^-`,
     `J ⊆ S`, `|J| ≤ 2` (the rank ≤ 2 Levi factors of the twin BN-pair, with `L_∅ = T` the
     torus).
   - **Lemma A (elementary, from the universal property).** If `Λ = colim_{|J| ≤ 2} L_J`,
     then an action of `Λ` on a set `Ω` is exactly a family of actions `ρ_J` of the finite
     groups `L_J` on `Ω` with `ρ_J|_{L_K} = ρ_K` whenever `K ⊆ J`. So the Polish space
     `A(Λ,N)` of actions on `N` is the closed subset of `∏_{|J|≤2} Hom(L_J, Sym(N))` cut out
     by these restriction equalities. Every `L_J`-orbit is finite, so a `Λ`-set is a union
     of finite rank-2 orbits glued along rank-1 orbits: a covering of the finite complex of
     groups of the amalgam. No condition involving three indices appears.
   - **Lemma B (the standard Baire reduction, elementary).** Let `X ⊆ A(Λ,N)` be closed and
     nonempty. Suppose that for every `k`, all pairs of `k`-tuples `a, b` of distinct points,
     and every `1 ≠ λ ∈ Λ`, both of the open sets
     `{ρ ∈ X : ρ(g)a = b for some g ∈ Λ}` and `{ρ ∈ X : ρ(λ) ≠ 1}` are dense in `X`. Then the
     comeager set of faithful highly transitive actions in `X` is nonempty. (Each set is
     open because the condition depends on finitely many values of finitely many
     generators; Baire in the Polish space `X`.)
   - **So the question becomes a finite free-completion problem.** By Lemmas A and B, high
     transitivity of `S_q` follows from a density statement (E) for some closed `X`, for
     example the closure of the actions without finite orbits. (E) says: a finite partial
     family of compatible finite-group actions, with specified `k`-tuples, can be completed
     to a genuine family in which some word carries one tuple to the other. That is an
     amalgamation problem for coset geometries of the rank-2 Levi groups `L_{ij}`, which are
     finite groups of Lie type.
   - **Calibration: (E) must use non-sphericity.** For a spherical diagram, such as
     `SL_4(q)` with its Curtis--Tits amalgam, the colimit is finite, every action has only
     finite orbits, and the pairwise relations force every free completion to close up; so
     `X` is empty. Any proof of (E) must therefore use that the rank-3 residues of the type
     are non-spherical, as for `(2,4,6)`. The natural tools are the free constructions of
     chamber systems whose only obstructions sit in spherical rank-3 residues (Tits'
     local approach; Ronan--Tits, "Building buildings"), transported from buildings to
     coverings of the Levi amalgam. Not attempted beyond this reduction.
   - **Constraint from FFKLZ (arXiv:2506.02319v2, TeX l.155--158, Theorem 1.1, and
     l.257, Corollary "cor large sets").** `Λ` acts on `X_+ × X_-`, a finite-dimensional
     contractible complex, with finite cell stabilizers (it is discrete in `G_+ × G_-`), so
     `Λ` lies in Kropholler's class `HF`, and so does `S_q`. A highly transitive action is
     oligomorphic. Hence in every highly transitive action of `S_q` there are finite subsets
     of every size `≥ k` whose stabilizers are not of type `FP_∞`, and by transitivity on
     `k`-sets, for infinitely many `k` no `k`-set stabilizer is `FP_∞`. This adds to
     `km-building-open-subgroups-have-infinite-ht-orbits`. It is only new content if `S_q`
     is itself `FP_∞`, which was not checked here; otherwise FFKLZ Lemma 2.3 (l.272) already
     gives it. The same theorem (l.171) says every twisted Brin--Thompson group `SV_{S_q}`
     built from an action of `S_q` on an infinite set fails `FP_∞`.
   - **Gap.** Prove (E), or at least one of its density statements, for the `(2,4,6)`
     Levi amalgam, or show that the pairwise Levi relations force identifications that
     block it even in non-spherical type. Sources fetched this session are in the swarm
     scratchpad `src/bh-free-24/` (FFKLZ, BFFHZ, Rybak and Le Boudec--Matte Bon TeX).
7. **Attacking (E): the link-by-link free completion closes up; one curvature lemma
   (2026-09-18, lane bh-free-24; elementary, not reviewed). (E) stays OPEN.**
   - **Set-up.** By Lemma A, a `Λ`-set is a covering of the Levi triangle of groups
     (vertex groups `L_12, L_13, L_23`, edge groups `L_1, L_2, L_3`, face group `T`),
     and `L_ij = ⟨L_i, L_j⟩`. So a `Λ`-set is a `T`-set with three `L_i`-actions such
     that each pair generates an action factoring through `L_ij`. The link at a vertex of
     type `ij` of the development is the coset graph `Γ_ij` of `L_ij` with respect to
     `L_i, L_j` (edges = cosets of `T`), since `L_i ∩ L_j = T`.
   - **What works: stars.** Completing one vertex whose partial data is a single `i`-edge
     together with the `j`-edges through its chambers (a star in `Γ_ij`) always succeeds.
     Distinct `j`-panels through distinct chambers of an `i`-panel are disjoint cosets, so
     the star embeds `L_i`- and `L_j`-equivariantly into a regular `L_ij`-orbit, and the
     rest of the orbit is new points.
   - **What fails: the growth order.** After one completion step the new points acquire
     edges at several *different* uncompleted vertices. Concretely: once a `13`-vertex
     `u` is completed, each point of a `3`-edge `E ⊂ u` lies on a different `1`-edge of
     `u` (because `L_1 ∩ L_3 = T`). Completing those `12`-vertices then gives the points
     of `E` their `2`-edges from different sources, all at the same `23`-vertex. So that
     vertex's partial link is no longer a star but a union of stars meeting in `E`. The
     `L_23`-relations can then force identifications. Whether they do is exactly (E).
     There is no order of completion that avoids this, because every triangle has
     vertices of all three types.
   - **Lemma C (curvature, from simplicity).** Let `g_J` be the girth of `Γ_J`. Then
     `Σ_{|J|=2} 1/g_J ≥ 1/2`.
     - Proof: otherwise give each triangle the hyperbolic metric with angle `2π/g_J` at
       the vertex of type `J`. The link condition holds, so the (simply connected,
       locally finite) development is CAT(−1) (Gersten–Stallings, Bridson–Haefliger
       II.12). Then `Λ`, acting on it properly and cocompactly with finite stabilizers, is
       hyperbolic, and so is `S_q = Λ/Z`. An infinite hyperbolic group is not simple
       (non-elementary ones are SQ-universal, Olshanskii/Delzant; standard, not re-read).
     - For `(2,4,6)`: `L_12 = L_1 L_2`, since the commuting type gives a product. So any
       coset of `L_1` meets any coset of `L_2` (in a `T`-coset), `Γ_12` is complete
       bipartite, and `g_12 = 4`. Hence `1/g_13 + 1/g_23 ≥ 1/4`.
     - The Moore bound (vertex degree about `q^2`, about `q^{10}` vertices in the `G_2`
       Levi) already predicts girths of about 10 or less, so the lemma is a calibration,
       not a surprise.
   - **Consequence for (E).** The development is not CAT(−1) with these links, and its
     links are dense graphs of small girth. So Ronan–Tits / Ballmann–Brin style free
     constructions, which embed partial links of diameter below half the girth, do not
     apply. Any proof of (E) needs a global mechanism, for example a choice of the growth
     order adapted to the root system, or an ambient action (such as on `X_+`) whose
     orbits are perturbed. It cannot be done link by link.
   - **Symmetry remark (not proved here).** The Chevalley–Cartan involution of the Tits
     functor exchanges `U_α` and `U_{−α}` and so swaps `B_+` and `B_−`. That would
     transfer `km-building-open-subgroups-have-infinite-bi-index` and
     `km-building-open-subgroups-have-infinite-ht-orbits` to the negative completion.
     Existence of the involution on the minimal Kac–Moody group over `F_q` is standard
     but was not checked at source.
