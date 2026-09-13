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
     - The natural candidates, such as stabilizers of chambers, of spherical residues
       and of boundary points, are not confined at all.
     - A negative answer needs a new obstruction that some lim-free MIF group
       satisfies.
   - **Gap.** Either a positive globalization mechanism for lim-free weakly hyperbolic
     groups without splittings, or a new obstruction to high transitivity beyond LBMB
     §2.4. Pins and search record: `research/artifacts/solve-ht-confined-2026-09-13.md`.
