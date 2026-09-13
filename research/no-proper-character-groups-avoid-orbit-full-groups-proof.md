---
rg: 2
id: no-proper-character-groups-avoid-orbit-full-groups-proof
kind: route
title: No proper characters gives the trivial-plus-regular character segment, and the exclusion theorem applies; import the two general sources and verify Thompson's T
target: no-proper-character-groups-avoid-amenable-orbit-full-groups
requires:
  - stabilizer-rigid-groups-avoid-amenable-orbit-full-groups
  - amenable-full-group-forces-invariant-measure
---

**Sources**, read from arXiv TeX on MSI
(`/scratch.global/sauer354/ex/ex-fp-simple-sofic/`, 2026-09-12).
- **Dudko--Medynets**, *Finite factor representations of Higman--Thompson groups*,
  arXiv:1212.1230, `main.tex`.
  - Definition `DefinitionCompressibleBase` (lines 139--145): a base `U` of the topology
    with (i) every support inside some `U`; (ii) for `U_1, U_2 ∈ U` some `g` with
    `g(U_1) ⊆ U_2`; (iii) for `U_1, U_2, U_3` with disjoint closures of `U_1, U_2`
    some `g` with `g(U_1) ∩ U_3 = ∅` and `supp(g) ∩ U_2 = ∅`; (iv) `U` is
    upward directed.
  - Theorem `TheoremNoCharactersSimpleGroups` (line 205, Theorem 2.9 as cited by
    Gardella--Tanner line 1283): "Let `G` be a simple countable group admitting a
    compressible action on a regular Hausdorff topological space `X`. Then `G` has no
    proper characters."
  - Theorem `TheoremCharactersNonSimpleGroups` (lines 212--222): for an ICC subgroup
    `R ≤ G` with (i) no proper characters, and (ii) for each `g != e` a sequence of
    distinct `g_i ∈ C_R(g)` with `g_i^-1 g_j ∈ R`, every finite factor representation
    of `G` is regular or factors through `G/N(R)`.
  - Corollary `CorollaryFnr` (1) (line 320): "The group `F_(n,r)'` has no proper
    characters."
- **Gardella--Tanner**, *Generalisations of Thompson's group V arising from purely
  infinite groupoids*, arXiv:2302.04078, `main.tex`.
  - Line 781: purely infinite means every compact open `X ⊆ G^(0)` is the source of two
    compact open bisections with disjoint ranges inside `X`.
  - Corollary `D has no proper characters` (lines 1270--1271): "Let `G` be a purely
    infinite and minimal Cantor groupoid. Then `A(G)` has no proper characters."
  - Stated in the introduction as Corollary `nopropercharacters` (line 517), for
    minimal, purely infinite, essentially principal Cantor groupoids.
  - Line 1840: "`nV_(2,r)` has no proper characters, and `V_(k,r)` has no proper
    characters if `k` is even."

**Item 1.** The characters of `Gamma` form a weak*-compact convex set whose extreme
points are the indecomposable characters (Definition in Gardella--Tanner, lines
1247--1265). With only two extreme points, Krein--Milman makes it the segment
`{s 1 + (1-s) delta_1}`. That is hypothesis (CR) of
`stabilizer-rigid-groups-avoid-amenable-orbit-full-groups`, whose theorem gives the
conclusion. ∎

**Item 2** is Theorem 2.9 of Dudko--Medynets, then item 1.

**Item 3.**
- *No proper characters:* Gardella--Tanner's corollary.
- *Simple and infinite:* Nekrashevych, arXiv:1511.08241, Theorem 1.1, recorded in
  `minimal-z2-subshift-derived-full-groups-are-fg-simple` for minimal groupoids of
  germs. An essentially principal groupoid is effective.
- *Not amenable.* `A(G)` contains every 3-cycle on a multisection. By Lemma 1.1 of
  `research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md` these realize moving
  bisections. Purely infinite gives a nonempty clopen `X` with two disjoint clopen
  images of itself under compact open bisections. So item 3 of
  `amenable-full-group-forces-invariant-measure` makes no group realizing moving
  bisections amenable. ∎

**Item 4, Thompson's T.**
- *Setting.* `T` acts on the circle `S^1 = [0,1]/(0 ~ 1)` by dyadic PL homeomorphisms.
  The subgroup `R` of elements supported in a closed arc avoiding `0` is `F'`: elements
  of `F` that are the identity near `0` and `1`.
- *Hypothesis (i).* `R` is infinite and simple, hence ICC, and has no proper characters
  by Corollary `CorollaryFnr` (1) with `n = 2`, `r = 1`.
- *Hypothesis (ii).* Let `g ∈ T \ {e}`. Pick a small open dyadic arc `I` with
  `I ∩ g(I) = ∅`, such that the closure of `I ∪ g^-1(I)` avoids `0`; this is possible
  because `g` moves an open set. Choose distinct `h_1, h_2, ...` in `R` supported in `I`,
  and put `g_i = h_i g h_i^-1 ∈ C_R(g)`. Then
  `g_i^-1 g_j = h_i (g^-1 h_i^-1 h_j g) h_j^-1`. The middle factor is supported in
  `g^-1(I)`, so the product is supported in `I ∪ g^-1(I)` and lies in `R`. The `g_i` are
  distinct: if `h_i g h_i^-1 = h_j g h_j^-1`, then `c = h_j^-1 h_i` commutes with `g`, so
  `supp(c) ⊆ I ∩ g(I) = ∅` and `h_i = h_j`.
- *Conclusion.* Theorem `TheoremCharactersNonSimpleGroups` says every indecomposable
  character of `T` is regular or factors through `T/N(R)`. Under the simplicity
  hypothesis `N(R) = T`, so `T` has no proper characters.
- *Not amenable.* `T` contains the rotations by dyadic rationals, a dense subgroup. An
  invariant probability measure would have `mu^(n) = e^(2 pi i n a) mu^(n)` for dense
  `a`, so it would be Lebesgue measure. But `T` contains elements of slope 2 on an arc,
  which do not preserve Lebesgue measure. A compact `T`-space without an invariant
  probability measure makes `T` non-amenable. Item 1 then applies. ∎

**Hypothesis checks.**
- *Simplicity cannot be dropped in item 1:* the argument passes through finite orbits
  being fixed points.
- *Non-amenability cannot be dropped:* an infinite simple amenable group would realize
  itself through its Bernoulli shift.
- *No proper characters is essential:* the Elek--Monod alternating group lies in a
  `Z^2` full group with full-support invariant measure, and its fixed-point character
  is a proper character.
