---
rg: 2
id: penrose-tiling-group-amenable-orbit-citation
kind: route
title: Import the Chornyi-Juschenko-Nekrashevych torus model of the Penrose group and check freeness and the invariant measure
target: penrose-tiling-group-is-an-amenable-orbit-full-group
requires:
  - amenable-orbit-full-group-subgroups-are-sofic
---

**Source.** Chornyi, Juschenko, Nekrashevych, *On topological full groups of
`Z^d`-actions*, arXiv:1602.04255. The TeX source `IET_copy.tex` was read on MSI
(`/scratch.global/sauer354/fpsz2/src/1602.04255.d/`, 2026-09-12). Line numbers
refer to that file.

- Lines 90--93: "In the last Section we associate a group `𝒫` to the Penrose
  tiling. The main result is \begin{theorem} The derived subgroup of `𝒫` is
  simple and finitely generated. \end{theorem}"
- Line 95: "It is an open question to decide if the group `𝒫` is amenable."
- Lines 423--438: each line of `L` is doubled to form `C~` with quotient map
  `Q : C~ -> C`; regular points have one preimage; "Polygons with sides belonging
  to lines from `L` form a basis of topology of `C~`"; "The group `P` acts on `C~`
  in the natural way, so that the action is projected by `Q` to the action of `P`
  on `C` by translations."
- Lines 578--590: "The parallelogram `F`, seen as a subset of `C~`, is the
  fundamental domain of the group `<w_1, w_2> < P`. It is easy to check that
  `P/<w_1, w_2>` is isomorphic to `Z^2 ⊕ Z/5Z`. The space of orbits
  `C~/<w_1, w_2>` is naturally homeomorphic to the parallelogram `F`." Then:
  "\begin{proposition} The group `𝒫` is isomorphic to the full topological group
  of the action of `P/<w_1, w_2>` on the Cantor set `C~/<w_1, w_2>`.
  \end{proposition} \begin{corollary} The derived subgroup of `𝒫` is simple and
  finitely generated. \end{corollary}"

This gives item 1 of the claim.

**Item 2, freeness.** Let `a ∈ P` and `x~ ∈ C~` with `x~ + a ≡ x~ (mod Lat)`. Then
`Q(x~) + a = Q(x~) + l` for some `l ∈ Lat`, so `a = l` and `a` is trivial in
`Lambda`. So every nontrivial element of `Lambda` acts without fixed points.

**Item 2, the measure.** `Q` induces a continuous `Lambda`-equivariant map
`Qbar : X -> C/Lat`, where `Lambda` acts on the torus `C/Lat` through translation by
the image of `P`. The union `N` of the images of the lines of `L` in `C/Lat` is a
countable union of lines, since `P` is countable, so it is Lebesgue-null and
invariant. Off `Qbar^-1(N)` the map `Qbar` is a Borel bijection onto `(C/Lat) \ N`.
Let `mu` be the pullback of normalized Lebesgue measure `m` on `(C/Lat) \ N`,
extended by zero on `Qbar^-1(N)`. Translations preserve `m` and `N`, so `mu` is
`Lambda`-invariant.

**Item 2, full support.** A nonempty open subset of `X` contains the image of a
basic polygon of `C~` with nonempty interior, or of its intersection with a
half-plane or sector at a doubled point. Such a set contains an open subset of
regular points of positive area, so it has positive `mu`-measure.

**Item 3.** An element of `[[Lambda ~ X]]` has a continuous cocycle into the
discrete group `Lambda` on the compact space `X`, so its range is finite, and
`[[Lambda ~ X]] ≤ W(Lambda ~ X)`. A nontrivial element moves a nonempty open set,
which has positive measure. `Lambda` is abelian, hence amenable, and acts freely,
so `amenable-orbit-full-group-subgroups-are-sofic` (its Corollary) makes every
subgroup of `[[Lambda ~ X]] ≅ 𝒫` sofic.

**Infinite.** Freeness and perfectness of `X` give, for every `k`, pairwise disjoint
clopen triples `U_k, U_k + a_k, U_k + b_k`. The corresponding 3-cycles commute. Each
is a commutator of two involutions of `[[Lambda ~ X]]` (as in
`research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md`, Lemma 1.1), so
`D(𝒫)` contains an infinite direct sum of copies of `Z/3`. ∎
