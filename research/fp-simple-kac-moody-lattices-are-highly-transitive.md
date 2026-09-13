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
