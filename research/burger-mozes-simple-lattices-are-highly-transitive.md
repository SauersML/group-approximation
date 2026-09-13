---
rg: 2
id: burger-mozes-simple-lattices-are-highly-transitive
kind: claim
title: The finitely presented simple Burger--Mozes groups are highly transitive, hence mixed-identity-free, and satisfy permutational Boone--Higman
distinct_from:
  burger-mozes-infinitely-transitive-tree-groups: that imports the Burger--Mozes structure theory of locally infinitely transitive tree groups; this imports the high transitivity of their finitely presented simple lattices, a statement about abstract permutation actions.
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C; this supplies one class of finitely presented simple groups to which its (iii) applies.
---

**ESTABLISHED (literature import).** Every finitely presented simple group `Λ`
of Burger--Mozes [BM97] is highly transitive, hence MIF, and therefore
satisfies the permutational Boone--Higman conjecture, as does every subgroup of
`Λ`.

**Source.** Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, Remark
3.5, extracted PDF text on MSI (`bh-reviewer/2503.21882.txt`), l.745--760:

> "The finitely presented simple Burger–Mozes groups Λ from [BM97] are not
> “obviously” highly transitive and MIF, but it turns out that they do have
> these properties; we thank Adrien Le Boudec for this argument. By
> construction, Λ is dense in a subgroup of the automorphism group of a locally
> finite tree T that is 2-transitive on the boundary [BM97, Remark 5]. It
> follows from density that the action of Λ on ∂T is extremely proximal. By
> [FLMMS22, Theorem B] it suffices to show that the action of Λ on ∂T is
> topologically free. Suppose that this is not the case; this means that there
> exists a proper open set U ⊂ ∂T such that the subgroup ΛU of elements of Λ
> supported on U is non-trivial. By extreme proximality, there exist
> g1, g2, g3 ∈ Λ such that the giU are pairwise disjoint. Then the
> gi-conjugates of ΛU generate a direct product. However, Λ has cohomological
> dimension 2, so it cannot contain a direct product of three non-trivial
> groups. This shows that Burger–Mozes groups are highly transitive, hence MIF,
> and thus satisfy PBH. In fact, this latter fact was recently established, in
> a completely different way, in [BLIW]."

**Consequences in this graph.**
- Through `fp-simple-highly-transitive-groups-satisfy-pbh` (Theorem C (iii)),
  every subgroup of `Λ` lies in the permutational class.
- In `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh` this removes the
  Burger--Mozes groups as potential counterexamples to BH implying PBH.

**Not re-verified here:** FLMMS22 Theorem B (Fima--Le Maître--Moon--Stalder, *A
characterization of high transitivity for groups acting on trees*, Discrete
Anal. 2022, Paper No. 8), [BM97, Remark 5], and the cohomological dimension
bound. All three are taken from BFFHZ's text.

Citation: `burger-mozes-simple-lattices-are-highly-transitive-citation`.
