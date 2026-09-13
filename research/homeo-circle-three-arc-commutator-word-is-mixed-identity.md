---
rg: 2
id: homeo-circle-three-arc-commutator-word-is-mixed-identity
kind: claim
title: Elements supported in three disjoint arcs give an explicit mixed identity for every group of orientation-preserving circle homeomorphisms containing them
distinct_from:
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4, whether mixed identities can be removed by passing to a finitely presented simple overgroup; this writes down one mixed identity of circle groups such as Thompson's group T.
  fp-simple-kac-moody-lattices-are-mif: that proves some finitely presented simple lattices have no mixed identity; this produces a mixed identity from small supports on the circle.
artifacts:
  - research/artifacts/solve-mixed-identity-undecidable-2026-09-13.md
---

**ESTABLISHED** by `homeo-circle-three-arc-mixed-identity-proof`.

Here `supp(g) = {p : g(p) != p}` and `[g, h] = g h g^-1 h^-1`.

**Circle version.** Let `G <= Homeo+(S^1)`. Let `A_1, A_2, A_3` be pairwise
disjoint open arcs, met in this cyclic order, and let `a_i in G` be nontrivial
with `supp(a_i) ⊆ A_i`. In `G * <x>` put

```text
s_ij = [a_i, x a_j x^-1],        w = [[s_12, s_21], s_33].          (CA1)
```

Then `w != 1` in `G * <x>`, and `w(g) = 1` for every `g in G`. So `w` is a
mixed identity of `G`.

**Interval version.** Let `G <= Homeo+([0,1])`, and let `a_1, a_2 in G` be
nontrivial with every point of `supp(a_1)` to the left of every point of
`supp(a_2)`. Then `[s_12, s_21]` is a mixed identity of `G`.

**Consequences.** Thompson's groups `F` and `T` are not MIF: both contain
nontrivial elements supported in any given open dyadic interval or arc (route,
Step 6). For `T` this is known. Belk--Fournier-Facio--Hyde--Zaremsky
(arXiv:2503.21882v2, extracted text on MSI, l.162–163) write that "Thompson's
group T is lawless but not MIF [LBMB22b, Proposition 4.7]". The citation is
Le Boudec--Matte Bon, *Triple transitivity and non-free actions in dimension
one*, J. Lond. Math. Soc. (2) 105 (2022). Their Proposition 4.7 was not read
here; the word (CA1) may differ from theirs. No novelty is claimed.

**Use.** `thompson-t-mixed-identity-problem-is-decidable` decides which words
are mixed identities of `F` and `T`; this claim shows that set is nontrivial.
