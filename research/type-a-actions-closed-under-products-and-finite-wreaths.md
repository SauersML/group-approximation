---
rg: 2
id: type-a-actions-closed-under-products-and-finite-wreaths
kind: claim
title: Type (A) actions pass to finite direct products and to wreath products with finite symmetric groups
distinct_from:
  type-a-action-gives-boone-higman-for-subgroups: that is Zaremsky's embedding payoff for the subgroups of one actor; this is a permanence statement that builds new actors from old ones and supplies no envelope by itself.
  two-transitive-action-reduces-type-a-to-two-clauses: that shortens the type (A) test for one two-transitive action; this constructs type (A) actions for products and finite wreaths, which are not two-transitive once both factors act nontrivially.
artifacts:
  - research/artifacts/bh-type-a-permanence-2026-09-12.md
---

Use the definition in `type-a-action-gives-boone-higman-for-subgroups`: an
action of `Gamma` on a nonempty set `S` is of type (A) when it is faithful,
`Gamma` is finitely presented, every point stabilizer is finitely generated,
and there are finitely many `Gamma`-orbits of two-element subsets of `S`.

(a) **Products.** If `Gamma_1` acts on `S_1` and `Gamma_2` acts on `S_2`, both
of type (A), then `Gamma_1 x Gamma_2` acting on the disjoint union
`S_1 ⊔ S_2`, each factor on its own part, is of type (A).

(b) **Finite wreaths.** If `Gamma` acts on `S` of type (A) and `k >= 1`, then
`Gamma wr S_k = Gamma^k x| S_k`, acting imprimitively on `S x {1,...,k}` by

```text
(gamma, sigma) . (s, i) = (gamma_(sigma(i)) s, sigma(i)),
```

with `(sigma . delta)_j = delta_(sigma^-1(j))` in the semidirect product, is
of type (A).

The proof is elementary and is written in
`type-a-products-finite-wreaths-proof`. Its consumer is
`boone-higman-type-a-class-closed-under-finite-extensions`.

**Credit: not new.** The permanence it serves is known. Belk--Fournier-Facio--Hyde--Zaremsky,
arXiv:2503.21882v2, say that the permutational Boone--Higman property (embedding
in a group with a type (A) action) "is stable under commensurability and direct
products". They cite Zaremsky, arXiv:2405.18354, Proposition 5.6, which was read
through a summarizing fetch, not line by line. The route here is an independent
elementary check of the two constructions, recorded because the graph consumes
them; it claims no priority.
