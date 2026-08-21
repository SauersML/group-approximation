---
rg: 2
id: algebraic-compact-action-group-factor-compiler
kind: claim
title: Pontryagin duality compiles a non-CE algebraic crossed product into a non-hyperlinear semidirect product
artifacts:
  - research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md
distinct_from:
  non-ce-property-t-equivalence-relation-exists: that supplies a non-CE relation factor but does not identify it with or embed it into a canonical discrete group factor; this is the formal compiler once an algebraic compact-abelian crossed-product envelope is supplied.
  thom-central-corner-criterion: that realizes finite scalar cocycle sectors as central-character corners of a central extension; this uses untwisted Pontryagin duality for a compact abelian algebraic action and produces an ordinary semidirect-product group factor.
---

Let `K` be a compact second-countable abelian group, let `Lambda` be a
countable discrete group acting continuously on `K` by group automorphisms,
and let `A=K-hat` be the countable discrete Pontryagin dual with the dual
`Lambda`-action.  There is a canonical trace-preserving isomorphism

```text
L^infinity(K) rtimes Lambda ~= L(A rtimes Lambda).       (ACGF1)
```

Consequently, if a non-Connes-embeddable tracial von Neumann algebra `N`
embeds trace-preservingly into the left side of `(ACGF1)`, then the discrete
semidirect product `A rtimes Lambda` is non-hyperlinear.  If that semidirect
product is finitely generated and recursively presented, Higman's embedding
theorem embeds it in a finitely presented group, which is also non-hyperlinear
because hyperlinearity passes to subgroups.

