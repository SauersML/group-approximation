---
rg: 2
id: three-address-binary-injective-rules-are-balanced-proof
kind: route
title: Rectangle relation, one glued involution, complementary insensitivity, and an invisible double flip
target: three-address-binary-injective-rules-are-balanced
requires:
  - sofic-groups-are-surjunctive
  - bijective-ca-preserve-uniform-bernoulli-measure
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

Artifact, Section 2: Lemma 6, Corollary 7 and Theorem 8.

- **Surjunctivity of amenable subgroups.** The prerequisite covers these, since amenable groups are
  sofic. When `<M>` is amenable, the automaton restricted to that subgroup is injective, hence
  surjective, so the whole automaton is bijective. By
  `bijective-ca-preserve-uniform-bernoulli-measure`, or directly by counting over the finite fibers
  of a bijection on finite windows, the rule is then balanced. The artifact uses the measure argument.
- **The rest.** Everything else is a finite check on the eight sites
  `1, a, b, ab, b^-1, b^-1 a, a b^-1, a b^-1 a`. Every coincidence among them makes `<a, b>` cyclic,
  dihedral or abelian.
