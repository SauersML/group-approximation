---
rg: 2
id: rover-nekrashevych-groups-are-highly-transitive
kind: claim
title: A Rover--Nekrashevych group of a countable self-similar group, and each of its nontrivial normal subgroups, acts highly transitively on every boundary orbit
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that is Zaremsky's theorem placing a finitely presented self-similar group in a finitely presented simple Rover--Nekrashevych commutator subgroup; this is a transitivity property of those envelopes, the input that lets them feed the permutational form of the conjecture.
  relative-automorphism-action-is-highly-transitive: that is high transitivity of Aut_S(S*F_n) on the homomorphism set Hom_S(S*F_n,S); this is high transitivity of Rover--Nekrashevych groups on orbits in the boundary of a regular rooted tree.
  rover-nekrashevych-finite-presentation-criteria: that records when V_d(H) and its commutator subgroup are finitely presented and simple; this records their permutation-theoretic property, high transitivity on boundary orbits, with no finiteness hypothesis.
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

Fix `d >= 2`, the alphabet `X = {1,...,d}`, the rooted tree `T_d = X^*` and its
boundary `C = X^N`. Let `G <= Aut(T_d)` be a countable self-similar group: every
section `g|_u` of every `g in G` lies in `G`.

The **Rover--Nekrashevych group** `V_d(G)` is the group of homeomorphisms `h` of
`C` for which there are partitions `C = u_1 C ⊔ ... ⊔ u_m C = v_1 C ⊔ ... ⊔ v_m C`
into cones and elements `g_1, ..., g_m in G` with

```text
h(u_i w) = v_i g_i(w)      for all i and all w in C.
```

**ESTABLISHED.** Let `O` be a `V_d(G)`-orbit in `C`.
1. `O` is countably infinite, and `V_d(G)` acts on `O` faithfully and highly
   transitively.
2. Every nontrivial normal subgroup `N` of `V_d(G)` acts on `O` faithfully and
   highly transitively. In particular `[V_d(G), V_d(G)]` does.

Consequently every finitely presented simple group of the form `[V_d(G), V_d(G)]`,
for `G` countable and self-similar, is highly transitive. That is the
hypothesis of Belk--Fournier-Facio--Hyde--Zaremsky Theorem C
(`fp-simple-highly-transitive-groups-satisfy-pbh`).

**Credit: known.** Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2,
Remark 3.5, read from the extracted PDF text on MSI
(`/scratch.global/sauer354/bh-reviewer/2503.21882.txt`). They list as "obviously"
highly transitive "any finitely presented simple groups of homeomorphisms of the
Cantor space {1,...,n}^N that contain the commutator subgroup of the
Higman–Thompson group V_n. In particular this includes Thompson's group V itself,
along with all finitely presented commutator subgroups of Röver–Nekrashevych
groups V_n(G) [Nek18, Theorem 4.7]."

The route `rover-nekrashevych-groups-are-highly-transitive-proof` is an
independent elementary verification of the orbit and normal-subgroup steps. It
claims no priority.
