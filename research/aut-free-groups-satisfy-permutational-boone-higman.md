---
rg: 2
id: aut-free-groups-satisfy-permutational-boone-higman
kind: claim
title: Every Aut(F_n) embeds in a finitely presented simple twisted Brin--Thompson group
distinct_from:
  relative-automorphism-action-is-highly-transitive: that imports one input of the proof, the high transitivity of the action of the relative automorphism group; this imports the paper's main embedding theorem and its universality and free-product corollaries.
  twisted-brin-thompson-finite-presentation-criterion: that is the criterion for a twisted Brin--Thompson group to be finitely presented; this is the theorem that every Aut(F_n) embeds in such a finitely presented simple group.
artifacts:
  - research/artifacts/boone-higman-frontier-2026-09-12.md
---

**ESTABLISHED (literature import).**

> **Theorem A (Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2).**
> For each n, the group Aut(F_n) embeds in a finitely presented simple group,
> and hence satisfies the Boone--Higman conjecture.

It holds in the permutational form, where the simple group is a twisted
Brin--Thompson group. The abstract also states:

- "finitely presented twisted Brin--Thompson groups are universal among
  finitely presented simple groups that are highly transitive" (Corollary D);
- "satisfying the permutational Boone--Higman conjecture is closed under free
  products" (Corollary F).

Corollary B yields Boone--Higman for:
- the (extended) mapping class groups of finite-type surfaces with boundary or
  a puncture;
- the braid groups B_n;
- Artin groups of types B_n = C_n, D_n, I_2(m) and Ã_n;
- loop braid groups, extended loop braid groups and ribbon braid groups.

## Scope

Still open, per arXiv:2306.16356v3, Remark 5.4:
- mapping class groups of closed surfaces of genus at least 3;
- Out(F_n) for n ≥ 3;
- exceptional spherical and most Euclidean Artin groups.

Nothing is reproved here, and there is no Lean counterpart.
