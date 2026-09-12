---
rg: 2
id: strict-automata-closed-under-host-manipulations-proof
kind: route
title: Conjugate by bijective right translations, act coset by coset, and compare images of composites
target: strict-automata-closed-under-host-manipulations
requires: []
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

Section 3 of the artifact.

1. **Conjugation:** `R_c` is a bijective automaton, and
   `R_c tau R_(c^-1)(x)(g) = mu((x(gcmc^-1))_m)`.
2. **Subgroups:** an automaton with memory in `H` acts independently on the left `H`-cosets, each
   a copy of the `H`-automaton. Transport along `alpha` is this case for `alpha(G)`, composed with
   the isomorphism `alpha`.
3. **Composites:** composites of injective maps are injective.
   - The image of `tau o rho` lies in `tau(A^G)`.
   - The image of `rho o tau` is `rho(tau(A^G))`. It is proper when `rho` is onto, and otherwise it
     lies in `rho(A^G)`.
4. **Products:** the image lies in `tau(A^G) x B^G`.
