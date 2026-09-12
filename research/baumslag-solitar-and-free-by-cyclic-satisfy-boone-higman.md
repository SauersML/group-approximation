---
rg: 2
id: baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman
kind: claim
title: All Baumslag--Solitar groups and all free-by-cyclic groups embed in finitely presented simple groups
distinct_from:
  fp-self-similar-groups-embed-in-fp-simple-groups: that covers finitely presented self-similar inputs, which are residually finite; this covers groups acting on locally finite trees, including non-residually-finite Baumslag--Solitar groups such as BS(2,3).
  hyperbolic-groups-satisfy-boone-higman: that covers hyperbolic inputs; this covers Baumslag--Solitar groups, which are not hyperbolic, and free-by-cyclic groups, many of which are not hyperbolic.
artifacts:
  - research/artifacts/boone-higman-frontier-2026-09-12.md
---

**ESTABLISHED (literature import).** Every Baumslag--Solitar group and every
free (finite rank)-by-cyclic group satisfies `boone-higman-conjecture`.

Source: K.-U. Bux, C. Llosa Isenrich, X. Wu, *On the Boone--Higman Conjecture
for groups acting on locally finite trees*, arXiv:2408.05673 (v2, 24 January
2025). Abstract, verbatim: "We develop a method for proving the Boone--Higman
Conjecture for groups acting on locally finite trees. As a consequence, we
prove the Boone--Higman Conjecture for all Baumslag--Solitar groups and for all
free(finite rank)-by-cyclic groups, solving it in two cases that have been
raised explicitly by Belk, Bleak, Matucci and Zaremsky."

The survey arXiv:2306.16356v3, Remark 5.4, records that items (4) and (8) of
its Problem 5.3 "are fully handled", and that the same paper handles
"Euclidean triangle Artin groups".

## Scope

The BLIW method applies to groups acting on locally finite trees under the
paper's hypotheses. Only the two named families, plus the triangle Artin case
the survey reports, are imported here. Nothing is reproved, and there is no
Lean counterpart.
