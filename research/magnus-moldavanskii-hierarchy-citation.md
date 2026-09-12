---
rg: 2
id: magnus-moldavanskii-hierarchy-citation
kind: route
title: Import the Freiheitssatz, Magnus's generalized word problem and the Magnus--Moldavanskii hierarchy
target: magnus-moldavanskii-hierarchy-with-decidable-edges
requires: []
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

Citation import. Read on 2026-09-12 from Linton--Nyberg-Brodda, *The theory of
one-relator groups: history and recent progress*, arXiv:2501.18306:
- Theorem 1.3.1 (Magnus's Freiheitssatz, [Mag30, §1]);
- Theorem 1.3.6 and §1.3.3 (Magnus 1932, the generalized word problem for Magnus
  subgroups);
- §1.5.4 (the HNN form, citing McCool--Schupp [MS73, Theorem 1]);
- Theorem 1.5.8 (Moldavanskii [Mol67]).

The survey was extracted on MSI; the quoted wording is in the linked artifact.
Not reproved here, and there is no Lean counterpart.

## What is load-bearing

- **Freeness on the displayed basis.** A bijection between two subsets of
  generators, each omitting a letter of the relator, induces an isomorphism of
  the Magnus subgroups. This is what makes the hierarchy steps HNN extensions.
- **Decidable membership.** It is what the general decidable-edge permanence
  premise needs.

The consumers use nothing else from the import.
