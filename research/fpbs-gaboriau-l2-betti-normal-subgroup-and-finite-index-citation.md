---
rg: 2
id: fpbs-gaboriau-l2-betti-normal-subgroup-and-finite-index-citation
kind: route
title: Import Gaboriau's Theorem 6.8 and the finite-index formula from Invariants l2 de relations d'equivalence et de groupes
target: fpbs-gaboriau-l2-betti-normal-subgroup-and-finite-index
requires: []
---

Citation import, not a reproof. Source: D. Gaboriau, *Invariants l2 de relations d'équivalence et de groupes*,
Publ. Math. IHES 95 (2002), 93--150 (numdam PMIHES_2002__95__93_0).

- **Theorem 6.8**, verbatim (Section 6, with proof): "Théorème 6.8. — Soit 1→N→Γ→Λ→1 une suite exacte où N et Λ
  sont des groupes infinis. Si β1(N) est fini, alors β1(Γ)=0."
- **Gaboriau's own contrapositive**, verbatim (introduction): "Si Γ est un groupe qui vérifie β1(Γ)≠0 et N est un
  sous-groupe normal tel que β1(N) soit fini (par exemple N de type fini), alors N est fini ou d'indice fini."
- **Finite index**, verbatim (table of properties of l2-Betti numbers of groups, Section 1): "Si Λ est d'indice fini
  dans Γ βn(Λ)=[Γ:Λ].βn(Γ)".
- The same paper gives the identification of the Betti numbers of a group with those of any free p.m.p. orbit
  relation, verbatim: "Corollaire 3.16. — Si R est produite par une action libre de Γ, préservant la mesure de
  probabilité, alors Γ et R ont les mêmes nombres de Betti ℓ2." It also gives the cost inequality, verbatim:
  "Corollaire 3.23. — On a une inégalité C(R)−1 ≥ β1(R)−β0(R)". The graph already imports these in
  `fpbs-amen2-betti-cost-input`; they are recorded here only as a cross-check.

All sentences were read on 2026-09-17 from the numdam PDF, extracted with pypdf (the extraction drops some spaces
and accents, which were restored). The groups in the paper are countable discrete groups; no finite generation is
assumed in Theorem 6.8 or in the index formula.
