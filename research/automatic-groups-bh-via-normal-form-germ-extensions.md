---
rg: 2
id: automatic-groups-bh-via-normal-form-germ-extensions
kind: route
title: Normal-form germ extensions that meet the Belk--Hyde--Matucci hypotheses would put every automatic group in the permutational Boone--Higman class
target: automatic-groups-satisfy-boone-higman
requires:
  - automatic-groups-embed-in-corner-germ-extensions
  - germ-complex-and-bux-gonzalez-morse-inputs
  - permutational-boone-higman-iff-full-cantor-hosts
  - type-a-action-gives-boone-higman-for-subgroups
artifacts:
  - research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md
---

Let `G` be automatic. Take `G' >= G`, `L`, `B` and `Γ` as in
`automatic-groups-embed-in-corner-germ-extensions`.

1. **Γ is finitely presented.** By (E1)–(E4), Belk--Hyde--Matucci arXiv:2407.03149,
   `cor:MainFinitenessCorollary` at `n = 2`, applies (read at source; the germ-complex setup
   is quoted in `germ-complex-and-bux-gonzalez-morse-inputs`). Its three hypotheses are
   exactly (E3), (E2) and (E4).
2. **Γ is full and clopen transitive.** It is full by its definition in (E1), and clopen
   transitive because it contains `B`, by (E5).
3. **Γ ∈ B_A.** `permutational-boone-higman-iff-full-cantor-hosts`, direction (2 => 1), puts
   `Γ` in `B_A`. So `G <= G' <= Γ` lies in `B_A`.
4. **Conclusion.** `type-a-action-gives-boone-higman-for-subgroups` embeds `G` in a finitely
   presented simple group. ∎

**Status of the steps.**
- Steps 1–4 are formal applications of results on main or read at source.
- All the mathematical difficulty is in the OPEN premise.
