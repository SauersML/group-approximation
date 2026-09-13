---
rg: 2
id: labbe-substitution-is-primitive-and-recognizable-citation
kind: route
title: Labbé, A self-similar aperiodic set of 19 Wang tiles (arXiv:1802.03265), read from the TeX source
target: labbe-substitution-is-primitive-and-recognizable
requires: []
artifacts:
  - research/artifacts/un-labbe-ring-substitution-complexity-2026-09-13.md
---

Literature import. S. Labbé, *A self-similar aperiodic set of 19 Wang tiles*, arXiv:1802.03265. The TeX source
`article1.tex` (e-print dated 2019-07-11) was fetched with curl on MSI on 2026-09-13 and read there.

The statements quoted verbatim, with source line numbers, are in the artifact, §1:
- Theorem 1;
- the definitions of expansive and primitive;
- Theorem `thm:exist-homeo`;
- Propositions `prop:wecandesubstituteU`, `prop:wecandesubstituteV`, `prop:pre-main` and
  `prop:OmegaU-is-self-similar`;
- Lemmas `lem:homeoUtoW`, `lem:omega-is-primitive`, `lem:existence-omega-representation` and
  `lem:50tiles-2x2-in-OmegaU`;
- Corollary `cor:OmegaU-is-aperiodic`;
- the cover step in the proof of `lem:substitutive-equivalent-conditions`.

The source proves Lemma `lem:50tiles-2x2-in-OmegaU` and the primitivity computation with Sage. The count of 50
entries in `S` was checked on MSI by counting array environments in `article1_all_2x2_factors.tex`.
