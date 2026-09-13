---
rg: 2
id: commuting-hamiltonians-on-small-set-expanders-in-np-citation
kind: route
title: Import Aharonov--Eldar on commuting Hamiltonians over small-set bipartite expanders
target: commuting-hamiltonians-on-small-set-expanders-in-np
requires: []
artifacts:
  - research/artifacts/qpcp-landscape-sources-2026-09-12.md
---

Literature import. Aharonov--Eldar, *Commuting local Hamiltonians on expanders,
locally testable quantum codes, and the qPCP conjecture*, arXiv:1301.3407v1.
Theorem numbers were read from the v1 PDF (pp. 5--6), and the definition from the
TeX source (`def:expbi`), on 2026-09-12:

- Definition (bi-partite small-set expansion): every `S subseteq R` with `|S|<=k`
  has `|Gamma(S)|>=|S| D_R (1-eps)`;
- Theorem 1: (AE1), including "In particular, the gamma(eps)-approximation
  problem of CLH(k,d) on such eps small-set bi-partite expander graphs is in NP";
- Theorem 2: (AE2).

The commuting-family consequence is the contrapositive of Theorem 1 at promise gap
`gamma>2kd eps`. The NLTS remark uses only the constant-depth clause of Theorem 1
and Theorem 1 of arXiv:2206.13228v4. Section 2 of the linked artifact quotes the
source.
