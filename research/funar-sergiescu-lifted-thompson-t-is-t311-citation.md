---
rg: 2
id: funar-sergiescu-lifted-thompson-t-is-t311-citation
kind: route
title: Import Remark 2.1 and the identification of the lift group with T_(3,1,1) from Funar-Sergiescu, and recheck by exact lifting
target: funar-sergiescu-lifted-thompson-t-is-t311
requires: []
---

Direct reading of arXiv:0802.2996v2 (Funar and Sergiescu, *Central
extensions of the Ptolemy-Thompson group and quantized Teichmüller theory*), 2026-09-19.  Text was extracted with `pypdf`.
The passages read were Remark 2.1, Section 2.4 (the proof of Proposition
2.1), Section 2.5 (the groups `T_(n,p,q)`, Lemma 2.2, and the proof of
Proposition 2.2), and the introduction.  The verbatim quotes are in the
target.

Independent check.  `experiments/torus-knot-cover-2026-09-17/lift_relations.py`
does the following:
- stores the Cannon-Floyd-Parry maps as exact piecewise-linear lifts to `R`;
- sets `beta = C^(-1)` and `alpha = C^(-1) B`;
- confirms `A = beta alpha^2`, `B = beta^2 alpha`, `C = beta^2` on the circle,
  with the product `gh = g o h`;
- picks the lifts `a` and `b` with translation numbers `1/4` and `1/3`;
- computes `a^4 = z`, `b^3 = z` and `(ba)^5 = z^3`, and finds that both
  commutator relators lift to the identity.

The output is in `experiments/torus-knot-cover-2026-09-17/output.txt`.  The
completeness of the lifted presentation is the general fact that lifts of a
complete set of relators of `T`, together with centrality of `z`, present a
central extension.  The source states this in Section 2.4.  None of the
consequences in this graph uses completeness: they use only that `a` and `b`
generate `T̄` and satisfy `a^4 = b^3 = z`.
