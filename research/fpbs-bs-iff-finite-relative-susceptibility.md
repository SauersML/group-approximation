---
rg: 2
id: fpbs-bs-iff-finite-relative-susceptibility
kind: claim
title: With an amenable wq-normal subgroup strict thresholds mean finite relative susceptibility above p_c
distinct_from:
  fpbs-nonuniqueness-parameter-criterion: that reduces p_c<p_u on one graph to a parameter with infinitely many infinite clusters; this reduces it, for groups with an infinite amenable wq-normal subgroup H, to a parameter above p_c where the expected number of points of H in the root cluster is finite, a one-subgroup two-point summability statement.
  fpbs-critical-l2-implies-nonuniqueness: that is Hutchcroft's sufficient operator criterion over the whole graph; this is an exact equivalence that only sums the two-point function over the subgroup H.
artifacts:
  - research/artifacts/fpbs/docs/relative-susceptibility-reduction.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated, `H <= Gamma` an infinite
amenable wq-normal subgroup, `G = Cay(Gamma,S)` for any finite generating set,
and `chi^H_p = E_p|K_o ∩ H| = sum_{h in H} tau_p(o,h)`. The following are
equivalent.

1. `p_c(G) < p_u(G)`.
2. `chi^H_p < infinity` for some `p > p_c(G)`.
3. For some `p > p_c(G)` and `c > 0`, `P_p(|K_o ∩ H| >= n) <= e^(-cn)` for all
   `n`.

So for this class the Benjamini--Schramm conjecture is exactly **relative
subcriticality just above p_c**: slightly supercritical clusters must meet `H`
only finitely often, with finite mean. The conjecture is thereby reduced to a
two-point summability statement along one amenable subgroup rather than a
merger estimate over the whole graph.

The class contains every group with an infinite amenable normal subgroup
(groups with infinite center such as braid groups, spherical Artin groups and
`Gamma x Z^k`; Seifert-fibred 3-manifold groups; lamplighters; `Z^d x| SL_d(Z)`),
and commensurated amenable subgroups such as `<a>` in non-solvable
Baumslag--Solitar groups. None of the normal cases is acylindrically hyperbolic,
so `fpbs-sc-choi-seo` supplies none of them.

Section 3 of `research/artifacts/fpbs/docs/relative-susceptibility-reduction.md`
contains the proof.

DERIVATION
fpbs-bs-iff-finite-relative-susceptibility-proof
