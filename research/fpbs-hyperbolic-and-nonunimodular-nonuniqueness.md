---
rg: 2
id: fpbs-hyperbolic-and-nonunimodular-nonuniqueness
kind: claim
title: Hyperbolic and nonunimodular quasi-transitive graphs have a nonuniqueness phase
artifacts:
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
  - research/artifacts/fpbs/creative-branches.md
---

Two established special cases of `fpbs-benjamini-schramm-universal`, both due
to Hutchcroft.

1. **Hyperbolic.** arXiv:1804.10191, *Percolation on hyperbolic graphs*:
   Bernoulli bond percolation on any nonamenable, Gromov hyperbolic,
   quasi-transitive graph has a phase with infinitely many infinite clusters,
   that is `p_c<p_u`. The same proof gives the triangle condition
   `nabla_{p_c}<infinity` at criticality.
2. **Nonunimodular.** arXiv:1711.02590, *Non-uniqueness and mean-field
   criticality for percolation on nonunimodular transitive graphs*: whenever
   the automorphism group of a quasi-transitive graph has a nonunimodular
   quasi-transitive subgroup, there is a nonempty phase with infinite light
   clusters, hence `p_c<p_h<=p_u`. This covers `T_k x Z^d`, a `k`-regular tree
   times a Euclidean lattice.

These are graph-level results. They do not carry the every-generating-set
quantifier of the goal for an arbitrary nonamenable group; they carry it only
for groups all of whose Cayley graphs satisfy the geometric hypothesis. The
result that does carry the full quantifier for a class is `fpbs-sc-choi-seo`,
Choi--Seo for acylindrically hyperbolic groups.

**Attribution correction.** Section 3 of
`research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md` cites
arXiv:1804.10191 for both halves, including the `T_k x Z^d` example. The
nonunimodular half and that example are arXiv:1711.02590; the hyperbolic paper
does not mention nonunimodularity in its abstract. Both identifiers were
checked against the arXiv API on 2026-09-09.

Status records imported theorems, not independent mathematical verification.
