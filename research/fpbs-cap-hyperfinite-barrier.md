---
rg: 2
id: fpbs-cap-hyperfinite-barrier
kind: claim
title: In the stated Burnside range all sufficiently reliable hyperfinite connectors lie in one finite cyclic subgroup
root: true
invalidates:
  - fpbs-dead-hyperfinite-small-average-defect
---

**Statement.** Theorem 5.1 of the connector-capacity note. Fix Gamma = B(2,n) with n odd and large
enough for Osin's bounded-word embedding theorem, let rho_n < 1 be the norm of the symmetric four-point
convolution operator on the standard Cayley graph, let L_n be Osin's word-length bound, and set
epsilon_n = (1-rho_n)/L_n > 0. Then for every free p.m.p. Gamma-action and every hyperfinite subrelation
S <= R, the set A_S = {g : Delta_S(g) < epsilon_n} of sufficiently reliable connectors is contained in a
single cyclic subgroup of order n; in particular |A_S| <= n. Corollary 5.2 turns this into a uniform
mean-defect obstruction: distinct connector lists of length k have average defect at least
epsilon_n(1 - n/k). The constant epsilon_n is an existence constant and no numerical value is asserted.

The argument: if u,v in A_S do not commute, Osin gives r,s of {u,v}-word length at most L_n generating a
copy of B(2,n), so Delta_S(r) and Delta_S(s) are both below 1-rho_n by subadditivity. But the regular
representation restricted to <r,s> is a sum of regular representations of that subgroup, and the
four-point bound forces Delta_S(r)+Delta_S(s) >= 2(1-rho_n). So A_S is abelian, hence inside a
centralizer, which is cyclic of order n.

**Proof location.** `research/artifacts/fpbs/connector-capacity.md`, Section 5, on the regular-bound and
subadditivity of Section 4; response 26.

**Imported inputs.** Osin, *Uniform non-amenability of free Burnside groups*, arXiv:math/0404073v1,
Theorem 2.7 for the uniformly short embedded Burnside bases and Lemma 2.2 for cyclic centralizers. The
note is explicit that it uses these statements and not the stronger fixed universal-word assertion that
the paper discusses only as an unproved announcement. Donoso-Echenique-Silva, arXiv:2608.20472v1,
Lemma 2.4, for the same centralizer fact. Both identifiers resolve with matching titles and authors.

**Finite-replay evidence.** `research/artifacts/fpbs/connector-capacity-checks.json` via
`scripts/replay_connector_capacity.py`: status passed, with 77,952 restriction-defect cases, 64,960
repaired labelings, 13,590 moment entries, 7,308 defect-subadditivity checks and 6,090 adaptive root
families over a finite S_3 action. The file lists measurable partition separation in infinite actions,
hyperfinite exhaustion, regular-representation limits and Osin's bounded-word theorem itself among the
things it does not verify.

**Evidence level.** Written deduction from two verified published inputs, with a passing finite replay of
the defect algebra. Not refereed, not formally verified. This is a barrier result: it says the
hyperfinite-connector strategy for large odd Burnside groups cannot supply more than a bounded cyclic
supply of reliable connectors, which is why `fpbs-cap-construction-target` remains OPEN.
