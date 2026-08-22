---
rg: 2
id: kun-thom-nonsofic-wreath
kind: claim
title: Kun--Thom nonsofic generalized wreath products over infranormal Kazhdan pairs
distinct_from:
  wreath-not-sofic: that node is about *this repository's* wreath candidate and stays open pending an identification check; this one is the external theorem about Kun--Thom's own explicit groups
  openai-leavitt-unit-nonsofic: that is the first nonsofic group, about the binary Leavitt unit group, and this paper's abstract says it builds on it; this is the later generalized-wreath theorem extracted from the same mechanism, and it is not an independent existence proof
  nonsofic-hyperbolic-group: that asks for a nonsofic group from a different mechanism entirely; this records the (T)-compression mechanism's strongest published output
---

Kun--Thom, *Nonsofic wreath products of residually finite groups*,
arXiv:2608.06222 (v1 2026-08-06; v3 2026-08-20 with an updated Theorem A whose
hypotheses are unchanged and whose conclusion also covers the group double,
recorded in `kt-pair-group-double-is-nonsofic`; 16 pp), prove unconditionally:

> **Theorem A.** Let `Gamma` be an infranormal but not normal subgroup of `G`,
> and suppose that both `Gamma` and `G` have Kazhdan's property (T).  Then
> `(Z/2Z) wr_(G/Gamma) G` is not sofic.

Here `Gamma` is **infranormal** in `G` when its compression semigroup
`P_Gamma={g in G : g Gamma g^(-1) <= Gamma}` generates `G` as a group, and
`(Z/2Z) wr_(G/Gamma) G` denotes `(directSum_(G/Gamma) Z/2Z) semidirect G`
with `G` permuting coordinates through the coset action.

The hypotheses are realized by an explicit pair:

> **Theorem E.** Let `q` be a prime power and let `r,d>=3`.  Put
> `R_+=F_q[x_1,...,x_d]` and `R=F_q[x_1^(±1),...,x_d^(±1)]`, and let `SL_d(Z)`
> act on `R` by monomial substitutions.  Then `Gamma=EL_r(R_+)` and
> `G=EL_r(R) semidirect SL_d(Z)` are residually finite Kazhdan groups,
> `Gamma` is infranormal but not normal in `G`.

Two further statements from the same paper are used elsewhere in this graph:

> **Theorem C.** `Gamma` infranormal in `G`, both Kazhdan, `G action (X,mu)`
> a sofic p.m.p. action; then the fixed-point algebra `L^infinity(X)^Gamma`
> is `G`-invariant.

> **Corollary D.** Under Theorem C's hypotheses with `Gamma` not normal, the
> generalized Bernoulli action `G action (K,kappa)^(G/Gamma)` is not sofic,
> for every nontrivial standard probability space `(K,kappa)`.

**Downstream in this graph.** Beyond the wreath program, Theorems A and E
feed `commuting-counterexample-from-kun-thom-pair`: the coset action
`G ↷ G/Γ` of Theorem E's pair is nonsofic (`coordinate-action-not-sofic`),
and running it through the diagonal-coset construction closes GKP Question
4.2 in the negative (`commuting-sofic-actions-need-not-combine`) — the first
external open question this preprint settles through this repository.

**Priority. This paper is not the first nonsofic group and must never be
cited as one.** Its own abstract opens: "This work builds on the breakthrough
of OpenAI in finding the first nonsofic group. We analyze the underlying proof
mechanism and find further applications." The first nonsofic group is
`openai-leavitt-unit-nonsofic`, announced 2026-08-01; this preprint was posted
2026-08-06. An earlier version of this node argued that the dependency was
"only inspirational" because both inputs -- Kun's expander decomposition
(arXiv:1606.04471, 2016) and Kun--Thom (arXiv:1901.03963, 2019) -- predate the
announcement. That conflates the ingredients with the argument: infranormality
is the compression-semigroup form of the selection step the OpenAI chapter
introduced, and the authors say as much themselves. What makes this graph's
nonsoficity independent of any external text is not this preprint but
`one-sided-compression-nonsofic-criterion` and `universal-leavitt-el4-nonsofic`,
both kernel-checked here.

**Trust surface.** This is an arXiv preprint, not yet refereed. It is
nevertheless imported as established because it is a self-contained
mathematical argument by named authors in their own area, verified here
from the PDF (not the HTML render, which returned wrong content). Note that
the paper contains **no** operator-norm, MF, or corona content, so it raises
no priority conflict with the non-MF manuscript.
