---
rg: 2
id: kun-thom-nonsofic-wreath
kind: claim
title: Kun--Thom nonsofic generalized wreath products over infranormal Kazhdan pairs
distinct_from:
  wreath-not-sofic: that node is about *this repository's* wreath candidate and stays open pending an identification check; this one is the external theorem about Kun--Thom's own explicit groups
  openai-leavitt-unit-nonsofic: that is the announced, unrefereed OpenAI result about the binary Leavitt unit group; this is a refereeable arXiv preprint by named authors about wreath products
  nonsofic-hyperbolic-group: that asks for a nonsofic group from a different mechanism entirely; this records the (T)-compression mechanism's strongest published output
---

Kun--Thom, *Nonsofic wreath products of residually finite groups*,
arXiv:2608.06222v1 (2026-08-06, 16 pp), prove unconditionally:

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

**Trust surface.** This is an arXiv preprint, not yet refereed.  It is
nevertheless imported as established because it is a self-contained
mathematical argument by named authors in their own area, verified here
from the PDF (not the HTML render, which returned wrong content), and
because its own dependency on the announced OpenAI result is only
inspirational: Theorem A is proved from Kun's expander decomposition
(arXiv:1606.04471) and Kun--Thom (arXiv:1901.03963), both of which predate
the announcement.  Note that the paper contains **no** operator-norm, MF, or
corona content, so it raises no priority conflict with the non-MF manuscript.
