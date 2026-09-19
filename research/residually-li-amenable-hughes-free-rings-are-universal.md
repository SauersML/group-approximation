---
rg: 2
id: residually-li-amenable-hughes-free-rings-are-universal
kind: claim
title: For residually-(locally indicable and amenable) groups the Hughes-free division ring exists and is Cohn-universal (Jaikin-Zapirain 2021)
distinct_from:
  fsp-graph-of-rings-and-linnell-extension-imports: that imports existence statements and FSP's graph-of-rings embedding; this imports universality in Cohn's sense (a specialization to every epic division ring), which is strictly stronger and known on a narrower class.
  hughes-extension-lemma-and-fsp-universal-field-imports: that imports Hughes's extension lemma and FSP's universal field of fractions of graphs of rings; this is Jaikin-Zapirain's universality theorem for residually-(LI amenable) groups, a different source and a different statement.
  flat-weak-bass-holds-exactly-for-locally-indicable-groups: that node's item 1(ii) invokes universality of D_{Q[G]} for every locally indicable G; this records the published statement, whose scope is residually-(LI amenable) groups only.
---

Let `G` be residually-(locally indicable and amenable): for every `1 != g in G` there are a
locally indicable amenable group `A` and a homomorphism `G -> A` not killing `g`. Let `E` be a
division ring. Then the Hughes-free division `E[G]`-ring `D_{E[G]}` exists, and it is the
universal division ring of fractions of `E[G]` in Cohn's sense. That is, `E[G] -> D_{E[G]}` is
injective and epic, and for every epic division `E[G]`-ring `L` there is a specialization
`D_{E[G]} ~> L`.

A specialization `U ~> L` is a subring `R_0 ⊆ U` containing the image of `E[G]`, with a ring
homomorphism `alpha: R_0 -> L` compatible with the maps from `E[G]`, such that every element of
`R_0 \ ker(alpha)` is a unit of `R_0` (Cohn, *Skew Fields*, CUP 1995, Ch. 4).

Source: A. Jaikin-Zapirain, *The universality of Hughes-free division rings*, Selecta Math.
(N.S.) 27 (2021), no. 4, Paper No. 74, DOI 10.1007/s00029-021-00691-w. The abstract states it
verbatim; see the citation route.

**Scope warning.** The abstract says that existence of `D_{E*G}` "for an arbitrary locally
indicable group G is still an open question" for crossed products. It proves universality only
for the residually-(LI amenable) class. Universality of `D_{Q[G]}` for all locally indicable
`G` is not claimed there.

**ESTABLISHED 2026-09-18** by [[residually-li-amenable-hughes-free-universality-citation]].
This is a literature import. The body of the paper was not read, and its theorem number was not
verified.

## Attempts

- 2026-09-18 (swarm-0917-w11-w11-gs-follow): the verbatim abstract was obtained from the Crossref
  record of the DOI. The UAM repository PDF returned 503.
