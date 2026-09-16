---
rg: 2
id: contracting-combings-give-contractible-rips-complexes-citation
kind: route
title: Import Alonso's combing theorem as quoted in Zaremsky's Bestvina–Brady Vietoris–Rips paper
target: contracting-combings-give-contractible-rips-complexes
requires: []
---

Citation import, not a reproof. Source read: M. C. B. Zaremsky, *Bestvina–Brady
discrete Morse theory and Vietoris–Rips complexes*, arXiv:1812.10976v3 (28 March
2021; to appear in Amer. J. Math.), Section 6.1. Text extracted from the v3 PDF with
ghostscript on MSI on 2026-09-13.

- Definitions of path, combing, bounded combing and contracting combing (Section 6.1,
  "Following [Alo92]"), as recorded in the claim. The ghostscript extraction dropped
  primes in the contracting condition, and the reconstruction first recorded here
  (`n <= n'`) was wrong. A second extraction of the v3 PDF with pypdf on 2026-09-16
  keeps the primes and reads: "for all g, h ∈ G and n, n′ ∈ N0, with n′ ≤ n and
  ⌊C/2⌋ ≤ n, if d(s(g)(n), s(h)(n′)) ≤ C then also d(s(g)(n − ⌊C/2⌋), s(h)(n′)) ≤ C".
  The claim now records `n' <= n`. The reversed reading holds only for finite groups
  (`research/artifacts/zaremsky-4-01-contracting-combings-2026-09-16.md`,
  Proposition 1).
- Citation 6.7, verbatim: "[Alo92, Theorem 1] If G admits a bounded combing then for
  all t there exists s ≥ t such that the inclusion VR_t(G) → VR_s(G) induces the
  trivial map in π_k for all k. If G admits a contracting combing then VR_t(G) is
  contractible for some t."
- Following remark: "groups admitting bounded combings include the important family of
  automatic groups (in this case the function φ can be taken to be φ(n) = Cn+D for
  constants C and D), so this implies automatic groups are of type F_∞."

Primary source, not read here: J. M. Alonso, *Combings of groups*, in Algorithms and
Classification in Combinatorial Group Theory, MSRI Publ. 23 (1992), Theorem 1 and
Lemma 2 (contracting combings are bounded).

The same section also has Proposition 6.8 ("good combing"). If a geodesic combing `s`
and `N >= 0` are such that for every `g` with `d(1,g) = t >= N` there is `n` with
`d(h, s(g)(n)) < t` for all `h` with `d(1,h), d(h,g) <= t`, then `VR_t(G)` is
contractible for all `t >= N` (Theorem 6.5, via the Strong Link Criterion).
