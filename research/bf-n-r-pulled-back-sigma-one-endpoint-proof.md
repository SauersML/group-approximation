---
rg: 2
id: bf-n-r-pulled-back-sigma-one-endpoint-proof
kind: route
title: "Endpoint-germ centralizers of windings, connected-and-dominating criterion, and the strictly ascending HNN for the holes"
target: bf-n-r-pulled-back-sigma-one-misses-only-endpoint-characters
requires:
  - bf-n-r-off-endpoint-plane-pullbacks-lie-in-sigma-one
  - bf-n-r-sigma-m-holes-of-f-n-r-pull-back
  - pure-braided-bht-braid-characters-dimension-n-n-minus-1
artifacts:
  - research/artifacts/zp-bf-n-r-sigma1-pullbacks-2026-09-20.md
---

Artifact part 4.

- Off `span(chi_0, chi_1)`: `bf-n-r-off-endpoint-plane-pullbacks-lie-in-sigma-one`.
- `psi = a chi_0 + b chi_1` with `a, b != 0` (Theorem 11). Apply Koban–McCammond–Meier
  (arXiv:1306.4046, Lemma 1.9, quoted verbatim) with `J = {s(y_0), s(y_1)}`:
  - `y_0`, `y_1` are commuting elements with slope `1/n` at one endpoint, supported in tiny end
    intervals;
  - `I` is the union of their centralizers.
  Every type representative of a winding lies in the centralizer of `s(y_0)` (block-winding Lemma W(d),
  Lemma E). Conjugators and all of `s(F_{n,r})` are products of end-supported elements.
- `[-chi_0]`, `[-chi_1]` (Proposition 10). Zaremsky's Lemma 5.1 gives `Sigma^infinity(F_n)`, carried to
  `F_{n,r}` by the root isomorphism. Then the extension lemma of part 3, with the conjugators corrected by
  powers of `s(y_0)`, which centralize every representative.
- Holes (Lemma H). `F_n = F_n(1) * x_0` is strictly ascending, because `ker chi_0` is not finitely
  generated. BGK Theorem 2.1 (Citation 1.10 of arXiv:1803.02717) gives `[chi_0] notin Sigma^1(F_n)`.
  Meinert's split-quotient criterion, in the holes claim, pulls this back.
- The orbit classification of leaf pairs (Lemma 3) is in the proof of
  `pure-braided-bht-braid-characters-dimension-n-n-minus-1`.
