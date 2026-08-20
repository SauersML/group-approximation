---
rg: 2
id: slofstra-subexponential-hyperlinear-profile
kind: claim
title: Slofstra's Clifford-shift-HNN group has at least subexponential hyperlinear profile
artifacts:
  - research/artifacts/self-similar-dimension-pressure-map-2026-08-20.md
  - research/artifacts/three-paper-cairn-ingestion-2026-08-20.md
distinct_from:
  two-generator-amitsur-levitzki-dimension-oracle: that detects the exact matrix size by polynomial identities; Slofstra obtains a quantitative lower bound by forcing a long approximate Clifford family.
  same-model-supercritical-clifford-trigger: that asks for an impossible Clifford family inside the same candidate model; Slofstra's theorem only makes the required dimension grow as the defect decreases.
---

There are a finitely presented group `G=<S|R>`, a word `w`, and constants
`alpha,C,C'>0` such that

```text
hlp(w;delta,epsilon)
  >= C' exp(C (delta/epsilon)^alpha)
```

for all `delta,epsilon>0`; `alpha` may be any fixed constant below `1/2`.
Here `hlp` is the least dimension of an `epsilon`-representation keeping `w`
at normalized-Frobenius distance at least `delta` from the identity.

The construction starts with the infinite Clifford group, compresses its
generators by a shift, adds the self-similar HNN relation `t z t^-1=z^2`, and
uses a quantitative BORS Higman embedding so short consequences in the
recursive group have controlled area in a finite presentation.  An
`epsilon`-representation retaining the central involution then contains a
long approximate Clifford family, which forces the displayed dimension
lower bound.

The theorem supplies no upper bound and does not prove that its group is
hyperlinear or nonhyperlinear.  In hyperlinear-profile language,
nonhyperlinearity requires the profile of some genuine word to be `+infinity`
at fixed positive separation for all sufficiently small relation defect.
