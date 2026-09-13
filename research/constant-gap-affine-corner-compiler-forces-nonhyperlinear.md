---
rg: 2
id: constant-gap-affine-corner-compiler-forces-nonhyperlinear
kind: claim
title: A constant-gap affine corner compiler for the magic-square AND source forces a nonhyperlinear target group
distinct_from:
  ce-exact-affine-compilers-force-nonhyperlinear-corners: that assumes the affine decoder is exact (perfect value) on Connes-embeddable models; this only assumes constant-gap soundness, decoded value at least a fixed s above the gadget's affine-support threshold, which is the regime (iii-c) left open there.
  perfect-lcs-gap-implies-nonhyperlinear: that derives nonhyperlinearity from a strict quantum-value gap of one LCS game; this derives it from a soundness threshold of an affine decoder into a group corner, using the fixed affine-support value gap of the magic-square AND gadget.
  matrix-conj-forces-unsafe-support: that is the qualitative source firewall; this converts its quantitative form into a constant-gap nonhyperlinearity criterion for corner compilers.
artifacts:
  - research/artifacts/affine-support-value-gap-2026-09-13.md
---

**ESTABLISHED** (as a conditional) by
`constant-gap-affine-corner-compiler-nonhyperlinear-proof`. Not independently
reviewed. No novelty is claimed: it plugs the constant gap of
`affine-safe-value-of-magic-square-and-gadget-below-one` into the
canonical-corner argument of
`ce-exact-affine-compilers-force-nonhyperlinear-corners`.

## Setting

Let `B_tilde = B_0 disjoint-union B_MS^AND` be the source of
`matrix-conj-forces-unsafe-support`, with `B_0` any finite tracially
satisfiable non-`R^U` BCS. Let `c* = 1/(9 C0 T)` be the constant of
`affine-safe-value-of-magic-square-and-gadget-below-one` `(V2)`.

A **constant-gap affine corner compiler** for `B_tilde` is: a countable group
`Gamma` with a central `J` of finite order `n` and a faithful character
`omega` of `<J>`; a corner constraint system over `(Gamma,J,omega)`; and an
affine decoder `D` of the form (GC5), such that

```text
(GAP)  for every Connes-embeddable model tau' of the corner, the decoded
       strategy from tau' is a synchronous strategy for B_tilde of value >= s,
```

for some fixed `s > 1 - c*`.

## Statement

If a constant-gap affine corner compiler for `B_tilde` exists with
`s > 1 - c*`, then `Gamma` is not hyperlinear.

## Why

If `Gamma` were hyperlinear, the canonical corner trace `tau_omega` would be
Connes-embeddable (Thom's central-corner criterion, exactly as in Step 2 of
`ce-exact-affine-compilers-nonhyperlinear-proof`). By `(GAP)` the decoded
strategy from `tau_omega` then has value `>= s > 1 - c*`. But that decoded
strategy is a canonical-corner pushforward under the affine `D`, so by part
`(VB)` of `affine-safe-value-of-magic-square-and-gadget-below-one`
its value on the `B_MS^AND` component, hence on `B_tilde`, is at most `1 - c*`.
Contradiction. So `Gamma` is nonhyperlinear.

## Scope and residual gap

- This is the constant-gap sharpening of
  `ce-exact-affine-compilers-force-nonhyperlinear-corners`, whose Scope block
  named "constant-gap affine decoders" as uncovered. It is covered here, with
  the explicit threshold `s > 1 - c*` of the fixed gadget.
- What remains open toward `non-hyperlinear-group`: the **existence** of a
  compiler meeting `(GAP)` with `s > 1 - c*`. The linear robust tests pinned
  in `research/artifacts/ce-only-decoder-floor-map-2026-09-13.md` (BLR,
  Pauli braiding, low individual degree) have affine readouts but certify only
  affine-safe structure, so they cannot achieve value above `1 - c*` on the
  affine-unsafe source `B_MS^AND`; consistent with `(VB)`, no affine decoder
  can. A witness therefore needs a genuinely non-affine or randomized readout,
  which is break (2b)/(iii-b) of the same artifact, not this affine regime.
- So this claim locates the affine regime precisely: within it there is a
  fixed constant gap, so no constant-gap affine corner compiler for an
  affine-unsafe source can have a hyperlinear target, and any affine route to
  `non-hyperlinear-group` is blocked at a fixed threshold rather than only in
  the limit.
