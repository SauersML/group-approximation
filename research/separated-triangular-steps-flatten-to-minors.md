---
rg: 2
id: separated-triangular-steps-flatten-to-minors
kind: claim
title: A triangular step whose carried idempotent minor separates the two diagonal blocks is a minor step
distinct_from:
  split-identity-minors-survive-triangular-moves: that removes a triangular step when the carried identity minor splits along both diagonal blocks and the padding separately; this allows each diagonal block to mix with its own padding, and works for idempotent minors.
  sylvester-rank-functions-iff-no-triangular-certificate: that characterizes existence of Sylvester rank functions by triangular identity certificates; this identifies a class of triangular steps that such certificates never need.
artifacts:
  - research/artifacts/separated-triangular-certificates-flatten-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `separated-triangular-steps-flatten-proof`. Verification requested from
`w4-vf-linear-b`.

Let `A` be a unital ring and `<~` the minor order `M = X N Y` on rectangular matrices. Let `A`, `B`, `C`,
`Z_1`, `Z_2` be matrices with `T = [[A, C], [0, B]]`, and let `f`, `g` be idempotent matrices with

    f <~ A (+) Z_1      and      g <~ B (+) Z_2.

Then `f (+) g <~ T (+) Z_1 (+) Z_2`, for every `C`.

- **Orientation and padding.** The roles of the two diagonal blocks can be exchanged, and either padding
  block may be empty.
- **Special case.** With empty padding and identity minors this is part 1 of
  `split-identity-minors-survive-triangular-moves`.

**Consequence.** A triangular step of a certificate is removable whenever the carried idempotent minor
separates this way. The steps that remain are those whose carried minor mixes the two diagonal blocks
with each other, or mixes both with a common padding block.

**Corollary.** `nilpotent-jordan-certificates-flatten-to-minors`.

Proof: Section 1 of the artifact.
