---
rg: 2
id: right-symmetric-sensitivity-profile-admits-no-decoder-proof
kind: route
title: Sum the decoded single-site changes over right orbits of the symmetry
target: right-symmetric-sensitivity-profile-admits-no-decoder
requires: []
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

Single-site inputs `b e_k` produce translated profiles, and the decoder identity
makes the total decoded change at the identity equal to `b`. A right symmetry
`c` of the profile makes the translated profiles for `k` and `kc` equal, so the
changes are constant on free right `<c>`-orbits of size `ord(c)`, and the total
is a multiple of `ord(c)`, hence `0` in `Z/n` when `n` divides `ord(c)`. Section 4
of the artifact.
