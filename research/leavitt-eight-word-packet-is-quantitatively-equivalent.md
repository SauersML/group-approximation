---
rg: 2
id: leavitt-eight-word-packet-is-quantitatively-equivalent
kind: claim
title: Eight native Leavitt words have the same quotient and factor-two defect control as the nine-word certificate
distinct_from:
  leavitt-has-an-explicit-finite-c-killing-certificate: That supplies the native kernel certificate excluding exact finite-dimensional models; this records equality of normal closures, comparisons for every unitarily invariant norm, and the separate squared-sum energy comparison for the eight- and nine-row versions.
  binary-leavitt-hyperlinear-iff-24k-feasible: That characterizes hyperlinearity through an exhaustive family of kernel tests; this compares two specified finite packets and does not establish a uniform gap for either.
artifacts:
  - research/artifacts/leavitt-eight-word-exact-reduction-2026-09-08.md
  - research/artifacts/leavitt-eight-word-pilot-and-replay-2026-09-08.md
---

Use the shorter compiler of the explicit nine-word certificate, whose
Thompson three-cycle word has length at most `164`. Define

```text
T_8={r_*,d^2,rho_2,rho_3,rho_5,rho_6,rho_7,rho_8}.
```

The artifact gives every word explicitly. This packet lies in the native
kernel and has the same normal closure in `P=C_3*C_2^3` as `T_9`.
For every unitary evaluation with `C^3=I`, and every unitarily invariant
norm, its maximum relator defect satisfies

```text
delta_8 <= delta_9 <= 2 delta_8.
```

Indeed `rho_1=j^2` is a conjugate of `d^2`, while `rho_4` is the
commutator `[L,r_*]` for the explicit word
`L=(j c)^(-1)c^(-1)(j c)^(-1)c^(-1)`.

The row length bounds are respectively

```text
166, 16, 492, 984, 4528, 7576, 7576, 9880.
```

For normalized-HS squared-sum energies, `E_8 <= E_9 <= 5E_8`.
The two packets have identical exact zero sets, vanishing sequences,
and fixed-dimension or dimension-uniform gap status. In particular
`T_8` still forces `c=1` in every exact finite-dimensional unitary model.

No positive dimension-uniform lower bound is established here. Its
existence remains the same open question for either packet.
