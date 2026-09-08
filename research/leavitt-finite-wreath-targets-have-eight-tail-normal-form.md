---
rg: 2
id: leavitt-finite-wreath-targets-have-eight-tail-normal-form
kind: claim
title: Finite Thompson-wreath witnesses for the Leavitt packet have a fixed eight-cell normal form
distinct_from:
  leavitt-eight-word-packet-is-quantitatively-equivalent: That reduces the native packet to eight rows and compares norm defects; this gives an exact prefix realization criterion for maps into finite permutation wreath products of Thompson groups.
  leavitt-has-an-explicit-finite-c-killing-certificate: That excludes exact finite-dimensional unitary targets; this normalizes a specified class of infinite targets without constructing a map into one.
artifacts:
  - research/artifacts/leavitt-eight-tail-wreath-normal-form-2026-09-08.md
---

For `Q=(C_3*C_2^3)/<<T_8>>`, let `N` be the kernel of the split
projection `Q->C_2^3`. The following are equivalent:

- A homomorphism `N->V` retains `c`.
- A homomorphism `Q->V^X semidirect F`, with `X,F` finite and `F`
  acting by coordinate permutations, retains `c`.
- A homomorphism `Q->V` retains `c`.
- The explicit eight-variable tail system in the artifact has a
  solution in `V` with `z_0!=1`.

In the last realization the images of `b_1,b_2,b_3` are fixed bit
flips on the first three binary digits. The image of `c` acts on
the eight prefix cells by the unknown order-dividing-three maps
`z_x`. Every shared word and all 64 packet-coordinate equations are
specified in the artifact, in addition to `z_x^3=1`.

The marked `C_2^3` embeds in this normal form. The normalized homomorphism
is newly constructed and need not be conjugate to the original witness.
A tail family invariant
under translation by either `e_1` or `e_2` is necessarily trivial.
No solution, universal obstruction, or hyperlinearity conclusion is
claimed. The equivalence does not require the separate perfect-kernel
structural theorem.

DERIVATION
normalize-leavitt-wreath-target-by-eight-prefix-cells
