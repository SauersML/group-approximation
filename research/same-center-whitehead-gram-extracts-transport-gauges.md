---
rg: 2
id: same-center-whitehead-gram-extracts-transport-gauges
kind: claim
title: The common Whitehead carrier exposes both transport gauges as finite-coordinate operators
artifacts:
  - research/same-center-whitehead-transport-gauge-extraction-proof.md
distinct_from:
  same-center-whitehead-gram-is-not-native-selector-gram: that correctly rejects the unsupported identification with the unequal selector support rows; this retains the valid finite-coordinate gauge extraction and identifies exactly what still has to be attached.
  binary-leavitt-native-two-scale-cross-gram-positive: that asks for the actual native selector contractions and their support typing; this constructs only their canonical same-gauge candidates from the literal Whitehead transports.
---

On the common positive carrier `F` of
`same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps`, write

```text
S_1=SWAP_(1,2) tensor V_1,
S_2=SWAP_(2,3) tensor V_2                              (WGE1)
```

relative to `FH=(C^2)^(tensor 3) tensor M`.  Let `A_1,A_2` denote the two
canonical adjacent swaps in the recovered `M_8(C)` label algebra.  They are
finite-coordinate operators determined by the exactified Pauli packet, so

```text
G_i=A_i^*S_i=I_8 tensor V_i.                           (WGE2)
```

Thus both Whitehead reservoir gauges are exposed on the same physical
carrier without selecting a microscopic Heisenberg atom and without a
Property-`(T)` or stability input.

Let `C_(1/4),C_(1/8)` be the fixed label reflections in `M_8(C)` with the
indicated negative spectral fractions.  Finite-coordinate multiplication
now gives canonical candidate controlled outputs

```text
T_1^cand=C_(1/4)G_1=C_(1/4) tensor V_1,
T_2^cand=C_(1/8)G_2=C_(1/8) tensor V_2.                (WGE3)
```

For operator-norm microstates the same formulas hold with `o(1)` error after
dimension-free exactification of this one fixed packet.  The construction is
analytic inside the matrix coordinate; it does not assert that either label
reflection is an ordinary group word.

This is the maximal conclusion supplied by the tautological full Gram.  To
invoke the affine selector obstruction one must still prove, on one nonzero
approximately reducing subcorner, that the two **actual** native selector
support rows have outputs `o(1)`-close to `(WGE3)`.  Equivalently, their
external gauges must be authenticated as the `V_i` extracted in `(WGE2)`.
Neither `S_i^*S_i=F` nor multiplication by the analytic label reflections
proves those support-row identities.

No Property T, Kazhdan constant, normalized-Hilbert--Schmidt promotion, or
literature theorem is used.

DERIVATION
same-center-whitehead-transport-gauge-extraction-proof
