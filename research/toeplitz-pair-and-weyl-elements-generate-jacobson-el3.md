---
rg: 2
id: toeplitz-pair-and-weyl-elements-generate-jacobson-el3
kind: claim
title: The Toeplitz root pair with the constant Weyl group generates the Jacobson elementary group, and with the constant root groups all Leavitt units
distinct_from:
  binary-jacobson-el3-rank-radical-is-the-finitary-kernel: that is the open rank-radical claim about models of EL_3 over the Jacobson algebra; this identifies that group as exactly what the Toeplitz pair and the constant Weyl group generate, which is where exact Toeplitz commutators stop being finite-subgroup data.
  natural-fock-quantized-compressors-miss-toeplitz-by-a-quarter: that measures how truncated-shift compressors fail the Toeplitz commutator; this determines the group in which that commutator is load-bearing.
  sofic-subgroups-carry-independent-cylinder-defects: that shows sofic subgroups force no strict deficit; this names the subgroup whose nonsoficity a relation-only deficit from Toeplitz and constant data would have to prove.
artifacts:
  - research/artifacts/fock-toeplitz-input-and-sofic-independence-2026-09-12.md
---

**ESTABLISHED** (route `toeplitz-pair-weyl-generation-proof`; artifact Section 3; independent re-derivation requested
from `w4-vf-gate`).

**Statement.** Let `R = L_(F_2)(1,2)`, `R^x = EL_3(R)`, `J = F_2<s0, t0> ⊂ R`, and `R_0 = ∪_j M_(2^j)(F_2)`.
* `<x_12(t0), x_23(s0), EL_3(F_2)> = EL_3(J)`.
* `<x_12(t0), x_23(s0), x_ij(R_0) : i != j> = R^x`.

The same holds over `F_3`, with `J_3 = F_3<s0, t0>` and `L_(F_3)(1,2)^x`.

**Consequence.**
* **Where the relation bites.** The Toeplitz commutator `[x_12(t0), x_23(s0)] = x_13(1)` lies in a finite unitriangular
  group, so on its own it is finite-subgroup data. It becomes load-bearing only together with the constant Weyl group,
  inside `EL_3(J)`.
* **What a deficit proof would show.** Frames at disjoint cylinders commute, so by
  `sofic-subgroups-carry-independent-cylinder-defects`, a relation-only strict deficit from Toeplitz and constant-Weyl
  data at two disjoint cylinders would prove `EL_3(J)` nonsofic.
* **Status of `EL_3(J)`.** It has a locally finite kernel over a residually finite linear quotient, and its soficity is
  not decided on main.
* **With the level constants.** The pair and the constant root groups generate all of `R^x`, so the compressor
  corrections of moving-level models involve every relation of `R^x`.

## Attempts

- Established, not open. The proof is the Steinberg coefficient-closure argument: permutation conjugation makes one
  coefficient set, commutators make it an algebra, and `p s0 = s1`, `t0 p = t1` with `p = s0 t1 + s1 t0`.
- **Soficity status (w7-el3j-sofic, 2026-09-12).** The undecided soficity in the Consequence paragraph is now the OPEN
  claim `binary-jacobson-el3-is-sofic`, with three firewalls in
  `research/artifacts/jacobson-el3-soficity-firewalls-2026-09-12.md`.
  - `EL_3(J)` contains no `V`, `R^x` or `EL_3(C_2)` (`jacobson-elementary-subgroups-are-locally-finite-by-linear`).
  - `EL_3(J)` is LEA iff it is LEF (`jacobson-elementary-groups-are-lea-only-if-lef`).
  - **Where the relation bites, confirmed.**
    - `x_12(t0)` lies in the preimage `H_-` of `SL_3(F_2[z^(-1)])`, and `x_23(s0)` in the preimage `H_+` of
      `SL_3(F_2[z])`. Both halves contain the constants, and both are LEF with the head retained
      (`jacobson-one-sided-symbol-preimages-are-lef`).
    - The commutator `[x_12(t0), x_23(s0)] = x_13(1)` does not hold in their amalgam over `H_0`.
    - So a relation-only deficit must use the Toeplitz pair jointly.
