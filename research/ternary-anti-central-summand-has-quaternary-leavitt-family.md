---
rg: 2
id: ternary-anti-central-summand-has-quaternary-leavitt-family
kind: claim
title: The anti-central summand of the ternary Leavitt group algebra contains a unital quaternary Leavitt family
distinct_from:
  ternary-anti-central-summand-has-cohn-family: that asks only for two orthogonal one-sided pairs; this asks for four pairs whose ranges also sum to the unit, a strictly stronger relation that the canonical trace still allows.
  anti-central-ternary-summand-has-no-binary-leavitt-family: that is the established no-go for binary Leavitt families in the same summand; this is the open quaternary relation, which the same trace argument does not exclude.
artifacts:
  - research/artifacts/ternary-anti-central-cohn-reformulation-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x`, `z = -1` and `S_- = F_3[G] / (1 + [z])`. Exhibit
`sigma_1, ..., sigma_4, tau_1, ..., tau_4` in `S_-` with

    tau_i sigma_j = delta_ij 1_-,       sigma_1 tau_1 + ... + sigma_4 tau_4 = 1_-.

This is sufficient for `ternary-anti-central-summand-has-cohn-family`, and so for the swap corner and
a counterexample to Gottschalk's conjecture on `G`.

## Attempts

- *The image family.* In `R = L_(F_3)(1,2)` the words `s_i s_j` and `t_j t_i` form a unital quaternary
  Leavitt family. An exact lift along `S_- -> R` would settle this claim.
- *Why quaternary.* The canonical trace has `tau(1_-) = 2`, and a type `(1, n)` family forces
  `n = 1 mod 3` (`anti-central-ternary-summand-has-no-binary-leavitt-family`). So the binary family
  cannot lift exactly, and four is the smallest trace-compatible rank.
- *Honest monomial lifts.* As for the Cohn claim, lifts of the words `s_i s_j` by cylinder idempotents
  and transpositions always leave a comparable piece. Invariant-measure arguments in the signed
  Thompson group exclude monomial compressions there. This is where it dies today.
- *Necessary conditions.* The support, together with `z`, generates a group that is not `F_3`-linear
  sofic. `F_3`-linear soficity of `G` refutes this claim.
