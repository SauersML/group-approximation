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
- *The Hadamard frame kills cross terms but not the family* (Section 4 of the artifact, gk-l3-units
  2026-09-12). The depth-two Hadamard unit `H_2` is an honest involution over `F_3` (`N = M (x) M`,
  `N^2 = 4 I = I`), and its non-monomial idempotents `2(1 +- [H_2])` cancel every cross term of the
  monomial lift, with no passage to `F_9`. So the cross-term obstruction is not fundamental. But `H_2`
  and every cylinder involution and permuting unit lie in a finite `2`-group `H`, and a family
  supported on a finite subgroup cannot be a unital two-pair Cohn family: `eps_- F[H]` is
  finite-dimensional, hence Dedekind-finite, so a left-invertible `sigma_1` is invertible and
  `tau_1 sigma_2 = 0` forces `sigma_2 = 0`. This is the finite-support case of
  `swap-separated-pairs-avoid-finitely-represented-supports`.
- *The unified dichotomy, where it dies.* Cross-term cancellation needs only finite-level non-monomial
  units; the kernel mass lives at infinite depth, so capturing it needs infinite support. A finite
  construction is Dedekind-finite and carries no rank defect; an infinite one must solve the mass
  problem, which is the original wall. The rank defect is the Leavitt relation `s0 t0 + s1 t1 = 1`
  iterated to the boundary. `F_9` buys non-monomial idempotents at depth one but lowers neither the
  stakes (a witness over `F_9` refutes Gottschalk over the alphabet `F_9`) nor the wall.
