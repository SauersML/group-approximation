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
- *Constant units, the Hadamard involution included, cannot help* (Section 4 of the artifact,
  gk-l3-units, 2026-09-12, corrected the same day).
  - The depth-two Hadamard unit `H_2 = u_(M (x) M)` is an honest involution over `F_3`
    (`N^2 = 4 I = I`). It gives non-monomial idempotents `2(1 +- [H_2])` without passing to `F_9`.
  - Every constant unit lies in the locally finite subgroup `union_k u(GL_(2^k)(F_3))`. No family is
    supported on a finite subgroup, because `eps_- F_3[H]` is finite-dimensional and hence
    Dedekind-finite. So constant supports are excluded.
  - `F_9` gives non-monomial idempotents already at depth one, but it lowers neither the stakes nor
    the gate.
- *Withdrawn claims (2026-09-12).* The first version of this entry made three claims, all wrong:
  - The Hadamard frame cancels every cross term. As stated this was false: a unital quaternary family
    in a finite-dimensional algebra is impossible.
  - The kernel mass sits at infinite depth. It already has Haar measure `1 - 2^(n+1-2^n)` at depth `n`
    (`odd-measure-kernel-carries-almost-all-haar-mass`).
  - A witness needs infinite support. That statement is equivalent to nonexistence, not a no-go.
- *Where it dies today.* Nothing proved here excludes non-constant finitely supported families, such as
  Hadamard constants combined with non-constant Thompson units. Inside the signed Thompson crossed
  product, the Thompson projection of the support must be nonamenable
  (`odd-measure-corner-witnesses-need-nonamenable-thompson-support`).
- *The F_9 Hadamard idea, tested* (lane w3-corner-cohn-b, 2026-09-12,
  `f9-hadamard-spectral-cohn-attempt-2026-09-12.md`).
  - **Coefficients.** F_9 families are equivalent to F_3 families
    (`ternary-anti-central-cohn-family-over-f9`): the regular representation followed by the
    matrix-ring embedding is a unital map `S_-^(9) -> S_-`.
  - **Spectral halves.** `f_(+/-) = 2(1 +/- i[h])` are conjugate halves through
    `u = s0 t0 + s1 t0 - s1 t1`, and fullness of `f_+` gives the Cohn family
    (`f9-hadamard-spectral-idempotent-is-full`).
  - **Collapse.** On the host `G_9` they conjugate to cylinder lifts. Over `G_3` they are 2x2 `F_3`
    designs supported on `{g, gh}`. By Galois density no lift uses one group element per half. The
    rank-model state filter carries over.
  - **Status.** No witness. The only new content is that `h` in the support escapes the monomial
    crossed product.
