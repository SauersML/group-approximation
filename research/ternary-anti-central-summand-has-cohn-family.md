---
rg: 2
id: ternary-anti-central-summand-has-cohn-family
kind: claim
title: The anti-central summand of the ternary Leavitt group algebra contains a unital two-pair Cohn family
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is the corner equation c e_- b = eps_- for the swap-averaging idempotent; this is the idempotent-free equation tau_i sigma_j = delta_ij in the whole summand, equivalent to it through the diagonal endomorphism.
  ternary-twisted-algebra-has-swap-separated-one-sided-pair: that is one one-sided pair c a = 1 whose partner kills the swap translate, c [w] a = 0; this is two orthogonal one-sided pairs with no reference to the swap, a free summand of rank two inside rank one.
  ternary-leavitt-unit-group-nonsurjunctive: that is the root asking for a strict automaton on the ternary unit group; this is an algebraic target sufficient for it through the swap corner.
artifacts:
  - research/artifacts/ternary-anti-central-cohn-reformulation-2026-09-12.md
---

**OPEN.** Let `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `S_- = F_3[G] / (1 + [z])` with unit `1_-`.
Exhibit `sigma_1, sigma_2, tau_1, tau_2` in `S_-` with

    tau_i sigma_j = delta_ij 1_-.

**Equivalent forms**, all proved in Theorem 2.1 of the artifact:
- `S_-^2` is isomorphic to a direct summand of `S_-`;
- some `sigma_j`, `tau_i` have Gram matrix `[tau_i sigma_j]` invertible in `M_2(S_-)`;
- `ternary-anti-invariant-swap-corner-is-full`, through the routes
  `anti-central-cohn-family-gives-swap-corner-fullness` and
  `swap-corner-fullness-gives-anti-central-cohn-family`.

**Necessary conditions.**
- The support of a witness, together with `z`, generates a group that is not `F_3`-linear sofic
  (Proposition 2.4).
- `F_3`-linear soficity of `G` would refute this claim (`linear-sofic-group-algebra-is-stably-finite`).

**What does not obstruct it.** No augmentation exists on `S_-`, so the no-Leavitt-family argument for
group algebras over a field does not apply here (Remark 2.3).

**What the trace says.** The canonical trace has `tau(1_-) = 2`. It forbids unital binary Leavitt
families in `S_-` and fixes `tau(p) = 1` for the defect `p` of any Cohn family
(`anti-central-ternary-summand-has-no-binary-leavitt-family`). A quaternary Leavitt family is
trace-compatible and sufficient (`ternary-anti-central-summand-has-quaternary-leavitt-family`).

## Attempts

- *Lifts of the Leavitt generators.* `pi_-` maps `S_-` onto `R`, where `(t_i, s_j)` is a Cohn family.
  For lifts `sigma_j` of `s_j` and `tau_i` of `t_i`, the Gram matrix lies in `I + M_2(K_-)`, with
  `K_- = ker pi_-`.
  - Invertibility of that Gram matrix is exactly the target, and a nilpotent defect is enough.
  - `K_-` contains nonzero idempotents (lane gk-l3-kernel), so invertibility is not automatic.
  - Where it dies today: no lift with a computed invertible Gram matrix is known.
- *Honest monomial lifts* (Section 3 of the artifact).
  - In characteristic three every cylinder projection `p` lifts to the idempotent `2(1 - [1 + p])`,
    and every disjoint-cylinder partial isometry lifts to idempotent . transposition . idempotent.
  - A lift of `s_0` always contains a comparable piece `S[0^(k+1)] T[0^k]`, which is itself a
    conjugate of `s_0`. So honest monomial pieces never assemble the isometry.
  - Lane gk-l3-free reports that an invariant measure excludes such monomial compressions inside the
    signed Thompson group. Witnesses must use mod-3 overlaps or non-monomial units.
