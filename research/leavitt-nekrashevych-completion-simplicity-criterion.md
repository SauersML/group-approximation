---
rg: 2
id: leavitt-nekrashevych-completion-simplicity-criterion
kind: claim
title: Graded ideals of O_psi correspond to psi-saturated ideals of B, and O_psi is simple when B is psi-minimal and the core has no off-degree centralizer
distinct_from:
  leavitt-nekrashevych-completion-embeds-and-is-fp: that proves finite presentation and injectivity of B -> O_psi; this describes the ideals of O_psi and gives a simplicity criterion.
  algebra-boone-higman-conjecture: that is the universal envelope statement; this is a criterion that one candidate envelope construction is simple.
---

**ESTABLISHED** through `leavitt-nekrashevych-completion-simplicity-proof`.

Notation as in `leavitt-nekrashevych-completion-embeds-and-is-fp`, with `psi`
injective. `O_psi` is `Z`-graded by `deg s_i = 1`, `deg t_i = -1`, `deg B = 0`.
Write `O_k` for the degree-`k` part and `C = O_0` for the core.

**Definitions.**

- An ideal `I` of `B` is **psi-saturated** if `I = psi^{-1}(M_d(I))`, i.e.
  `b in I` iff every entry of `psi(b)` lies in `I`.
- `B` is **psi-minimal** if its only psi-saturated ideals are `0` and `B`.
- `(B, psi)` is **aperiodic** if no nonzero element of `O_k`, `k ≠ 0`, commutes
  with every element of `C`.

**Claim.**

1. **Normal form.** `O_k = span{ s_mu b t_nu : b in B, |mu| - |nu| = k }`. For
   `|mu| = N + k` and `|nu| = N` (`N` large), the coefficient matrix
   `Y_{mu nu} = t_mu y s_nu in B` of `y = sum s_mu Y_{mu nu} t_nu` is determined by `y`.
2. **Graded ideals.** `J |-> J ∩ B` and `I |-> <I>` are mutually inverse
   bijections between graded two-sided ideals of `O_psi` and psi-saturated ideals
   of `B`. So `O_psi` is graded-simple iff `B` is psi-minimal.
3. **Simplicity criterion.** If `B` is psi-minimal and `(B, psi)` is aperiodic,
   then `O_psi` is simple. Conversely, if `O_psi` is simple then `B` is
   psi-minimal.
4. **Leavitt calibration.** For `B = K` and `psi(λ) = λ I_d`, `O_psi = L_d`, the
   pair is aperiodic, and `L_d` is simple with center `K`.

Part 4 recovers Leavitt's classical simplicity of `L(1,d)` inside this framework.
The graded-ideal correspondence parallels the gauge-invariant ideal theorems for
algebraic Cuntz--Pimsner rings (Carlsen--Ortega arXiv:0810.3254, graded-ideal
description per the abstract); the proof route is self-contained. No novelty is
claimed for parts 1, 2 and 4.

This settles the second open question in Attempt 5 of
`algebra-boone-higman-conjecture`, simplicity of `O_psi`, down to the two
hypotheses in part 3.
