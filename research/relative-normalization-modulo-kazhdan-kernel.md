---
rg: 2
id: relative-normalization-modulo-kazhdan-kernel
kind: claim
title: Sofic representations of a rigid pair normalize the relative centralizer modulo a normal Kazhdan subgroup
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is the Kun--Thom theorem that sigma(G) normalizes the exact centralizer C(sigma(Gamma)), the case M = 1; this asks the same for the group of permutations normalizing sigma(M) whose commutators with sigma(Gamma) lie in sigma(M).
  sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels: that is the group-level relative criterion; this is its ultraproduct form, equivalent to it by relative-defect-normalization-dichotomy, which is where the Kun--Thom finite-stage machinery would have to run.
  relative-element-splits-into-m-times-centralizer: that proposed the stronger splitting sigma(z) in sigma(M).C(sigma(Gamma)), refuted by outer automorphisms trivial modulo M; this makes no splitting claim and is not affected by that obstruction.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**OPEN.** Let `Gamma <= G` be a rigid pair and `M <= Gamma` a Kazhdan
subgroup normal in `G`. For every homomorphism `sigma : G -> S_U`, `sigma(G)`
normalizes

```text
N_rel(sigma) = { x in S_U : x sigma(M) x^-1 = sigma(M), [x, sigma(Gamma)] <= sigma(M) } .
```

By `relative-defect-normalization-dichotomy` this is equivalent to
`sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels`. The case `M = 1` is
Kun--Thom Theorem 4.1. Conjugation by `sigma(Gamma)` preserves `N_rel(sigma)`
automatically, so only strict compressors matter.

## Attempts

- **Splitting into `sigma(M) . C(sigma(Gamma))`: dead.** A splitting
  `sigma(z) = sigma(m_0) c` forces `z` to act on `Gamma` as the inner
  automorphism by `m_0`. Take `H = SL_3(Z) semidirect <alpha>` with `alpha` the
  transpose-inverse, and `M = Gamma = G = SL_3(Z)`, `z = alpha`. Then
  `[z, Gamma] <= M`, but `alpha` sends the companion matrix of `x^3 - 2x^2 - 1`
  (trace 2) to a matrix of trace 0, so it is not inner. Found by lane
  `hyperbolic-sofic`. This claim holds trivially in that example, since
  `Gamma = G`.
- **Invariant factor: vacuous exactly where it is needed.** Each `x` in
  `N_rel(sigma)` normalizes `sigma(M)`, so it preserves the diagonal algebra
  `D^{sigma(M)}` of `sigma(M)`-invariant functions. On that algebra
  `[x, sigma(gamma)]` acts trivially, so `x` commutes with `sigma(Gamma)`, and
  `sigma(G)` acts through `G/M`. Kun--Thom Theorem 4.1 at this level would need
  a sofic (trace-zero) representation of `G/M` on the factor. For the Leavitt
  cover, the block lemma `kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient`
  makes `sigma(G)` act trivially there, so the factor carries no information.
  All the content lies inside the `sigma(M)`-blocks. There
  `[sigma(g) x sigma(g)^-1, sigma(gamma)]` fixes `D^{sigma(M)}` pointwise and
  must be shown to be a single element of `sigma(M)`. That is a uniform
  condition, not a blockwise one, and no rounding theorem gives it. **This is
  where it stops.**
- **2-norm criterion (from `hyperbolic-sofic`).** An injective trace-zero
  `sigma` of `H` extends to a trace-preserving embedding of `L(H)` into the
  tracial ultraproduct, and `E_{sigma(L(M))} sigma(u_d) = sigma(E_{L(M)} u_d)`,
  which is `u_d` or `0` according as `d in M`. So for a defect element
  `d = [g z g^-1, gamma]`, any lower bound `||E_{sigma(L(M))} sigma(u_d)||_2 > 0`
  gives `d in M`. Caveat: `sigma(L(M))` is not the block algebra of the finite
  groups `sigma(M)|_B`. A lower bound for the conditional expectation onto the
  larger block algebra does not suffice.
