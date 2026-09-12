---
rg: 2
id: natural-leavitt-pair-lifts-have-partial-symmetry-defect
kind: claim
title: Every mixed-depth monomial lift of the Leavitt pair has a partial-symmetry defect on one kernel idempotent
distinct_from:
  odd-measure-space-has-no-honest-thompson-compression: that forbids monomial compressions of the odd-measure space by Haar invariance; this computes the exact Gram defect of the natural lifts of (s0, t0) for every choice of extending Thompson units.
  ternary-anti-central-summand-has-cohn-family: that is the open target; this is an established computation showing what the natural lifts leave undone.
artifacts:
  - research/artifacts/ternary-cohn-mixed-depth-lifts-2026-09-12.md
---

Work in `B = C(M_-, F_3) x| V ⊆ S_-` (`signed-thompson-algebra-is-odd-measure-crossed-product`), with
honest lifts `P_C = 1_(U_C)`, `U_C = { mu : mu(C) = 1 }`. Let `g_0, g_1 in V` be any Thompson units with
`g_0(0x) = 00x` and `g_1(1x) = 01x`, and put

```text
sigma = [g_0] P_0 + [g_1] P_1,        tau = [g_0^-1] P_00 + [g_1^-1] P_01,
```

lifts of `s_0` and `t_0`. With `A = g_1^-1(00)`, `B' = g_0^-1(01)`, `h = g_0^-1 g_1`,
`W_1 = U_A ∩ U_1`, `W_2 = U_0 ∩ U_(B')`, `F = 1_(W_1) + 1_(W_2)` and `D = [h]1_(W_1) + [h^-1]1_(W_2)`:

- `tau sigma = 1 + D`, with `F` a nonzero idempotent in `ker pi` and `D in ker pi`;
- `D^2 = F` and `DF = FD = D`, so `D` is a partial symmetry on `F`;
- `e' = 2(F - D)` is a nonzero idempotent, and `tau'' = (1 + D) tau = tau sigma tau` is another lift of
  `t_0` with `tau'' sigma = (1 + D)^2 = 1 - e'`;
- `(1_(W_1), 1_(W_2), [h]1_(W_1), [h^-1]1_(W_2))` are `2 x 2` matrix units and `e'` is their rank-one
  idempotent `2[[1,-1],[-1,1]]`. So `e' ~ 1_(W_1) ~ 1_(W_2) ≤ P_0`, and `e' ~ 1` iff `1 ~ 1_(W_1)`.

So for every choice of extending units the lift of the binary Leavitt pair is left invertible exactly
modulo one nonzero kernel idempotent, and `sigma` is left invertible in `S_-` iff `e' in S_- sigma`.
The mixed-depth freedom changes the sets `W_i` but never the type of the defect. Proof: Lemma 2.1 of
the artifact.

**Correction (w4-vf-linear-b, 2026-09-12).** An earlier version of the third bullet displayed the
factor `((1 - F) + 2(F + D))`. That factor equals `1 - e'`, and multiplying it onto `tau sigma` returns
`tau sigma = 1 + D`, not `1 - e'`. The artifact's `c = (1 - F) + 2e = 1 + D`, with `e = 2(F + D)`, is
correct. No conclusion changes (`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`,
Section 1).
