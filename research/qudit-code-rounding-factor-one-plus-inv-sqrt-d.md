---
rg: 2
id: qudit-code-rounding-factor-one-plus-inv-sqrt-d
kind: claim
title: On prime qudits with d>=5, code-constraint Hamiltonians have stabilizer states within the sharp factor 1+1/sqrt(d) of the ground energy
artifacts:
  - experiments/qudit-stabilizer-rounding-constant-2026-09-17/README.md
distinct_from:
  qudit-stabilizer-rounding-for-code-constraint-hamiltonians: that proves the factor 8/sin^2(pi/d) through a general Weyl-sum rounding; this proves the sharp factor 1+1/sqrt(d) for d>=5 (and 8/5 for d=3) by post-selecting on code projectors directly.
  stabilizer-rounding-constant-is-one-over-sqrt2: that is the qubit Pauli-sum theorem with factor 1+1/sqrt2 for code constraints; this treats odd prime qudits, where the general Weyl-sum constant grows linearly in d but the code-constraint factor tends to 1.
---

**ESTABLISHED (ordinary proof, unreviewed, not Lean-verified; route
`qudit-code-rounding-factor-one-plus-inv-sqrt-d-proof`).** Let `d` be prime and
`H = sum_a w_a (I - Pi_(S_a))`, with `w_a >= 0` and stabilizer code projectors
`Pi_(S_a)` on `n` qudits. Then some stabilizer state `phi` has

```text
<phi|H|phi>  <=  gamma_d * lambda_min(H),
gamma_d = 1 + 1/sqrt(d)   (d >= 5),      gamma_3 = 8/5,      gamma_2 = 2 by this argument.
```

For qubits, `stabilizer-rounding-constant-is-one-over-sqrt2` already gives
`1 + 1/sqrt2`.

**Sharpness.** For every prime `d`, `H = (I - |0><0|) + (I - |+><+|)`, where `|+>` is
the uniform superposition (the `X = 1` eigenvector), has
`lambda_min = 1 - 1/sqrt(d)`. The best stabilizer value is `1 - 1/d`, at `|0>` or
`|+>`. The ratio is exactly `1 + 1/sqrt(d)`. So `gamma_d` is optimal for all prime
`d >= 5` and every `n >= 1`. For `d = 3` the truth lies in `[1 + 1/sqrt3, 8/5] = [1.5774, 1.6]`.
The numerics below point to `1 + 1/sqrt3`.

**Idea.** Post-select a ground state of `H` on the code space of its most satisfied
term `R`. Every other term `Pi_a` compresses to `r_a Pi_(T_a)` with
`r_a = |T_a|/|S_a| in {1, 1/d, 1/d^2, ...}`, where `T_a = S_a cap C(S_R)`. So the code space
carries a smaller instance of the same kind, and each non-commuting term gives up
at least `w_a(1 - r_a)` of weight for good. The energy lost by post-selection is
`sum_a w_a Re<psi|Pi_R Pi_a (I - Pi_R)|psi> / <Pi_R>`. All principal angles between
the two code spaces have `cos^2 = r_a`, and `<Pi_a> <= <Pi_R>`. A Jordan-block
computation then bounds each term by `h(r_a) <Pi_R>`, where
`h(r) = sqrt r - r` for `r <= 1/4` and `h(r) = 1/4` otherwise. Induction on the code
dimension closes when `h(r)/(1-r) <= (gamma-1)/gamma`. The left side increases in `r`,
so the worst case is `r = 1/d`, which gives `gamma_d`.

**Consequences.**
- *NP thresholds.* For explicit such `H` over prime `d >= 5`, deciding
  `lambda_min(H) <= a` versus `>= b` is in NP whenever `b > (1 + 1/sqrt(d)) a`. For
  `d = 3` it is in NP when `b > 8a/5`. The witness is a stabilizer tableau, verified
  over `F_d` as in `qudit-stabilizer-rounding-for-code-constraint-hamiltonians`. With
  extra arbitrary terms `0 <= h <= I` of total weight `V`, it is in NP when
  `V < b - gamma_d a`.
- *Window for quantum PCP on code-constraint families.* Previously, stabilizer
  witnesses decided these problems only above ratio `8/sin^2(pi/d)`, about
  `0.81 d^2`. Now they decide them above `1 + 1/sqrt(d)`, and the example shows they
  fail at or below it. The open window for QMA-hardness of code-constraint
  Hamiltonians is therefore `1 < b/a <= 1 + 1/sqrt(d)` (`d >= 5`), `<= 8/5` (`d = 3`),
  and `<= 1 + 1/sqrt2` (`d = 2`). This does not show hardness inside the window.
- *Bearing on the root* (`quantum-pcp-constant-gap-local-hamiltonian`). Unless QMA is
  in NP, a QMA-hard family on prime-`d` qudits (`d >= 5`) whose terms all penalize
  leaving stabilizer code spaces, with NO floor `b`, has YES energy
  `a >= b sqrt(d)/(sqrt(d)+1)`. Its relative gap `(b-a)/b` is at most `1/(sqrt(d)+1)`,
  and this tends to 0 as `d` grows. So the admissible relative gap for such families
  shrinks as the local dimension grows. For fixed `d` it is still a constant. With
  non-stabilizer weight `V`, the bound is `a >= (b - V)/gamma_d`.
- *Contrast with general Weyl sums.* For arbitrary Hermitian Weyl sums the additive
  rounding constant grows linearly in `d`
  (`qudit-weyl-rounding-constant-linear-upper-bound`,
  `qudit-weyl-rounding-sharp-constant`). The Harper sum `Z+Z^*+X+X^*` already forces
  about `d/pi`. Code-constraint structure (nonnegative combinations of code
  projectors) is what keeps the factor bounded.

**Numerics** (`experiments/qudit-stabilizer-rounding-constant-2026-09-17/`, not used in
the proof).
- State-side dual LP for the factor: `gamma(psi) = min g` such that a stabilizer mixture
  has `1 - tr(rho Pi_S) <= g (1 - <psi|Pi_S|psi>)` for every code projector.
  Local search over `psi` peaks at `1.577350` for `d=3, n=1`, at `1.447213` for
  `d=5, n=1`, and at `1.545199` for `d=3, n=2` with random restarts. Searches seeded at
  (one-qutrit extremal) x (qutrit) stay at `1.577350`.
- The proof's rounding, run on random instances, gives a worst ratio
  `F_phi/F_psi` of `1.577350` (`d=3`, `n=1,2`) and `1.447214` (`d=5`, `n=1`). There
  is no violation of `gamma_d` (see the README for the `d=5, n=2` and `d=7` runs).
