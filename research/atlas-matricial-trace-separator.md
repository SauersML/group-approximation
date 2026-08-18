---
rg: 2
id: atlas-matricial-trace-separator
kind: claim
title: A matrix-only trace-polynomial inequality separates the explicit atlas group trace
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
---

Let `T_St` be the explicit finite rank-five atlas/Steinberg relator list from
`atlas-steinberg-rank-five-translation`, on its twelve atlas generators, and
let

```text
Gamma_St = Pbar / <<T_St>>.
```

There exist a self-adjoint finite-degree trace polynomial `P` in those twelve
unitary variables and constants `C,c>0` such that:

```text
P_n(U) + C * sum_(r in T_St) ||r(U)-1||_2^2 >= 0
```

for **every** matrix size `n` and every unitary twelve-tuple `U`, while the
canonical group trace satisfies

```text
tau_Gamma_St(P(lambda(g_1),...,lambda(g_12))) <= -c.
```

This is an all-dimensions matrix inequality, not an assertion that approximate
solutions are close to exact finite-dimensional representations.  In
particular it is designed to bypass the atlas program's existing
Leavitt/Pauli/PVM/commutant decoder machinery completely.

## Attempts

- **Moment-SDP search.**  Truncate the trace-word algebra at degree `D`, impose
  unitary and robust `T_St` relator constraints, and optimize a separating
  functional against the canonical atlas moment vector.  Increase `D` and run
  direct finite-`n` adversarial searches only as discovery tools; no finite
  size sweep is accepted as proof of the all-`n` inequality.
- **Exploit presentation symmetry.**  Average a candidate separator under the
  visible atlas/root symmetries so thousands of relator penalties collapse to
  a small number of orbit sums.  Rational reconstruction of stabilized dual
  SDP coefficients is the preferred path to a human/Lean-checkable formula.
- **All-dimensions proof language.**  Try simultaneous-conjugation invariant
  theory (Procesi trace words), exterior-power/Schur-complement inequalities,
  and fixed-size trace Positivstellensatze as a microscope for discovering a
  proof that inducts in matrix size.
- **Hard guardrail.**  `global-tracial-positivity-cannot-separate-group-trace`
  rules out any purported proof that is actually sound in every tracial von
  Neumann algebra: evaluating such a certificate in `L(Gamma_St)` would
  contradict the required negative canonical trace.  The successful proof
  must genuinely use finite-dimensional matrix structure.
