# A matrix-only trace-polynomial inequality separates the explicit atlas group trace

Former Cairn claim `atlas-matricial-trace-separator`, demoted because its
unrestricted form is a root-equivalent certificate language, not a logically
smaller theorem.  The bounded-window specialization remains active.

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
solutions are close to exact finite-dimensional representations.  It is a
useful certificate/search language for the explicit atlas presentation, but in
this unrestricted form it should **not** be advertised as a new logical
reduction of the root: Hahn--Banach/finite-word duality makes general separator
existence too close to nonhyperlinearity itself.  The genuinely stronger route
is the bounded first-window specialization `atlas-radius-nine-trace-separator`.

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
