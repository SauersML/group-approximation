---
rg: 2
id: leavitt-units-are-not-quantitatively-surjunctive
kind: claim
title: The binary Leavitt unit group carries injections into proper subshift tracks with margins below every linear deficit
distinct_from:
  leavitt-unit-group-nonsurjunctive: that asks for an injective nonsurjective automaton on one full shift, which gives this claim with one track and zero margin; this allows many tracks that only miss a pattern, and a positive margin sublinear in the number of tracks.
  leavitt-units-have-zero-rokhlin-entropy-supremum: that is the measurable zero side of the dichotomy; this is a topological statement that forces it, and no converse is known.
artifacts:
  - research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md
---

**OPEN.** Let `U = L_(F_2)(1,2)^x`. There are a finite alphabet `B` and a proper subshift `Y <= B^U` such that for
every `delta > 0` there are a finite alphabet `D`, integers `n >= 1` and `j, j' >= 0` with
`(j' - j) log|D| < delta n`, and an injective cellular automaton from `(B^n x D^j)^U` into `Y^n x (D^(j'))^U`. That
is, `U` is not quantitatively surjunctive in the sense of `surjunctive-groups-are-quantitatively-surjunctive`.

- **Payoff.** It forces `h^Rok_sup(U) = 0` (route `leavitt-zero-rokhlin-supremum-from-sub-threshold-injection`), and
  so refutes `bernoulli-rokhlin-entropy-maximal-for-every-group`. One injection with margin below
  `n eta_W / |W W^-1|`, for a pattern on `W` missing from `Y`, already suffices.
- **Equivalent form.** Quantitative surjunctivity implies surjunctivity. So this claim holds iff `U` is nonsurjunctive
  or `U` is a surjunctive counterexample to `surjunctive-groups-are-quantitatively-surjunctive`.
- **Candidates.** `Y` must contain every constant configuration (Residue item of
  `quantitative-surjunctivity-constants-lift-from-quotients`).

## Attempts

- **No construction yet (w7-quant-residue).** Recorded as the weakest topological target known to force the zero side
  of the dichotomy over `U`. The image may miss patterns on every track and the margin may be positive, so it asks
  less than a strict automaton. No candidate has been built. Section 3 of
  `research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md`.
