---
rg: 2
id: kazhdan-heat-maps-round-to-finite-algebras
kind: claim
title: Admissible heat maps of full Kazhdan asymptotic representations round to coordinate algebra expectations
distinct_from:
  bistochastic-near-idempotents-round-dimension-free: That rounds arbitrary nearly idempotent bistochastic channels; this only rounds heat from a fixed Kazhdan group with full asymptotic relations and a fixed group-algebra SOS certificate.
  quotient-gap-expectations-have-coordinate-lifts: That lifts a commutant expectation as coordinate linear maps; this supplies finite coordinate subalgebras and ordinary sequential mixed-norm convergence.
  kazhdan-commutants-are-internal: That describes full relative commutants for specified ultrafilters; this states the sequential heat-rounding consequence, with explicit admissible-time conditions.
artifacts:
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
  - research/artifacts/leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md
  - research/artifacts/leavitt-poissonization-and-admissible-time-rounding-equivalence-2026-09-08.md
---

Let G be a finitely generated property-(T) group. Fix a finite symmetric
generating list S of literal words, with inverse spellings paired, and a
finite group-algebra certificate

```
Delta^2 - kappa Delta = sum_j xi_j^* xi_j,
Delta = 1 - |S|^(-1) sum_(s in S) s,   kappa > 0.
```

Let V_n be unitary tuples in M_(d_n) for which every fixed true relation of
G has normalized-Hilbert--Schmidt defect tending to zero. Evaluate inverse
spellings as adjoints. Let epsilon_n -> 0 bound the finitely many equality
rows in the fixed expanded SOS certificate. For every sequence

```
t_n -> infinity,             epsilon_n t_n -> 0,
A_n = I - |S|^(-1) sum_s Ad(V_(n,s)),
P_n = exp(-t_n A_n),
```

there are unital star-subalgebras B_n of the original M_(d_n) such that

```
||P_n - E_(B_n)||_(infinity->2) -> 0.
```

All matrix traces are normalized, E_(B_n) preserves that trace, and the
mixed norm takes the supremum over the entire operator unit ball. The
limits here are ordinary sequential limits. Canonical trace is not an
assumption. The algebras may depend on the group, certificate, tuples and
times; no numerical modulus uniform over groups is asserted.

## Attempts

**Attribution.** The proposed analytic input is Jihao Liu,
[*Nonhyperlinear groups exist* (2026-09-20)](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7 (commutant internality); Proposition 3.1 gives the related
uniform coordinate expectation criterion. This sequential admissible-heat
formulation is Cairn's conditional application of Liu's analytic theorem,
using the earlier September 8 Cairn heat-identification and time-comparison
arguments linked above. Liu's internality proof remains under review.

2026-09-20: `heat-rounding-from-internal-commutants` proves this implication
from the still-open universal internality claim. The SOS energy estimate
identifies every admissible heat limit with the full commutant expectation.
A bounded-sequence witness argument makes internality into uniform rounding
along each ultrafilter; a bad-subsequence argument gives the stated ordinary
convergence. This does not import Liu's long internality proof as established.
