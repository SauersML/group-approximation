---
rg: 2
id: qudit-code-rounding-sharp-factor-all-primes
kind: claim
title: For every prime d, including 2 and 3, code-constraint Hamiltonians have stabilizer states within the sharp factor 1+1/sqrt(d) of the ground energy
artifacts:
  - experiments/qudit-code-rounding-symmetric-averaging-2026-09-17/README.md
distinct_from:
  qudit-code-rounding-factor-one-plus-inv-sqrt-d: that proves 1+1/sqrt(d) only for d>=5 (8/5 at d=3, 2 at d=2) by post-selecting on the most satisfied term with a one-sided leak lemma; this proves the sharp 1+1/sqrt(d) for every prime d by averaging over the post-selected term and a two-sided operator inequality.
  stabilizer-rounding-constant-is-one-over-sqrt2: that is the qubit Pauli-sum theorem, whose consequence gives 1+1/sqrt2 for qubit code spaces; the d=2 case here reproduces that value by a different, projector-only argument.
---

**ESTABLISHED (ordinary proof, unreviewed, not Lean-verified; route
`qudit-code-rounding-sharp-factor-all-primes-proof`).** Let `d` be any prime and
`H = sum_a w_a (I - Pi_(S_a))`, with `w_a >= 0` and stabilizer code projectors `Pi_(S_a)` on `n`
qudits. Then some stabilizer state `phi` has

```text
<phi|H|phi>  <=  (1 + 1/sqrt d) lambda_min(H).
```

The factor is optimal for every prime `d` and every `n`. `H = (I - |0><0|) + (I - |+><+|)` has ratio
exactly `1 + 1/sqrt d`. So the qutrit value is `1 + 1/sqrt3 = 1.5774`, where the earlier bound was
`8/5`, and the qubit value is `1 + 1/sqrt2`, where the earlier projector argument gave `2`.

**The new ingredient.** For projectors `P, Q` whose compression `PQP` is `r` times a projector,
`0 < r < 1`,

```text
PQ + QP - PQP - QPQ  <=  (sqrt r - r)(P + Q)      as operators.
```

On each two-dimensional Jordan block the difference is `-sqrt r |p - q><p - q|`. The left side,
evaluated at the ground state `psi`, is the sum of the two post-selection leaks
`Re<psi|PQ(I-P)|psi> + Re<psi|QP(I-Q)|psi>`. The earlier proof bounded one leak at a time, and
needed `<Q> <= <P>`. The per-term bound `h(r) = 1/4` for `r > 1/4` is sharp for that one-sided
lemma, so that proof could not reach `1 + 1/sqrt3`. Here the post-selected term `R` is not fixed in
advance. Averaging the induction inequality over `R` with weights `w_R` turns every leak into a
symmetric pair, which the inequality bounds with no side condition. So some `R` satisfies
`Leak_R <= M_R L_R/(1 + sqrt d)`, and the induction closes at `gamma_d = 1 + 1/sqrt d` for all `d`.

**Consequences.**
- *NP threshold.* For explicit such `H` on prime-`d` qudits, deciding `lambda_min(H) <= a` versus
  `>= b` is in NP whenever `b > (1 + 1/sqrt d) a`. The witness is a stabilizer tableau, verified over
  `F_d`. With extra terms `0 <= h <= I` of total weight `V`, it is in NP when
  `V < b - (1 + 1/sqrt d) a`. Stabilizer witnesses fail at or below the threshold, by the example.
- *Quantum PCP window.* The window for QMA-hardness of code-constraint Hamiltonians is
  `1 < b/a <= 1 + 1/sqrt d` for every prime `d`: `1.7071`, `1.5774`, `1.4472`, `1.3780` for
  `d = 2, 3, 5, 7`. This is the bearing on `quantum-pcp-constant-gap-local-hamiltonian` recorded in
  `qudit-code-rounding-factor-one-plus-inv-sqrt-d`, with the qutrit threshold lowered from `8/5`.
- *Effective rounding.* The proof is an algorithm with at most `n` rounds of linear algebra on a top
  eigenvector: compute every `Leak_R`, `M_R` and `L_R` and post-select on any `R` with
  `Leak_R <= M_R L_R/(1 + sqrt d)`.
- *Scope.* The proof uses only compression closure, one principal angle per pair, and
  `r in {d^(-k)}`. The same argument should give factor `1 + sqrt(r_max)` for any projector family
  with those properties whose minimal members serve as witnesses, where `r_max < 1` bounds the
  pairwise squared cosines. This generalization is not written out.

**Numerics** (`experiments/qudit-code-rounding-symmetric-averaging-2026-09-17/`, not used in the
proof). The operator inequality was checked on all code-projector pairs for `d = 2, 3, 5` with
`n = 1` and for `d = 2`, `n = 2`, and on 16300 pairs for `d = 3`, `n = 2`. The largest eigenvalue
of the difference is `3e-16`. The rounding, run on random instances, attains the worst ratio
`1.707107`, `1.577350`, `1.577350`, `1.447214` for `(d, n) = (2, 1-2)`, `(3, 1)`, `(3, 2)`,
`(5, 1)`. This equals `gamma_d` exactly, with no violation. It matches the earlier state-side dual LP
peaks for `(3, 1)` and `(5, 1)` (`experiments/qudit-stabilizer-rounding-constant-2026-09-17/`).
