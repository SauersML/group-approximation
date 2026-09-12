---
rg: 2
id: atlas-full-relator-data-factor-through-double-commutant-gauge
kind: claim
title: All finite Atlas relator data factor through the relative double-commutant gauge
distinct_from:
  atlas-phase-cycle-determinant-is-gauge-trivial: that proves scalar invariance for the twenty-seven phase formulas; this proves the larger left-and-right commutant symmetry for every word in the full two-chart presentation.
  atlas-repeated-h6-gauge-is-one-gl2m-coordinate: that quotients finite-field H6 conjugators by full-chart gauges; this gives the complex-unitary word-evaluation identity and identifies which mixed singular operators are actually authenticated.
  atlas-separate-chart-module-ledger-is-kernel-blind: that removes invariants of the two chart restrictions separately; this removes raw coordinates of the relative unitary and retains only double-coset mixed data.
---

**ESTABLISHED FIREWALL AND COORDINATE REDUCTION.**  Let
`rho_1,rho_2:A8->U(H)` be the two exactified regular chart models and evaluate
the free product through a relative unitary `U` by

```text
pi_U(i_1(a))=rho_1(a),
pi_U(i_2(b))=U rho_2(b) U^*.                           (DCG1)
```

For arbitrary

```text
D in rho_1(A8)',             C in rho_2(A8)',
U'=D U C,                                                     (DCG2)
```

every word `w in A8*A8` satisfies the exact identity

```text
pi_(U')(w)=D pi_U(w) D^*.                              (DCG3)
```

Therefore the complete finite Atlas relator list--not only the six phase
cycles--has identical defects, singular values, normalized traces, and
normalized-HS energies at `U` and `DUC`.  All ordinary group-word data factor
through the double quotient

```text
rho_1(A8)' \ U(H) / rho_2(A8)'.                        (DCG4)
```

In particular no raw coefficient `tr(A^*U)`, determinant phase, chosen
multiplicity basis, or one-sided singular vector of `U` is authenticated by
the Atlas relators.  Adding more words from the same two-chart presentation
cannot fix this: `(DCG3)` applies word by word.

The smallest legal singular data are mixed compressions.  If `P` belongs to
the first chart algebra and `Q` belongs to the untransported second chart
algebra, then

```text
P U' Q=D (P U Q) C,                                   (DCG5)
```

so the singular values of `PUQ` are double-gauge invariant.  Kernels and
principal angles of finite families of such compressions are therefore
authenticated mixed coordinates; raw singular vectors are not.  The rank
version recovers the mixed-intersection pencils of
`atlas-mixed-fixed-spaces-are-rank-pencils`.

Consequently the finite-only Atlas frontier has a precise admissibility
condition: a proposed singular-subspace invariant must be assembled
equivariantly from several mixed blocks `P_i U Q_j` and be invariant under
simultaneous left/right commutant changes.  A gauge pin chosen from one raw
linear functional, the determinant of `U`, and the raw Jacobian all violate
or forget this condition.  This claim does not prove that an admissible mixed
block family has a gap; it proves that no smaller raw-coordinate operator can
be certified by the actual finite relator list.
