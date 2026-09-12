---
rg: 2
id: central-reducing-spike-certificates-batch-round
kind: claim
title: Central reducing spike certificates batch-round with no dependence on the number of cuts
distinct_from:
  central-weighted-erasure-ledger-recovers-reset-density: that bounds the weighted size of cleaning sets from blockwise bad parity rows; this composes that ledger with simultaneous reset and an operator-coverage certificate.
  block-adaptive-sparse-reset-is-cheap: that turns arbitrary GIVEN blockwise reset density into displacement and induced energy; this supplies the density from balanced parity and records the retained operator-small conclusion.
  balanced-parity-excludes-perfect-matching-pauli-mixtures: that exactly rounds central PROJECTIVE Pauli labels using their symplectic syndrome matrix; this treats arbitrary central reducing blocks conditionally on the nonprojective spike-coverage certificate, without classifying their generated algebra.
---

Let `E=E_bal(Q)` be the balanced-overlay energy of a shared reflection tuple,
and let `(z_omega)` be a finite, countable, or measurable reducing central
decomposition.  Fix a bad-row threshold `rho>0`.  On each block let

```text
E_omega={h:e_(h,omega)>rho}                              (CRB1)
```

and let `S_omega` be the deterministic erasure-cleaning set from
`central-weighted-erasure-ledger-recovers-reset-density` (all coordinates
on its exceptional blocks).

Assume the OPERATOR CONSTRUCTION supplies the following coverage
certificate: after simultaneously resetting the coordinates in `S_omega`
on block `z_omega`, every retained anchor-odd part obeys

```text
||z_omega Y'_(a,i)||_infty<=kappa                       (CRB2)
```

for the anchors/sites assigned to that block.  Then the simultaneous batch
reset `(Q_i')` satisfies

```text
(1/L)sum_i ||Q_i-Q_i'||_2^2 <=C E/rho^2,                (CRB3)
E_bal(Q')                  <=2E+C E/rho^2,              (CRB4)
ess sup_(omega,a,i)||z_omega Y'_(a,i)||_infty<=kappa.   (CRB5)
```

The constant is independent of the number of central blocks, the number of
spike projections that produced them, `L`, and matrix dimension.

Consequently, for ANY schedules

```text
rho(E)->0,       E/rho(E)^2->0,       kappa(E)->0,       (CRB6)
```

the whole central/reducing spike family is corrected at `o(1)` cost and
leaves an operator-small soft core.  For example `rho=E^(1/4)` gives reset
cost `O(sqrt(E))`.  There is no need to execute or count the cuts one at a
time: their union is reset once on each central block.

The hypothesis `(CRB2)` is deliberately explicit.  This theorem closes the
COUNTING and batch-correction half of the central branch; constructing the
reducing decomposition and proving that its cleaning sets cover every high
odd spike is still the operator content of
`central-adaptive-peeling-or-noncentral-stopping`.

## The zero-boundary Pauli stress test is paid by parity

For the family in
`monotone-anchor-sign-budget-does-not-give-stagewise-coverage`, assume the
parity matrix has bounded nonzero column degree and `M=Theta(L)`.  On block
`j`, choose any original row containing coordinate `B_j`.  Its evaluated
word contains exactly one `X`; every other factor is `Z`, so it has trace
zero and squared distance `2` from the identity.  Hence

```text
E_par >=(1/M)sum_j (1/N) 2=2/M=Theta(1/L).              (CRB7)
```

Batch all central cuts and reset the single anchor coordinate on their
union, which is the identity projection.  Its weighted coordinate density
is `1/L`, and its average squared generator displacement is exactly `2/L`.
Thus `(CRB7)` pays the batch reset at the correct scale even though
one-at-a-time operator coverage required `N` cuts.  If additional original
rows are bad, parity only pays more.

This audit does not invoke the existing projective-Pauli rounding theorem;
it uses only one trace-zero parity word per central block and the weighted
reset ledger.
