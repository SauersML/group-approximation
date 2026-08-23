---
rg: 2
id: atlas-kernel-relators-couple-cross-gram-to-four-pauli
kind: claim
title: Full Atlas kernel relators couple the compulsory overlap to all four Pauli words
distinct_from:
  compulsory-pauli-cross-gram-is-four-word-intertwiner: that incorrectly asks the local raw/comb packet alone to supply the coupling and is refuted by the canonical rectangular model.
  atlas-five-row-operator-phase-lift: that controls five global covariance energies; this asks only for four mixed intertwining residuals on the already forced positive overlap.
  four-pauli-cross-gram-exact-completeness-firewall: that proves ordinary quotient-algebra coupling is impossible; this retains only the finite-matrix rank/multiplicity extraction which can evade the exact regular model.
  atlas-pauli-rank-ledger-has-finite-rectangular-model: that rules out bare carrier-rank divisibility and separate Pauli module degrees; this still asks whether mixed full-kernel relations select a non-functorial finite coordinate.
---

**OPEN, FINITE-MATRIX-ONLY.**  Work in the regular-`A_8` microstate normal form of
`leavitt-regular-atlas-hyperlinearity-criterion`, and assume the complete
fixed normal-generating packet `bar_S` has defect `delta`.  Form the two
compressed raw/comb coefficient contractions `X_0,X_1` and choose the heavier
ordered overlap

```text
T=X_j^*X_i,
||T||_2^2>=5/64-o_delta(1).                            (AKC1)
```

Using at least one relation in `bar_S` outside the local one-cell Pauli
tables, decode four contractions `C_1,...,C_4` in one recovered
`M_2 tensor I` coefficient algebra and the four transverse Pauli target
words `D_1,...,D_4` such that

```text
sum_(k=1)^4||D_kT-TC_k||_2<=omega(delta),              (AKC2)
||s4(D)-8D_1D_2D_3D_4||_2<=omega(delta),              (AKC3)
```

for one dimension-independent modulus `omega(delta)->0`.

The same orientation and the literal overlap `(AKC1)` must occur in all four
rows.

The Lin cross-Gram package removes a formerly separate analytic step after
this point. By `two-transport-cross-gram-has-a-fixed-mass-reducing-corner`
and `positive-cross-gram-state-rounds-to-common-pvm`, `(AKC1)--(AKC2)` would
already produce a fixed-density common packet corner; near-full overlap and
global carrier rounding are unnecessary. It does not help prove `(AKC2)`.
The exact-factor and double-gauge firewalls below remain attacks on precisely
that same-Gram mixed covariance certificate.

## Exact algebraic interpretation is refuted

`four-pauli-cross-gram-exact-completeness-firewall` gives, already at zero
error,

```text
sum_(k=1)^4 ||D_kT-TC_k||_2^2 >= 5/2304.              (AKC4)
```

Consequently `(AKC2)` cannot be obtained as a fixed quotient group-algebra
identity, a coefficient-ideal membership certificate, or a van Kampen
consequence of the full kernel packet.  Any such consequence would also hold
in the exact regular quotient representation, where all kernel defects are
zero and the canonical cross-Gram overlap remains positive, contradicting
`(AKC4)`.  The exact rectangular packet is therefore not merely a warning
against using the local one-cell relations: exact completeness rules out
every ordinary algebraic derivation from the full kernel as well.

## Remaining target

The source factor and common carrier in `(AKC2)` must be extracted by a
genuinely finite-coordinate operation: normalized-rank separation,
finite-multiplicity balance, or an equivalent matrix-integrality theorem
which has no analogue in the exact regular von Neumann model.  After that
finite-only extraction, the mixed hard/comb/interior relations may control
the four residuals on the selected matrix carrier.  The load-bearing claim is
now precisely this finite-multiplicity extraction; no fixed algebraic kernel
identity can replace it.

Bare integrality is already insufficient.
`atlas-pauli-rank-ledger-has-finite-rectangular-model` computes that every
fixed denominator through `64` clears in the canonical dimensions
`20160 k`; on the trace-quarter carrier both the source `M_2` type and target
`M_4` type occur with integral multiplicity.  It also gives exact finite
rectangular Pauli models at every amplification.  Thus the remaining
``finite-multiplicity'' operation cannot mean a divisibility check on the
separate packet types.  It must extract a mixed singular subspace or relative
multiplicity coordinate from full-kernel operators, with a uniform positive
normalized-HS consequence.

Nor can that coordinate be a determinant phase or a Fredholm index of the
phase-cycle operators.  `atlas-phase-cycle-determinant-is-gauge-trivial`
shows that every phase edge has determinant one identically, while scalar
rotation changes `det U` arbitrarily without changing any nonlinear cycle or
any singular value of the additive rows.  The viable finite-only object has
therefore narrowed to relative singular *spaces* (or an equivalent
noncommutative-rank/shrunk-subspace certificate), not scalar determinant,
index, or separate-rank data.

There is a larger gauge than the scalar circle.
`atlas-full-relator-data-factor-through-double-commutant-gauge` proves that
every word evaluation is unchanged up to conjugacy under

```text
U -> D U C,       D in rho_1(A8)', C in rho_2(A8)'.
```

Hence no raw multiplicity basis, coefficient of `U`, or one-sided singular
vector is authenticated by the full kernel.  The smallest admissible objects
are simultaneous singular/range data of mixed compressions `P_i U Q_j`,
considered equivariantly under this double gauge.  The remaining target must
derive its common four-word carrier from such a family, not from a pinned raw
coordinate.

Even the complete scalar mass profile of that family is insufficient.
`atlas-a8-mixed-block-transport-has-permutation-models` constructs an exact
finite permutation unitary for every rational transport plan on the 448
minimal regular-A8 Fourier corners.  Thus the mixed full-kernel step must
control simultaneous *directions* or singular ranges inside `P_i U Q_j`, not
only their ranks or squared-HS masses.  On the positive side, any strict Hall
deficit extracted from those ranges automatically has gap at least
`1/20160`; the remaining difficulty is qualitative range deletion, not the
size of the final constant.

The ordinary full-word Jacobian cannot perform this deletion at an exact
aligned frame.  `atlas-aligned-word-jacobian-has-full-multiplicity-absorber`
shows that every actual word derivative factors as a finite
representation-coordinate map tensored with the identity on the complete
multiplicity matrix space.  The compulsory scalar-gauge tangent then expands
to arbitrary multiplicity matrices on every aligned block.  Each surviving
block has full collective range and the aligned support is Hall balanced.
Therefore the remaining finite-only extraction must use nonlinear secant or
singular-space data away from the aligned tangent stratum; stacking more
kernel-relator differentials cannot establish `(AKC2)`.

Even exact finite secants inside a common word-value fiber are insufficient.
`atlas-word-fiber-secants-have-full-multiplicity-absorber` computes their
span at an aligned frame as `U_0 rho_2(A8)'`.  It contains arbitrary
multiplicity matrices on every compulsory aligned block and an invertible
operator.  What remains is therefore a transverse quantitative singular
invariant on the quotient by this exact commutant orbit, not a Jacobian or a
same-fiber chord minor.

The aligned transverse quotient itself is not the answer.
`atlas-aligned-quotient-spectrum-cannot-reach-low-defect` shows that its
positive singular spectrum is automatically independent of multiplicity,
but the actual `19243` centrality consequence keeps every low-defect frame a
fixed distance `sqrt(2)/16` from that entire aligned quotient.  Therefore the
remaining invariant must live globally on this remote nonlinear branch; a
finite aligned irrep-pair Hessian, even with a strict spectral gap, cannot
extract the carrier in `(AKC2)`.
