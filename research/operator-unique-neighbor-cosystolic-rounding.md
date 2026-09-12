---
rg: 2
id: operator-unique-neighbor-cosystolic-rounding
kind: claim
title: Operator-valued cosystolic expansion rounds the repeated LDPC presentation on the same Hilbert space
distinct_from:
  unique-neighbor-ldpc-checks-force-dense-noncommutation: that is an exact support theorem; this asks for a dimension-independent normalized-HS correction modulus.
  quadratic-repetition-supports-complete-commutation-overlay: that removes all exact contextual quotients; this is the missing stability statement for approximate representations.
  sparse-clifford-cycles-refute-average-commutator-rounding: that refutes the assertion without parity faces; this includes the LDPC faces in the energy.
---

OPEN.  Choose a bounded-check binary code family whose Tanner complexes have
a uniform operator-valued local-testability/cosystolic constant.  For the
quadratically repeated occurrence reflections, let

```text
E = E_equality + E_local-PVM + E_parity + E_complete-pair. (OUC1)
```

The required condition is a dimension-independent modulus `omega(eps)->0`
such that every tracial matrix representation with `E<=eps` admits, on the
same Hilbert space, a joint PVM `(P_c)_(c in C)` supported on codewords and
coordinate reflections

```text
Q_i' = sum_(c in C) (-1)^(c_i) P_c
```

with average squared normalized-HS displacement at most `omega(eps)` from
the occurrence reflections.

This is an operator `1`-cosystolic expansion statement for the presentation
two-complex.  For fixed `j`, the derivation

```text
delta_j(X)=[X,Q_j]
```

linearizes a bounded parity face by the Leibniz rule.  When face defects and
commutators are small, the row `(delta_j(Q_i))_i` approximately obeys the
classical parity checks, up to bounded local and quadratic errors.  A
classical locally testable code estimate can therefore control distance to
an operator-valued code row.  One then still needs the complete-pair or
exterior sampler to kill the resulting Lie-algebra-valued code kernel and a
bootstrap that improves small commutators to zero-distance from a joint PVM.

At exact parity,
`adjoint-parity-defects-form-tanner-fundamental-cone` makes this precise:
the squared commutator magnitudes lie in the Tanner fundamental cone, so
expander-code pseudoweight is the strongest purely classical magnitude
input naturally available.  The naive threshold/layer-cake upgrade fails.
`commutator-threshold-sets-need-not-be-stopping-sets` gives one exact parity
face with magnitude vector `(4,2,2)`, whose high-level set is a singleton.
Different local character atoms can therefore pay the required partner
commutator on different spectral pieces.  The missing cosystolic estimate
must align or correct those operator-valued pieces; support expansion alone
cannot do so.

Ordinary good-LDPC distance and unique-neighbor stopping expansion prove only
`unique-neighbor-ldpc-checks-force-dense-noncommutation`; they do not provide
this norm estimate.  Conversely the parity term in `(OUC1)` is essential:
`sparse-clifford-cycles-refute-average-commutator-rounding` has vanishing
complete-pair energy but stays a constant distance from all commuting
tuples.  Thus the exact new analytic target is an operator-valued LTC plus
kernel-killing bootstrap, not generic almost-commuting stability.

The desired decoder is strictly weaker than a uniform quadratic adjoint
gap.  `tanner-separated-codewords-create-dihedral-soft-mode` gives exact
parity representations in which the face-Hamiltonian gap vanishes through
two nearby reflections generating `D_infinity`.  Their complete-pair energy
is `O(theta^2)`, but they are made commuting by an `O(theta)` correction.
Thus this soft mode is compatible with a decoder having
`omega(epsilon)=O(sqrt(epsilon))`; it refutes only attempts to derive the
decoder from classical LDPC parameters via a uniform `(GFP3)`.  Either the
selected code must exclude the separated-codeword quotient, or the proof
must explicitly correct such amenable soft sectors before applying a gap on
the remaining representation.

There is no additional exact atlas-agreement obstruction hidden in the face
PVMs.  `binary-face-pvm-is-determined-by-coordinate-reflections` reconstructs
each bounded binary face from its coordinate marginals, and
`complete-overlay-glues-exact-ldpc-face-pvms` constructs one global code PVM
at zero defect.  Hence an agreement theorem for separate face gauges would
attack the wrong object.  The unresolved estimate is precisely uniform
approximate correction of the shared coordinate reflections; after that,
the bounded faces follow by the Lipschitz reconstruction formula.

The canonical randomized sequential-product POVM does not bypass this gate.
`sequential-pinchings-have-sharp-linear-disturbance-loss` computes its
marginals on the sparse Clifford cycle: every order has average disturbance
at least `1/2`, a random order has expectation `2/3`, but the complete-pair
energy is only `8/L`.  Subsequent POVM orthogonalization cannot recover the
original tuple because any PVM output has commuting marginals.  Therefore
the LDPC parity/fundamental-cone structure must be used inside a spectral-
mixture alignment or correction step before sequential measurement; generic
random ordering necessarily pays the forbidden factor `L`.

A parity-aware alternating-projection route is now reduced to one explicit
spectral hypothesis.  `gapped-face-pinchings-give-same-hilbert-code-pvm-rounding`
proves the desired correction if the average whole-face pinching Hamiltonian
has a uniform gap above the common commutant, after
`repeated-ldpc-shared-face-marginal-synchronization` has produced literal
shared face marginals.  Conditional expectation then
sends each coordinate into the **center** of that commutant, so spectral-sign
rounding really yields one commuting tuple; classical LTC decoding finishes
the code support.  The adjoint-gap side is now supplied by
`quadratic-redundant-check-overlay-gives-uniform-face-gap`: quadratic
repetition permits all pairwise sums of original parity checks as bounded
faces, and these faces abelianize the exact face group with a uniform
code-distance gap.  The remaining claim is therefore precisely
`repeated-ldpc-shared-face-marginal-synchronization`.  Ordinary LTC and
unique-neighbor expansion still do not exactify the approximate shared face
tables; that stability step must use the augmented redundant-check system.
