---
rg: 2
id: coherent-word-oracles-cannot-branch-on-their-own-tracial-profile
kind: claim
title: Coherent word oracles cannot branch on their own tracial profile
distinct_from:
  amplification-natural-words-cannot-read-packet-multiplicity: that treats finite authenticated word algebras and anonymous multiplicity; this treats an adaptive-looking coherent query circuit, including fixed controls and gapped functional calculus.
  post-candidate-nemesis-has-a-finality-dilemma: that rules out externally appending a challenge after reading a rational tuple; this rules out feeding an internal measurement or moment back into a challenge inside one fixed presentation.
  lin-introspection-payload-is-global-gauge-covariant: that positively transports a precompiled question/answer payload through one extraction isometry; this rules out using that payload to perform tomography and then choose a new matrix-dependent question.
---

**ESTABLISHED NO-GO (black-box scope stated explicitly).**  Start from a
finite unitary tuple `U=(U_s)` and allow a finite coherent query circuit made
from fixed group-word evaluations, adjoints, sums and products, fixed finite
control ancillas, and fixed continuous functional calculus.  Fixed-gap
spectral projections and polar signs are also allowed on the domain where
their prescribed gap holds.  Every output `Q` is blockwise and
amplification natural:

```text
Q(U direct-sum V) = Q(U) direct-sum Q(V),
Q(U tensor I_l)   = Q(U) tensor I_l,                         (CWO1)
```

up to the fixed permutation which groups the control ancilla with each
summand.  The same identities hold for every intermediate coherent control
register.

Consequently such a circuit may query algebraic word values and fixed local
spectral predicates, but it cannot:

* read normalized moments `tr(w(U))`, spectral multiplicities, ambient
  dimension, or the size of an anonymous commutant factor and feed the answer
  back into one operator branch;
* measure a control, postselect an outcome, and impose only the corresponding
  challenge; or
* manufacture an independent tensor copy of the unknown tuple.

Indeed normalized trace and measurement probabilities are external scalar
functionals, not operators produced by the allowed calculus.  Coherent
control keeps all branches as reducing blocks.  Moreover the requested map
`U |-> U tensor U` does not preserve direct sums: it creates the cross terms
`U tensor V` and `V tensor U`, so it is not a one-copy word operation.
Adjoining a second commuting tuple does not repair this: group relations can
force commutation and selected correlations, but not tracial independence or
equality with a canonical clone of arbitrary input matrices.

The normalized squared defect and every fixed word moment of a direct sum are
convex combinations of the corresponding block statistics.  Hence a
``fingerprint, then choose its nemesis'' program compiled only from these
coherent queries merely runs the already precompiled challenges blockwise;
it cannot choose one global challenge from the empirical profile of the
whole approximation.

This no-go does **not** rule out a finite self-test whose challenge is fixed in
advance and sound on every extracted block, nor a genuine representation-type
conductor already encoded by a named word.  Those are blockwise mechanisms.
It rules out the proposed approximation-specific oracle: tomography,
measurement feedback, full-commutant search, or tensor-copy fingerprinting
cannot be obtained from ordinary group relations without an additional
trace-to-operator/compiler primitive.  Supplying such a primitive is exactly
the missing constant-sound groupification problem, rather than free
self-awareness.
