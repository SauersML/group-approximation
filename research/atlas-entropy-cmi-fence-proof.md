---
rg: 2
id: atlas-entropy-cmi-fence-proof
kind: route
title: Compare integer covering numbers with face nonemptiness and evaluate CMI in the Leavitt trace
target: atlas-entropy-and-cmi-stop-at-face-emptiness
requires:
  - atlas-six-relator-hyperlinear-escape-test
  - atlas-hyperlinear-enemy-is-map-or-large-simple
  - atlas-six-relator-leavitt-tracial-countermodel
  - atlas-full-relator-data-factor-through-double-commutant-gauge
---

The displayed definition `(AEC1)` is already exactly a positive-energy
six-relator microstate sequence for some fixed `a>0`; no use of the open
five-row inequality is made here.  Such a sequence gives the exact
positive-energy matrix-ultraproduct model.  The hyperlinear escape theorem
identifies that model with the nonempty regular CE trace face.

Under the claim's exclusion of the large finite-simple branch, the dimensions
must tend to infinity.  Otherwise pass to a fixed-dimensional subsequence and
use compactness of the unitary group.  The limiting tuple is a nontrivial
finite-dimensional representation of `Gamma_6`; its finite image has a marked
finite-simple quotient, returning exactly the excluded branch.  Conversely,
the hyperlinear quotient obtained from an unbounded sequence lies in the MAP
branch once the finite-simple alternative has been excluded.  This proves the
equivalence of items 1--3 in the claim.

For every metric space `X`, a `delta`-cover of a nonempty `X` contains at
least one ball.  Hence `(AEC2)` is immediate.  If a raw covering exponent is
strictly negative, the relevant covering number must be zero, so the space
is empty.  Conversely emptiness gives `log 0=-infinity`.  Entropies with a
subtracted ambient or orbital normalization do not retain this elementary
integer threshold: a singleton or a shrinking positive-codimension family
can have a nonpositive normalized value while remaining nonempty.  Therefore
such a value has no implication for the existence required by `(AEC1)`.

For the CMI statement, restrict the trace to whatever finite-dimensional
tensor/register algebra the proposed construction specifies.  It is an
ordinary finite-dimensional state, so strong subadditivity and data
processing apply.  These theorems depend only on positivity and partial
trace, not on Connes embeddability of the ambient factor.  Apply the same
finite construction inside the exact Leavitt tracial model.  Every six-word
constraint is exact there and the five-row witness remains positive, so no
inequality assembled solely from standard CMI rules can separate the two
categories.

Finally the double-commutant gauge acts on every nonempty regular-chart
microstate space without changing a relator defect.  Counting that orbit
measures multiplicity-basis freedom already quotiented by orbital entropy;
it cannot turn a nonempty face into an empty one.  This completes the fence.
