---
rg: 2
id: computation-capacity-operator-ltc-audit-proof
kind: route
title: Assemble the proved rank and capacity endpoints and isolate the common-resource decoder
target: computation-capacity-operator-ltc-audit
requires:
  - gatewise-cook-levin-rank-is-baseline-plus-unsat
  - predicate-rank-gate-doubles-restriction-multiplicity
  - gram-branching-capacity-with-overlap
  - rational-supercritical-branch-certificate
  - strongly-connected-branching-gives-rational-pressure
  - one-sided-pvm-leakage-controls-schreier-multiplicity
  - signed-character-expansion-decodes-operator-parallelograms
  - bounded-degree-left-right-character-code-has-bounded-dimension
  - finite-covariance-energy-sees-only-character-restrictions
---

The first two requirements give the exact gatewise rank and local
Schur-multiplicity identities.  The next three give the rational
branch-capacity inequality once common typed carrier maps and a leakage bound
have been supplied.  The atomic-Schreier requirement gives the independent
square-root-multiplicity inequality once a global character PVM has been
supplied.

The final three requirements locate the decoder frontier.  Signed-character
parallelogram expansion is a genuine dimension-uniform same-Hilbert PVM
decoder, but its bare bounded-degree character code has bounded message
dimension.  Finite lamp covariance has the opposite defect: it sees only
finite character restrictions and is blind inside their fibers.  Hence none
of the listed established claims supplies the growing common resource register
needed by either endpoint.

The target is therefore an audit of implications and missing hypotheses.  Its
operator-LTC statement is explicitly proposed as an open input; this route
does not promote it to a theorem and does not derive nonhyperlinearity.
