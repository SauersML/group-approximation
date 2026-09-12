---
rg: 2
id: fanizza-native-join-tree-groupification-route
kind: route
title: Groupify the semantically reduced native Fanizza join tree
target: fanizza-native-signal-groupification
requires:
  - pauli-guard-collapses-c18-to-three-bit-recurrence
  - join-tree-bcs-has-explicit-signed-hecke-atlas
  - gauge-doubling-gives-selector-flip-symmetries
  - native-fanizza-join-tree-prescribed-word-realization
  - kleene-completeness-needs-only-a-nontrivial-exact-representation
---

Retain the Pauli, conjugacy, involution, and commutator equations as ordinary
group relations.  Replace C18 by its exactly equivalent three-bit recurrence
predicate.  The remaining four nonlinear contexts admit a join tree, so use
the explicit signed-Hecke induction without any chord or cycle cell.

Apply the prescribed-word realization to couple its compatible marginals to
the native machine words.  The finite-dimensional decoder then supplies the
moduli required by `fanizza-native-signal-groupification`; exact HALT
completeness uses gauge covariance and countable amplification.  Feeding this
compiler into `nonhyperlinear-from-fanizza-native-signal` yields a finitely
presented nonhyperlinear group.
