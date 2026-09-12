---
rg: 2
id: finite-input-no-shift-bijection-proof
kind: route
title: Count the trivial group and the naturals
target: finite-input-has-no-shift-bijection
requires: []
---

Present `1` by the empty finite presentation.  Its word problem is decided
by always answering yes.  Every map from its one-element underlying set has
image of cardinality at most one, while `N` contains at least two elements.
Hence no map `1 -> N` is surjective, so no such map is a bijection.  This is
exactly a counterexample to the quantification in
[[shift-higman-compiler]]. `∎`

