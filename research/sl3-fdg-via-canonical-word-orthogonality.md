---
rg: 2
id: sl3-fdg-via-canonical-word-orthogonality
kind: route
title: Kill every finite-word central separator using canonical trace orthogonality
target: sl3-hnn-finite-window-central-dual-gap
requires: []
---

Proposed mechanism: use a sufficiently large finite mixed Britton trace
window to make every bounded separator in the span of evaluated group words
orthogonal to the lattice generator tuple.  This would force its source
pairing, and hence its matrix-range separation gap, to vanish.

This mechanism is invalidated by
`generator-diagonal-is-a-central-matrix-range-separator`.  The normalized
tuple `B_s=X_s/sqrt(|S|)` lies in the fixed generator-word span, inherits
stable-letter centrality, and has source pairing `sqrt(|S|)` from the
identity products `X_s^*X_s`.  Its gap is at least the squared primal
matrix-range distance divided by `2sqrt(|S|)`.  Hence canonical
nonidentity-word orthogonality cannot remove it; one must raise the support
function by constructing a nearby ucp point.
