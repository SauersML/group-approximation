---
rg: 2
id: term-pairing-holonomy-no-go-proof
kind: route
title: Track the vertex-potential cocycle required by a tagged projection
target: term-pairing-does-not-bypass-signed-hecke-holonomy
requires: []
---

Expand `WYW*` using `W=sum_i h_iE_ii`.  Its `(i,j)` coefficient is
`y_ij h_i h_j^(-1)`, so the inverse and triangle identities `(TPH3)` are
immediate.  Conversely those identities are the cancellation used when
expanding the adjoint and square of the tagged matrix; arbitrary independent
occurrence tags do not inherit it.

Pairing the terms of one linear relation imposes only the chosen word
equalities.  Pairing the additional star and idempotence residuals produces
the compatibility equations among the same tags.  Solving vertex potentials
along a forest is definitional.  Multiplying the equations around a cycle
eliminates those potentials and leaves its coefficient holonomy word.

Finally, equation `(TPH5)` is itself a two-term coefficient pairing and
collapses a prescribed nonidentity coefficient element.  Thus coefficient
pairing alone has no relative-injectivity guarantee.  Common padding is only
conjugation, while independent padding abandons the projection cocycle and
must restore it by the same cycle relations.  These observations prove every
clause of the claim without an external group-equation theorem.
