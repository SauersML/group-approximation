---
rg: 2
id: llp-hole-via-triangle-relator-local-sections
kind: route
title: Local ucp sections of the relator extension give the LLP witness
target: non-rf-kazhdan-group-with-llp-full-c-star-algebra
requires:
  - triangle-relator-extension-admits-local-ucp-sections
  - triangle-colimit-llp-reduces-to-relator-local-splitting
  - simple-kazhdan-kac-moody-lattices-exist
---

Let `Lambda` be the lattice supplied by the open requirement, with its
triangle presentation and locally ucp-split relator extension.  By the
equivalence theorem (TC4), `C*(Lambda)` has the LLP (the transfer
lemma consumes the LP of `C*(G_0)` established there).  By
`simple-kazhdan-kac-moody-lattices-exist`, `Lambda` is an infinite
finitely generated (indeed finitely presented) Kazhdan group that is
simple, hence has no nontrivial finite quotients and is not residually
finite.  So `Lambda` witnesses the target: a finitely generated,
non-residually-finite Kazhdan group whose full group C*-algebra has
Kirchberg's local lifting property.
