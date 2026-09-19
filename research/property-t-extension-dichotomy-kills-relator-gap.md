---
rg: 2
id: property-t-extension-dichotomy-kills-relator-gap
kind: route
title: Combine quotient property T with the virtually free Haagerup action to refute every finite relator Poincare inverse
target: km-triangle-relator-kernel-has-no-relative-gap
requires:
  - simple-kazhdan-kac-moody-lattices-exist
  - triangle-colimit-llp-reduces-to-relator-local-splitting
---

For the normal kernel `K` in `(NRG1)`, relative property `(T)` of `(G_0,K)`
together with property `(T)` of `Lambda=G_0/K` would imply property `(T)` of
`G_0`.  But `G_0` is infinite virtually free and hence admits a proper tree
action, so it has the Haagerup property and is not Kazhdan.  Therefore the
pair has no relative gap.  The almost invariant vectors witnessing this
failure make every fixed finite family of relator words small while remaining
at distance one from the `K`-fixed space, which directly contradicts any
finite-reservoir Poincare estimate `(NRG5)`.
