---
rg: 2
id: stw99-lxxvi-finite-graph-compact-core-proof
kind: route
title: Retain compact cycle cores, cut small spectral slices, realize modules, then recover order
target: stw99-lxxvi-finite-graph-compact-core-cu-regularity
requires:
  - stw99-lxxvi-cactus-enriched-cu-classification
  - stw99-lxxvi-finite-graph-compact-clutching-rigidity
  - stw99-lxxvi-finite-tree-formation-preserves-cu-regularity
  - stw99-lxxvi-circle-formation-preserves-cu-regularity
artifacts:
  - research/artifacts/stw99-lxxvi-finite-graph-compact-core-audit-2026-09-05.md
---

For each positive section `a`, retain the union `K(a)` of circles on
which its actual Cu restriction is nonzero compact. Brown--Ciuperca
Theorem 3.5 gives a uniform spectral gap on each such circle in its
stably finite stabilized section algebra. Taking the minimum over the
finite collection gives a spectral gap, hence a projection class, on
every connected core component. The ADPS circle theorem makes this
core depend only on the pointwise Cu function.

Every cycle not contained in the core has an arbitrarily small positive
spectral value outside the core, or is identically zero. Open a point
there, and repeat until the remaining graph consists of the actual core
components joined by a forest. At most the first Betti number of cuts
are needed. Choose the finite spectral values before the common cutdown.

The ADPS alignment and small-spectrum unitary lemmas make all endpoint
alignment unitaries have zero K1 class at arbitrarily small action cost.
They lift simultaneously through the endpoint quotient of
`Her(q^*b)+C(Y)1`, by lifting exponential factorizations in the identity
component. This permits support zeros and arbitrary endpoint scalar
quotients. Splice on disjoint collars and descend to obtain comparison
downstairs. The graph and its cuts may vary with the error tolerance.

Using the articulation theorem only for one-point gluing, this proves
that equality of pointwise Cu functions and equality of the actual
projection classes on all core components completely detect Cuntz
equivalence. Conversely, interval modules and chosen core projection
modules glue over the finitely many endpoints: stable rank one of the
coefficient turns equal endpoint Cu classes into module isomorphisms.
The finite pullback is countably generated and has the required
restrictions. This proves realization without assuming order reflection
for a general two-endpoint pullback.

A coefficient map inducing Cu and K1 isomorphisms therefore preserves
and realizes all equivalence data. It gives set bijectivity on every
finite graph. For a compact source `p` and a target comparison
`phi_*(p)<=phi_*(x)`, target `(O5)` splits
`phi_*(x)=phi_*(p)+z`. Lift `z` and use set injectivity to get
`x=p+z'`. This proves compact-left order reflection on every finite
graph before any general order reflection is invoked.

For a general source, cut outside its compact cycle core. The compact
core comparisons now reflect by the preceding paragraph; interval
comparisons reflect by the coefficient Cu isomorphism. One-point
gluing gives upstairs comparison, and spectral surgery gives downstairs
comparison. The resulting order isomorphism is a Cu isomorphism.
