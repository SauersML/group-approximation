---
rg: 2
id: approximate-bernoulli-extraction-cartan-reduction-proof
kind: route
title: Separate finite-window diagonalization from simultaneous normalizer extraction
target: approximate-bernoulli-lamp-extraction-is-cartan-completion
requires:
  - arithmetic-global-pvm-does-not-bypass-coset-action-gate
  - diagonal-normalizer-rigidity
  - scalar-trace-of-diagonal-normalizer-is-permutation-blind
  - simple-lamp-gauge-rigidity-reduces-to-actor-classicalization
---

`arithmetic-global-pvm-does-not-bypass-coset-action-gate` proves the first
half directly: Fourier transformation of an exact lamp PVM gives finite
weighted atoms, canonical lamp moments give cylinderwise Haar convergence,
and actor relators give only asymptotically equivariant transports.  Its
proof explicitly leaves the transports approximate.

If a single invariant diagonal ultraproduct is additionally supplied, then
`diagonal-normalizer-rigidity` applies to every actor unitary.  It produces
permutation normalizers up to diagonal phases, and the phases commute with the
lamp image, so the permutations alone implement the action.  Conversely,
coherent finite probability spaces with multiplicative permutation actions
generate precisely such an invariant diagonal ultraproduct after passage to
the ultralimit.  Thus the missing coherent-action assertion is the invariant
diagonal/Cartan completion step, not a consequence of Fourier convergence or
Portmanteau.

The scalar-trace firewall shows why canonical trace separation does not fill
this gap: a balanced diagonal sign has trace zero but identity permutation
part.  Conditional-expectation control is therefore part of the coherent
Cartan completion, not a consequence of scalar regular-character data.

The final requirement records the multiplicity-gauge version of the same
obstruction.  It also prevents an incorrect appeal to amenable-kernel
permanence: actor classicalization is still the missing operation.
