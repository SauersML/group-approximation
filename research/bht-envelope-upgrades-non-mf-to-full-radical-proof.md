---
rg: 2
id: bht-envelope-upgrades-non-mf-to-full-radical-proof
kind: route
title: Turn trivial normal intersection into total MF-target collapse
target: bht-envelope-upgrades-non-mf-to-full-radical
requires:
  - bht-trivial-normal-intersection-envelope
  - mf-positive-controls
  - fp-quotient-iff-kernel-finitely-normally-generated
artifacts:
  - research/artifacts/property-t-free-mf-envelope-calculus-2026-08-30.md
---

Apply `bht-trivial-normal-intersection-envelope` to `Gamma`.  It gives an
embedding `Gamma <= P`, with `P` finitely presented, such that

```text
N normal in P and N != P  implies  N intersect Gamma = 1.       (1)
```

Let `phi:P -> A` be a homomorphism to an MF group.  If `phi` were nontrivial,
then `ker(phi)` would be a proper normal subgroup of `P`.  By `(1)`, the
restriction `phi|Gamma` would be injective.  Thus `Gamma` would be isomorphic
to a subgroup of the MF group `A`, and `mf-positive-controls` would make
`Gamma` MF, contradicting the hypothesis.  Hence every such `phi` is
trivial, which is exactly

```text
Rad_MF(P)=P.                                                   (2)
```

Now let `q:P -> Q` be any quotient map.  Every homomorphism `psi:Q -> A` to
an MF group has `psi q=1` by `(2)`, and surjectivity of `q` gives `psi=1`.
Consequently `Rad_MF(Q)=Q`.  If `Q` is nontrivial, it cannot itself be MF:
otherwise its identity homomorphism would be a nontrivial homomorphism to an
MF group.  Notice also that if `Q=P/N` is nontrivial, then `N` is proper and
`(1)` says directly that the image of `Gamma` in `Q` is embedded.

It remains only to justify the simple-quotient refinement.  Since `P` is
finitely presented, it is finitely generated.  A union of a chain of proper
normal subgroups cannot equal `P`: if it did, one member of the chain would
contain a finite generating set of `P` and hence equal `P`.  Zorn's lemma
therefore supplies a maximal proper normal subgroup `M`.  Then `P/M` is
nontrivial, finitely generated and simple; the preceding paragraph gives
its full MF radical and the embedded copy of `Gamma`.  Finally `(BMS3)` is
exactly `fp-quotient-iff-kernel-finitely-normally-generated`.  ∎

## Provenance boundary

This proof is entirely Property-`(T)`-free.  Substituting a concrete seed
whose *known proof* of non-MF uses Kazhdan transport does not erase that
upstream dependence.  The theorem therefore strengthens every future
Property-`(T)`-free seed immediately, but cannot create the first such seed
from an MF or merely non-residually-finite input.
