---
rg: 2
id: kawauchi-weak-kervaire-rests-on-unresolved-inputs
kind: claim
title: The claimed weak-Kervaire proof rests on unresolved four-dimensional inputs
invalidates: [kl-via-weak-conjecture-import]
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Kawauchi, arXiv:2303.13728, *Kervaire conjecture on weight of group via
fundamental group of ribbon sphere-link* (submitted 24 March 2023, last
revised 1 April 2024), abstract read from source 2026-08-17: "Kervaire
conjecture that the weight of the free product of every non-trivial group and
the infinite cyclic group is not one is confirmed by confirming Conjecture Z
of a knot exterior."

Its supporting manuscript, arXiv:2212.02617, *Ribbonness of Kervaire's
sphere-link in homotopy 4-sphere and its consequences to 2-complexes*,
abstract read from source the same day, states its own inputs: "In the use of
the smooth unknotting conjecture and the smooth 4D Poincaré conjecture, any
such sphere-link is shown to be a sublink of a free ribbon sphere-link in the
4-sphere", together with the assertion that "the compact complement of every
ribbon disk-link in the 4-disk is aspherical" and a reference to "the
Whitehead aspherical conjecture".

So the chain replaces one open problem by several stronger claimed
resolutions rather than closing it independently.  This graph therefore does
not carry the weight-one statement as established, and
`kl-via-weak-conjecture-import` is dead.

## What this claim is and is not

It is a **dependency audit**, verified at the level of the manuscripts' own
abstracts: the claimed proof declares its reliance on the smooth unknotting
and smooth 4D Poincaré conjectures.  It is *not* an assertion that any
statement in those papers is false, and it is not a refereeing verdict.
Should the four-dimensional inputs be independently settled, the right move
is to re-audit rather than to treat this node as a permanent obstruction.

Two further reasons the import would not help here even if granted, both
recorded elsewhere so that this node stands on the dependency question alone:
the statement proved is the weight form, not coefficient injectivity
(`weak-kervaire-transfers-only-at-unimodular-degree`), and current primary
literature continues to state the one-variable conjecture as open
(`kervaire-laudenbach-nonsingular-conjecture`, quoting arXiv:2606.24741v2 of
10 August 2026).
