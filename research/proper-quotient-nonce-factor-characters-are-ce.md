---
rg: 2
id: proper-quotient-nonce-factor-characters-are-ce
kind: claim
title: Every proper quotient of a regular-or-finite-dimensional character-rigid group has only CE factorial characters
distinct_from:
  factor-universality-character-rigidity-implies-nonhyperlinear: that puts universality and rigidity on the same group; this transfers one named non-CE factorial character backward through a quotient and detects its kernel.
  factor-universal-quotient-of-character-rigid-group-is-faithful: that assumes the whole quotient is factor-representation universal; this needs only one non-CE factorial character on the quotient and therefore identifies the sharp character-level obstruction.
  ah-groups-fail-regular-fd-character-rigidity: that pulls back the regular character of an infinite ICC quotient; this works for finite kernels, non-ICC quotients, and arbitrary nonregular non-CE factorial characters.
  standard-permanence-does-not-rigidify-the-cdi-image: that audits whether rigidity can be imported to one representation-dependent image; this classifies the entire quotient face of every genuinely character-rigid source.
---

Let `G` be countable and suppose every extremal character of `G` is either
the regular character or the character of a finite-dimensional factor
representation.  If

```text
q:G -> K
```

is a proper surjection, then every extremal character of `K` has a
Connes-embeddable GNS factor.  Equivalently, if `K` has even one extremal
character whose GNS factor is non-Connes-embeddable, every surjection
`G -> K` is an isomorphism.  In that case the character is the regular
character of `K`, and `K` (hence `G`) is nonhyperlinear.

This is the sharp character-level form of
`factor-universal-quotient-of-character-rigid-group-is-faithful`.
Factor universality is used there only to manufacture one non-CE factorial
character.  Once such a character is named, neither universality nor an ICC
hypothesis on `K` is needed.

## Construction audit

The statement rules out all quotient-based splices at once.

* In a nontrivial split extension `N rtimes K`, including an ordinary or
  permutational wreath product, the actor projection has kernel `N`.  If
  `K` carries a non-CE factorial character, the extension cannot have the
  regular-or-finite-dimensional character dichotomy.  This remains true
  when `N` is finite or central and when `K` is not ICC, cases not covered
  by pulling back a quotient regular character.
* A relative character-rigidity theorem which controls only characters
  nontrivial on `N` cannot repair the split construction.  The obstructing
  pullback is identically one on `N`; it lies exactly in the omitted
  quotient face.
* A simple-envelope theorem embeds `K` into a simple group `S`; it does not
  extend a prescribed factorial character of `K` to `S`.  If the embedding
  is supplemented by a retraction `S -> K`, then the retraction is a proper
  quotient unless it is an isomorphism, so the theorem applies immediately.
  Thus adding a retraction, lamp-killing map, or semidirect projection cannot
  transport a non-CE payload into a character-rigid host.
* In particular, taking `K` non-elementary acylindrically hyperbolic does
  not produce an example.  CDI factor universality supplies a non-CE
  factorial character of `K`, so any surjection from a character-rigid `G`
  would be an isomorphism.  Character rigidity would then transfer to `K`,
  contradicting `ah-groups-fail-regular-fd-character-rigidity`.  Thus the
  proposed AH quotient does not merely lack a known construction: under the
  stated full character dichotomy it cannot exist.
* Finite-index induction is genuinely outside this no-go: it transports a
  representation rather than factoring it through a quotient.  Its exact
  positive conclusion remains
  `finite-index-induction-transfers-non-ce-factor`; simple envelopes and
  infinite-index coinduction do not provide that missing finite-index host.

Consequently, an explicit regular-or-finite-dimensional character-rigid
group with a factor-universal quotient would not be an intermediate
construction: the quotient map would already be an isomorphism and the
group would already be the desired nonhyperlinear group.  Wreath,
semidirect, retracting-envelope, and relative-rigidity constructions cannot
make this route easier by allowing a nontrivial kernel.
