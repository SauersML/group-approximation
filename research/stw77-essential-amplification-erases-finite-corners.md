---
rg: 2
id: stw77-essential-amplification-erases-finite-corners
kind: claim
title: Essential amplification erases the intrinsic finite-corner obstruction in STW77
distinct_from:
  stw77-bounded-operator-target-case: that proves stability once the range representation is essential; this shows essentiality can always be manufactured by infinite amplification and therefore does not descend to the original target.
  stw77-quotient-properness-does-not-lift-coordinatewise: that hides finite coordinate packets in a quotient ideal; this shows the opposite failure, where a faithful ambient representation turns every intrinsic finite support into a properly infinite operator.
  stw77-fd-commutant-splitting-iff-proper-supports: that identifies the intrinsic obstruction in the original target; this proves that faithful essential amplification deletes it.
---

**ESTABLISHED.** Let `A` be separable and unital, let `B` be unital,
and let

```text
phi:A->B
```

be any unital homomorphism. Choose a faithful unital representation

```text
pi:B->B(K)
```

and form its countable amplification

```text
rho:B->B(K tensor l2),       rho(b)=pi(b) tensor 1.       (EAF1)
```

Then `rho(B)` is essential: it has zero intersection with the compact
operators. Consequently every nonzero positive element of
`(rho phi)(A)` is properly infinite in `B(K tensor l2)`, and

```text
rho phi:A->B(K tensor l2)
```

is `O_infinity`-stable by [[stw77-bounded-operator-target-case]].

Thus a bounded-operator envelope with coordinatewise essential
representations exists for **every** unital map. It uses neither nuclear
dimension zero nor proper infiniteness in the original target, so its
stability cannot by itself prove the STW77 conclusion in `B`.

The loss is exact already on one finite-dimensional model. Let
`D subset B` be unital and finite dimensional. Infinite amplification sends
every nonzero minimal projection of `D` to an infinite-rank, hence properly
infinite, projection in `B(K tensor l2)`. Therefore

```text
B(K tensor l2) intersect rho(D)'
```

contains two isometries with orthogonal ranges. If some minimal projection
of `D` is not properly infinite in `B`, however, then

```text
B intersect D'
```

contains no such pair, by
[[stw77-fd-commutant-splitting-iff-proper-supports]].

The same firewall applies to a product envelope: repeating `(EAF1)` in
arbitrarily many coordinates gives a constant product map whose nonzero
positive image elements have constant proper-infiniteness witnesses and
which is `O_infinity`-stable by
[[stw77-products-of-bounded-operator-targets-solve-map]]. The central
isometries live in the amplified product, not in `B`.

Hence the zero-colour case cannot be solved merely by lifting its local
finite-dimensional models to coordinatewise essential representations and
applying the product theorem. A successful envelope argument must add a
norm-controlled return mechanism that transports the central split back to
`B`; equivalently, it must merge or eliminate the intrinsic nonproper model
supports. That is precisely the unresolved proper-support clustering
problem, not a consequence of essential amplification.

DERIVATION
[[stw77-essential-amplification-firewall-proof]]
