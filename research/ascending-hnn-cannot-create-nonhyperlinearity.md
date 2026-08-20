---
rg: 2
id: ascending-hnn-cannot-create-nonhyperlinearity
kind: claim
title: An injective ascending HNN extension cannot create nonhyperlinearity from a hyperlinear base
distinct_from:
  pure-abelian-ascending-hnn-transport-is-amenable: that proves the abelian-base mapping torus is itself amenable; this permits an arbitrary hyperlinear base and concludes hyperlinearity by extension permanence.
  ascending-hnn-action-iff-iterated-cosets: that characterizes soficity of one coset action; this concerns hyperlinearity of the whole mapping-torus group.
  proposed-twisted-clifford-substitution-needs-endomorphism-audit: that audits whether the proposed formula defines an injective endomorphism; this shows that even a successful audit cannot make the HNN step the first source of nonhyperlinearity.
---

Let `K` be hyperlinear and let `phi:K->K` be injective.  Then the ascending HNN
extension

```text
G=<K,t | t k t^(-1)=phi(k), k in K>                       (AHC1)
```

is hyperlinear.

Indeed the kernel `N` of the height map `G->Z` is the increasing union of
stable-letter conjugates of `K`.  It is therefore hyperlinear, and `G/N=Z` is
amenable.  Hyperlinear-by-amenable group extensions are hyperlinear.

Consequently `(AHC1)` is nonhyperlinear only if its base `K` is already
nonhyperlinear.  A twisted substitution stable letter may repackage a known
obstruction or improve a profile, but it cannot manufacture the first
nonhyperlinear group from a hyperlinear Thompson--Clifford base.  Any proposed
finite-dimensional HS anomaly for the HNN group would, through this
contrapositive, already prove the base nonhyperlinear; the stable letter adds
no logical leverage toward the existence goal.

Primary source for the extension theorem: Arzhantseva--Berlai--Finn-Sell--Glebsky,
*Unrestricted wreath products and sofic groups*, Corollary 1.1,
arXiv:1802.04688.

