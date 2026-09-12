---
rg: 2
id: finitely-generated-rf-automorphism-mapping-torus-is-rf-proof
kind: route
title: Separate kernel elements through characteristic finite quotients
target: finitely-generated-rf-automorphism-mapping-torus-is-rf
requires:
  - mf-positive-controls
---

Write an element of `G` as `(k,n)`.  If `n` is nonzero, choose an integer
`m>=2` not dividing `n`; the exponent map followed by `Z->Z/mZ` separates
`(k,n)` from the identity.

It remains to separate `(k,0)` with `k` nontrivial.  Residual finiteness gives
a finite-index subgroup `H<=K` with `k` not in `H`.  Put `d=[K:H]` and let

```text
C = intersection { J<=K | [K:J] <= d }.
```

A finitely generated group has only finitely many subgroups of each bounded
index: an index-`e` subgroup is the stabilizer of a point in a homomorphism
to `Sym(e)`, and there are only finitely many such homomorphisms from a fixed
finite generating set.  Hence `C` has finite index.  It is characteristic,
because every automorphism permutes the displayed finite family, and
`C<=H`, so `k` does not lie in `C`.

The automorphism `phi` therefore descends to the finite group `F=K/C`.
Its induced automorphism has finite order, say `r`.  There is a homomorphism

```text
K semidirectProduct_phi Z  ->  F semidirectProduct Z/rZ
```

which sends the stable letter to the generator of `Z/rZ`; the target is
finite and the image of `(k,0)` is nontrivial.  Thus every nonidentity
element of `G` survives in a finite quotient, proving residual finiteness.

Every residually finite group is MF, so the identity embedding of `G` into
an MF target shows that its MF radical is trivial.
