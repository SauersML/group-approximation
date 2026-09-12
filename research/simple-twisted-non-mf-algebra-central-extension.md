---
rg: 2
id: simple-twisted-non-mf-algebra-central-extension
kind: claim
title: A simple non-MF twisted full algebra makes its central sign extension non-MF
artifacts:
  - research/simple-twisted-non-mf-algebra-central-extension-proof.md
distinct_from:
  central-extension-twisted-sector-criterion: that characterizes MF of an order-two extension by existence of a twisted asymptotic sector when the quotient is MF; this converts C-star simplicity plus failure of C-star MF directly into failure of group MF and does not assume the quotient is MF.
  nonce-twisted-factor-gives-nonhyperlinear-group: that starts from a non-Connes-embeddable twisted von Neumann algebra and targets normalized-Hilbert--Schmidt approximation; this starts from a non-MF full twisted C-star algebra and targets operator-norm matrix coronas.
  nuclear-embeddability-is-inherited-by-subalgebras: that transports embeddability between ordinary C-star subalgebras; this authenticates the projective group generators by cutting a central spectral corner.
---

**ESTABLISHED GROUPIFICATION CRITERION.**  Let `Gamma` be countable and let

```text
omega:Gamma x Gamma -> {+1,-1}
```

be a normalized scalar two-cocycle.  Let

```text
E={+1,-1} x_omega Gamma
```

be its central order-two extension, with central generator `z=(-1,1)`.  If
the full twisted group C-star algebra

```text
A=C^*(Gamma,omega)
```

is simple and is not an MF C-star algebra, then the abstract countable group
`E` is not operator-MF.

Indeed, a faithful group embedding of `E` in a norm matrix corona keeps `z`
nontrivial.  The nonzero `-1` spectral corner of `z` carries an exact
`omega`-projective representation of `Gamma`, hence a unital star-homomorphism
from `A` into a corner of a norm matrix corona.  Simplicity makes that map
injective, contradicting that `A` is non-MF.

## The accompanying firewall

This criterion does **not** turn an arbitrary non-MF unitary-generated
C-star algebra into a non-MF group.  Moreover, the algebra `A` in the
criterion cannot be one of the easy properly infinite or traceless non-MF
examples.  The twisted left regular representation gives a quotient

```text
C^*(Gamma,omega) ->> C^*_r(Gamma,omega).
```

If the full algebra is simple, this nonzero quotient is injective, so full
and reduced twisted algebras coincide.  Consequently `A` has the faithful
canonical trace of the reduced twisted algebra and is stably finite.

Thus this route closes the **groupification** step only for a simple,
stably-finite, non-MF full twisted group algebra.  Producing such an algebra
remains a genuine approximation-theoretic input; `O_2`, other traceless
simple algebras, and arbitrary non-MF quotients of full group algebras do not
satisfy the interface.
