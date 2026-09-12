---
rg: 2
id: agent-free-compressor-virtually-free-shadow-proof
kind: route
title: Shift two copies of a common finite cover and exhibit the diagonal stationary section
target: agent-free-compressor-virtually-free-shadow-has-stationary-types
requires: []
---

Let

```text
q_0:C->B,       q_0(b,a,epsilon)=b,
q_1:C->B,       q_1(b,a,epsilon)=a,
```

where the value of `q_1` is viewed in `B` through `A<=B`.  Define `theta` on
the free factors `C_0,C_1` by `q_0,q_1`, respectively.  This is an
epimorphism because `q_0` is onto.

Let `iota:C_0->C_1` be the tautological isomorphism and put

```text
g=(1,1,z) in C_0.
```

Define

```text
alpha(c)=iota(c)                  for c in C_0,
alpha(c)=g c g^(-1)              for c in C_1.          (VFP1)
```

The subgroups `C_1` and `gC_1g^(-1)` have trivial intersection in the free
product `C_0*C_1`: they stabilize two distinct vertices of the Bass--Serre
tree and the intervening edge has trivial stabilizer.  Hence they generate
their free product.  The universal property therefore makes `alpha`
injective.  Equivalently, free-product normal forms show directly that no
cancellation occurs between the images of two consecutive source
syllables.

The endomorphism is proper.  Let `rho_0:L->C_0` be the retraction which is
the identity on `C_0` and kills `C_1`.  Both subgroups in the image of
`alpha` are killed by `rho_0`, whereas `rho_0(g)=g!=1`.  Thus
`alpha(L)<=ker(rho_0)<L`.

Since `q_0(g)=1`, `(VFP1)` gives

```text
theta(alpha(C_0))=q_1(C)=A,
theta(alpha(C_1))=q_0(g)q_1(C)q_0(g)^(-1)=A.
```

This proves `(VFS1)`.  The standard normal-form theorem for ascending HNN
extensions then embeds `L` in `(VFS2)`.

Finally fix any unitary representation `pi:C->U(V)`.  Define a
representation `rho:L->U(V)` by

```text
rho(c in C_0)=pi(c),             rho(c in C_1)=pi(c).
```

The element `g` belongs to the central `C_2` factor of `C`, so `pi(g)`
commutes with `pi(C)`.  Therefore

```text
rho(alpha(c))=rho(c)             for c in C_0 union C_1.
```

Taking `rho(t)=1` satisfies every HNN relation in `(VFS2)`.  Since `pi` was
arbitrary, every finite `C`-type survives in an exact stationary model.  In
particular the two quotient-kernel Reynolds projections are not selected by
the self-compressor relations, completing the claimed localization
firewall.

