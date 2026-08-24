---
rg: 2
id: balanced-marginal-hnn-character-packing
kind: claim
title: Balanced marginal HNN rows give exact orthogonal character packing
root: true
artifacts:
  - research/balanced-marginal-hnn-character-packing-proof.md
distinct_from:
  finite-character-idempotents-have-exact-hnn-transport: that transports one matched character idempotent exactly; this gives a simultaneous family, proves pairwise orthogonality from distinct marginal characters, and constructs the prescribed tracial extension.
  canonical-types-extend-every-finite-bass-serre-actor: that extends canonical representations through arbitrary finite Bass--Serre data; this computes one character-packing family and its exact capacity.
  simultaneous-bad-character-packing-extension: that asks for a supercritical packing coupling all forbidden context families; this proves the strongest packing obtainable from independent balanced HNN rows and identifies its sharp capacity bound.
---

Let `H` be a finite abelian group, let `A<=H`, and let
`chi:H->T` be a character.  Fix automorphisms

```text
alpha_r in Aut(A),                     1<=r<=K,          (BMH1)
```

and form the multiple HNN extension

```text
Gamma=<H,t_1,...,t_K |
       t_r a t_r^(-1)=alpha_r(a), a in A>.             (BMH2)
```

Write

```text
e_chi=|H|^(-1) sum_(h in H) overline(chi(h)) h,
p_r=t_r e_chi t_r^(-1).                                (BMH3)
```

If the characters

```text
chi|A circle alpha_r^(-1)                              (BMH4)
```

are pairwise distinct, then the projections `p_1,...,p_K` are pairwise
orthogonal in `C[Gamma]`.

Let `M` be a finite factor and let `pi:H->U(M)` be a representation.  If
the tracial character of `pi|A` is invariant under every `alpha_r`, then
`pi` extends to a representation of `Gamma` in `U(M)`.  Indeed the two
trace-preserving embeddings of `C[A]` determined by `pi|A` and
`pi circle alpha_r` are unitarily conjugate in `M`; an implementing unitary
may be chosen as the image of `t_r`.

Suppose additionally that `J in A` is an involution fixed by every
`alpha_r` and `chi(J)=-1`.  Then `J` remains central in `Gamma`, every
`p_r` lies below

```text
q_-=(1-J)/2,                                            (BMH5)
```

and the packing is capacity sharp:

```text
K<=|A|/2<=|H|/2.                                       (BMH6)
```

For the canonical trace, `tau(e_chi)=1/|H|` and
`tau(q_-)=1/2`, so `(BMH6)` implies the finite-dimensional inequality

```text
K tau(e_chi)<=tau(q_-).                                (BMH7)
```

Thus balanced HNN rows solve the local orthogonality and exact-extension
problems simultaneously, but never exceed the regular marked-sector
capacity.  A supercritical simultaneous packing must impose a relation
among different row intertwiners or use data not determined by their
individual finite-subgroup marginals.
