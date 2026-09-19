---
rg: 2
id: coset-difference-cocycle-embeds-double-proof
kind: route
title: Embed the fold kernel as the free difference-lamp subgroup
target: sofic-coset-action-makes-amalgam-double-sofic
requires:
  - gkp-free-generalized-wreath-soficity
  - kt-q2-double-hyperlinear-iff-relative-embeddable
---

Let `X=H/Gamma`, `o=Gamma`, and

```text
F_X=*_(x in X)<z_x>,       W=F_X rtimes H,
h z_x h^(-1)=z_(h x).
```

## The difference cocycle

Define

```text
b(h)=z_o^(-1) z_(h o).
```

It is a nonabelian one-cocycle for the permutation action:

```text
b(g) (g b(h) g^(-1))
 = z_o^(-1) z_(g o) z_(g o)^(-1) z_(g h o)
 = b(g h).                                                     (CDC1)
```

Therefore

```text
i_0(h)=h,              i_1(h)=b(h)h
```

are homomorphisms `H->W`.  If `gamma in Gamma`, then
`gamma o=o`, so `b(gamma)=1` and `i_0(gamma)=i_1(gamma)`.  The universal
property gives a homomorphism

```text
Phi:H *_Gamma H -> W.                                         (CDC2)
```

## Injectivity

Let `pi:H *_Gamma H->H` be the fold map, and let `K=ker(pi)`.  The kernel
acts freely on the Bass--Serre tree: its intersection with any conjugate of a
vertex group is trivial because `pi` is injective on each vertex group.
The quotient graph `K backslash T` has two vertices and edge set

```text
K backslash (H *_Gamma H) / Gamma ~= H/Gamma=X.
```

Choose the edge `o` as a spanning tree.  For every `x!=o`, choose
`h_x in H` with `h_x o=x`, and let

```text
k_x=i_1^(D)(h_x) i_0^(D)(h_x)^(-1) in K,                      (CDC3)
```

where `i_0^(D),i_1^(D)` denote the two vertex embeddings in the double.
Changing `h_x` by right multiplication with an element of `Gamma` does
not change `k_x`, since the two vertex maps agree on `Gamma`.
The spanning-tree computation gives

```text
K=F({k_x:x in X, x!=o}).                                      (CDC4)
```

Under `Phi`,

```text
Phi(k_x)=z_o^(-1)z_x.                                         (CDC5)
```

The Nielsen-transformed family

```text
{z_o} union {z_o^(-1)z_x:x!=o}
```

is a free basis of `F_X`: the inverse change is
`z_x=z_o(z_o^(-1)z_x)`.  Hence (CDC5) maps the free basis (CDC4) to a free
family and `Phi|_K` is injective.  If `Phi(w)=1`, projection
`W->H` gives `pi(w)=1`, so `w in K`, and injectivity on `K` gives
`w=1`.  This proves (CDC2) is injective.

## Approximation and relative embedding

If `H` and its action on `X` are sofic, then
`gkp-free-generalized-wreath-soficity` makes `W` sofic.  Soficity passes
to subgroups, so (CDC2) makes `H *_Gamma H` sofic.  Thus its group factor,
which is the canonical tracial amalgam

```text
L(H) *_(L(Gamma)) L(H),
```

is Connes embeddable.

Finally suppose `a^k notin Gamma` for every `k!=0`.  For
`u=lambda(a) in L(H)`,

```text
E_(L(Gamma))(u^k)=0       for every k!=0.
```

Gao--Junge--Gao, arXiv:2012.07940v3, Appendix Theorem 7.1, identifies Connes
embeddability of the symmetric amalgam with `RE/C` for the vertex inclusion
under exactly this Haar-relative-unitary hypothesis.  This proves the final
assertion.
