---
rg: 2
id: projectively-closed-symmetry-bases-are-hyperfinite
kind: claim
title: A projectively multiplicatively closed orthonormal symmetry basis forces hyperfiniteness
requires:
  - every-separable-diffuse-finite-algebra-has-an-orthonormal-symmetry-basis
distinct_from:
  finite-normal-type-corner-is-twisted-group-algebra: that computes a selected finite-normal representation corner; this starts with an arbitrary factor basis and shows that the strongest possible group-like multiplication law would make the whole factor amenable.
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that permits arbitrary nonamenable index groups and asks whether one twisted factor is non-CE; this proves that the self-adjoint basis supplied by the Kadison theorem can only yield an elementary-abelian projective index group.
artifacts:
  - research/artifacts/kadison-symmetry-basis-groupification-audit-2026-08-21.md
---

Let `(M,tau)` be a finite von Neumann algebra and let
`B={s_i:i in I}` be a complete orthonormal basis of `L^2(M,tau)` consisting
of symmetries.  Suppose it is closed under multiplication up to phase:

```text
for every i,j there are k and lambda in T with
s_i s_j=lambda s_k.                                   (KSB1)
```

Then the projective classes `G={T s_i:i in I}` form a group.  Indeed they
are closed by `(KSB1)`, every class is its own inverse because `s_i^2=1`,
and cancellation holds inside `U(M)/T`.  A group in which every element has
order at most two is abelian, so `G` is an elementary abelian `2`-group.

Choosing basis representatives gives a scalar cocycle `omega` and a
trace-preserving isomorphism

```text
M ~= L_omega(G).                                      (KSB2)
```

The trace statement follows from orthonormality: the identity class is the
unique scalar basis line and every other basis element has trace zero.
Completeness makes the twisted group span `L^2`-dense in `M`.

Since `G` is abelian, hence amenable, its twisted group von Neumann algebra
is injective; with separable predual it is hyperfinite and Connes
embeddable.  Therefore no non-CE factor can have a projectively closed
orthonormal symmetry basis.

Thus the 2026 solution of Kadison's basis problem does not solve the group-
factor embedding hole.  Any attempted compiler must encode the genuinely
spread structure constants of the basis, rather than merely name its
unitary vectors.
