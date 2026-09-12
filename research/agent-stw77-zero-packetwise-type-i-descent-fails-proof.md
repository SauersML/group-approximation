---
rg: 2
id: agent-stw77-zero-packetwise-type-i-descent-fails-proof
kind: route
title: Move an amplified two-point model away from a separable C-star algebra
target: agent-stw77-zero-packetwise-type-i-descent-fails
requires: []
---

Take `B=O_2` and a faithful irreducible representation
`pi:O_2->B(H)` on a separable infinite-dimensional Hilbert space.  It is
essential.  Indeed `pi(O_2) intersect K(H)` pulls back to an ideal of the
simple algebra `O_2`; it cannot be all of `O_2` because the representation is
unital on an infinite-dimensional space, so it is zero.

We first choose a projection far from `pi(O_2)`.  Fix an orthonormal basis of
`H`.  There is an uncountable family `(q_alpha)` of diagonal projections such
that both `q_alpha` and `1-q_alpha` have infinite rank and

```text
||q_alpha-q_beta||=1                  (alpha!=beta).    (1)
```

If every `q_alpha` had distance less than `1/3` from the separable algebra
`pi(O_2)`, choose `b_alpha in pi(O_2)` with
`||q_alpha-b_alpha||<1/3`.  Formula `(1)` would give

```text
||b_alpha-b_beta||>1/3,
```

an uncountable uniformly separated subset of a separable metric space.  This
is impossible.  Hence, for some infinite-rank and infinite-corank projection
`q`,

```text
dist(q,pi(O_2))>=1/3.                                  (2)
```

Let `s_1,s_2` be the canonical Cuntz generators, put

```text
p=s_1s_1^*,
D=C p + C(1-p) subset O_2,
```

and set `K=l2 tensor H`.  Both projections

```text
1 tensor pi(p),       1 tensor pi(1-p)
```

have infinite rank on `K`, as do `q` and `1-q` on `H`.  Thus there is a
unitary `U:K->H` satisfying

```text
U(1 tensor pi(p))U^*=q,
U(1 tensor pi(1-p))U^*=1-q.                            (3)
```

Define

```text
rho(d)=U(1 tensor pi(d))U^*,
E=rho(D)=Cq+C(1-q).                                    (4)
```

The two minimal projections of `E` have infinite rank and are therefore
properly infinite in `B(H)`.

Finally take the scalar map

```text
phi:C->O_2,       phi(lambda)=lambda 1.
```

It has nuclear dimension zero, and every nonzero positive range element is
properly infinite because `1_(O_2)` is properly infinite.  Its countable
amplification is intertwined with `pi compose phi` by every unitary
`K->H`, since both representations are scalar.  Hence `(4)` is exactly a
type-I absorbed finite-dimensional model of the kind produced by
`agent-stw77-zero-type-i-proper-support-models`, and

```text
(pi compose phi)(C)=C1 subset E.                       (5)
```

Thus the range-model error is identically zero.  Nevertheless `(2)` gives
the asserted operator-norm gap.  If a homomorphism `theta:E->pi(O_2)` were
within `1/3` of the inclusion on the unit ball, then
`||q-theta(q)||<1/3`, contradicting `(2)`.  The same projection shows that
the unit ball of `E` is not one-sided near-included in `pi(O_2)` below that
constant.

This argument obstructs descent of an arbitrary absorbed model, not the
existence of a specially selected good model: the original `D subset O_2`
already has properly infinite supports.  Its force is quantitative and
precise--agreement on every element of the represented range does not
control even one minimal projection of the absorbed model.
