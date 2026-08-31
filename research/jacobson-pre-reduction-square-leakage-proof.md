---
rg: 2
id: jacobson-pre-reduction-square-leakage-proof
kind: proof
title: Block the opposite root across the residual and track the four conjugate cuts
target: jacobson-pre-reduction-square-forces-sqrt-half-leakage
requires:
  - jacobson-residual-t-root-is-orthogonal-transport
  - qutrit-jacobson-residual-has-fixed-polar-gap
---

Every generator of the elementary abelian residual group `N` is a root
in position `(1,3)` or `(2,3)`. The root
`t=x_23(T)` has the same target coordinate and commutes with all of them.
Hence

```text
[t,e]=0.                                                (JPS4)
```

Set `E=e`, `T=t`, and `K=k`. Relative to

```text
H=EH directSum (1-E)H,
```

write

```text
T=[[T_0,0],[0,T_1]],          K=[[B,L^*],[L,D]],
B=EKE,                        L=(1-E)KE.                 (JPS5)
```

Both `T_0,T_1` are unitaries on their corners. Since
`U=TKTK=u` and `EUE=0`, the upper-left block of the product is zero:

```text
T_0 B T_0 B+T_0 L^*T_1L=0.                              (JPS6)
```

Let `lambda=||L||_op`. Unitarity of `K` gives

```text
B^*B+L^*L=E,
```

so the least singular value of `B` is at least
`sqrt(1-lambda^2)` when `lambda<1`. Therefore the least singular
value, and hence the operator norm, of the first term in `(JPS6)` is at
least `1-lambda^2`. The second term has operator norm at most
`lambda^2`. Equality in `(JPS6)` forces

```text
1-lambda^2<=lambda^2.
```

This proves `lambda>=1/sqrt(2)`; if `lambda=1`, the conclusion is
immediate. Thus `(JPS1)` holds in every finite-dimensional unitary
representation in which the residual cuts and alternating relation are
evaluated exactly. The same estimate persists with an additive
`o(1)` loss for rounded approximate occurrences.

For the trace audit, define the cuts in `(JPS2)`. Each is obtained from
`e` by conjugation by a group word, so it is the corresponding character
idempotent for

```text
N_j=g_j N g_j^(-1) isomorphic to C_2^5.
```

The last word is `g_4=u`, and the residual orthogonality theorem gives
`e_0e_4=0`.

Let `F_q` be the order-`3^5` qutrit support group. For every `j`,
the intersection `F_q intersect N_j` is trivial by coprime orders.
Expanding a qutrit group-algebra projection `p` and the character
idempotent `e_j`, the identity coefficient of their product can only
come from the identity in each factor. Hence

```text
tau(p e_j)=tau(p)tau(e_j)=tau(p)/32,
||e_jp||_2^2=tau(p)/32.                                 (JPS7)
```

Substituting the three qutrit traces proves `(JPS3)`. Notice that this
trace calculation does not claim that `p` commutes with `e_j`; only
their canonical Hilbert--Schmidt overlap is used.

Thus the alternating word supplies a fixed transverse operator-norm
boundary, but every one of its natural vertex cuts has the same qutrit
weight vector. A Hall contradiction requires a further block-support
identity, not merely the pre-reduction transport path.
