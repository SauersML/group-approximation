---
rg: 2
id: wandering-leavitt-corner-reflection-proof
kind: route
title: Install the black-hole base in orthogonal conjugate corners and pull back all kernels
target: wandering-leavitt-corner-reflection-compiler
requires:
  - binary-leavitt-all-ranks-full-mf-radical
---

For `q in Q`, put

```text
s_q=q s,                t_q=t q^(-1),
p_q=s_q t_q.
```

Then `t_q s_q=1`.  Pairwise orthogonality of the `p_q` implies
`t_q s_r=0` for `q!=r`: multiply `p_qp_r=0` on the left by `t_q` and on the
right by `s_r`.

For a finitely supported tuple `u=(u_q) in U^(Q)`, define

```text
beta(u)=1+sum_q s_q(u_q-1)t_q.                          (WCP1)
```

The matrix-unit relations above give

```text
beta(u)beta(v)=beta(uv),        beta(u)^(-1)=beta(u^(-1)),
t_q beta(u)s_q=u_q.
```

Thus `beta` is an injective homomorphism.  For `k in Q`,

```text
k s_q=s_(kq),                 t_q k^(-1)=t_(kq),
```

so conjugation by `k` implements the regular left shift of the base.

The base centralizes every `p_q`.  A nonidentity `k in Q` sends `p_1` to the
orthogonal nonzero idempotent `p_k`, and therefore cannot belong to the base.
It follows that the base and actor generate the internal semidirect product
in `(WC1)`.

Every homomorphism from `W(Q,p)` to an MF group kills each coordinate copy of
`U`, hence kills the whole restricted base and factors uniquely through
`pi`.  Conversely, every MF-target map from `Q` pulls back along `pi`.
Intersecting the corresponding kernels proves `(WC2)`--`(WC4)`.

The same bijection restricted to maps killing a normal subgroup `N` matches
them with the MF-target maps from `Q` killing `pi(N)`.  Intersecting kernels
again gives `(WC5)`.

The quotient `W(Q,p)/N` is MF exactly when `N` equals its semantic closure.
By `(WC5)`, that equality first forces `ker(pi)=U^(Q)<=N`; it then becomes

```text
N=pi^(-1)(cl_MF^Q(pi(N))),
```

which is equivalent to `Q/pi(N)` being MF.  This proves `(WC6)`.  It also
shows that the MF-closed normal subgroups on the two sides correspond under
inverse image and image, and these operations preserve arbitrary meets and
joins.

If `Q` is MF, `(WC2)` is the base.  If `d` normally generates `U`, it
normally generates the identity coordinate of the base; conjugation by `Q`
then reaches every coordinate.  If every quotient of `Q` is MF, its semantic
closure operator is the identity, so `(WC5)` reduces to `(WC7)`, and the
quotient criterion follows.

Finally, if `S_U` and `S_Q` are finite generating sets, the copy of `S_U` in
the identity corner together with `S_Q` generates the actor and every shifted
coordinate.  This proves finite generation.
