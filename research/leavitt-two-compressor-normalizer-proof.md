---
rg: 2
id: leavitt-two-compressor-normalizer-proof
kind: route
title: Conjugate diagonal block matrices through the two Leavitt inverse pairs
target: leavitt-two-compressor-diagonal-kernel-is-locally-finite
requires: []
---

Write `a=s_0`, `b=s_1`, `A=t_0`, `B=t_1`.  On the first two rank-five
blocks the first compressor and its inverse use

```text
U_0=[[a,bA],[0,B]],              V_0=[[A,0],[aB,b]],
```

and the other two blocks use the inverse pair in the opposite order.  The
second compressor is obtained by exchanging `a<->b`, `A<->B`.

For every `d in D`, prefix cancellation gives

```text
t_i d s_j=0              when i!=j,
t_i d s_i in D,          s_i d t_i in D.              (N1)
```

Apply `(N1)` entrywise to arbitrary `g_0,g_1 in M_5(D)`.  Every off-diagonal
block in each of

```text
U_0 diag(g_0,g_1) V_0,          V_0 diag(g_0,g_1) U_0
```

vanishes, while each diagonal block is a sum of terms of the forms in
`(N1)` and hence belongs to `M_5(D)`.  Thus both `U_0` and `V_0` normalize
`GL_5(D)^2`.  Branch exchange proves the same assertion for the second
compressor, and the four-block matrices normalize `K=GL_5(D)^4`.

Now `D=union_k D_k` with every `D_k` finite, so

```text
K=union_k GL_5(D_k)^4
```

is locally finite.  Since `Lambda<=K` and both compressor generators
normalize `K`, every conjugate of `Lambda` in `B_EL` lies in `K`; so does its
normal closure.  The intersection `B_EL intersect K` is normal for the same
reason and is locally finite.  Finally the explicit elementary matrices give
the two scalar blocks

```text
R_+=[[bA,a],[B,0]],              R_-=[[0,A],[b,aB]]
```

for `tau_1 tau_0^(-1)`.  Direct multiplication with
`Aa=Bb=1`, `Ab=Ba=0`, and `aA+bB=1` gives
`R_+^3=R_-^3=I`.  Hence `(tau_1 tau_0^(-1))^3=1`, so the corresponding
relative coset has order dividing three.
