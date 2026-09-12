---
rg: 2
id: stw77-infinite-amplification-descent-gap-proof
kind: route
title: Split both amplified blocks and test descent on the rank-one vector
target: stw77-infinite-amplification-hides-finite-model-supports
requires:
  - stw77-fd-commutant-splitting-iff-proper-supports
  - one-sided-fd-models-allow-finite-junk-corners
---

Let `xi` be a unit vector spanning `pH`.  In the amplified Hilbert space
write

```text
K=(pH) tensor l2,          L=(qH) tensor l2.
```

Both `K` and `L` are infinite dimensional.  Choose isometries
`v_(1,K),v_(2,K) in B(K)` with orthogonal ranges and likewise choose
`v_(1,L),v_(2,L) in B(L)`.  Relative to

```text
H tensor l2=K direct-sum L,
```

put

```text
S_i=v_(i,K) direct-sum v_(i,L).                         (3)
```

Each `S_i` commutes with `p tensor 1`, hence with `iota(D)`, and (3)
immediately gives

```text
S_i* S_j=delta_(i,j)1.
```

This proves the amplified splitting.

For the descent estimate, let `s_1,s_2 in B(H)` be any isometries with
orthogonal ranges and set

```text
delta=max_i norm([s_i,p]).
```

Decompose

```text
s_i xi=alpha_i xi+eta_i,          eta_i in qH.
```

Since

```text
eta_i=q s_i xi=q[s_i,p]xi,
```

we have `norm(eta_i)<=delta`.  The isometry equation gives

```text
|alpha_i|^2=1-norm(eta_i)^2>=1-delta^2.                (4)
```

The two vectors `s_1 xi` and `s_2 xi` are orthogonal, so

```text
0=conj(alpha_1)alpha_2+<eta_1,eta_2>.
```

Consequently Cauchy--Schwarz and (4) give

```text
1-delta^2
 <=|alpha_1 alpha_2|
 <=norm(eta_1)norm(eta_2)
 <=delta^2.
```

Hence `delta>=1/sqrt(2)`, proving (2).

The argument is intrinsic to operator norm.  Strong or weak approximation
of the amplified isometries cannot evade (2), and the obstruction is
already present in the type-I algebra `B(H)`.  Infinite amplification
therefore cannot be the missing descent bridge in the nuclear-dimension-zero
case: it repairs every minimal support indiscriminately, including the
finite junk block that must instead be merged with a near-duplicate proper
cluster downstairs.
