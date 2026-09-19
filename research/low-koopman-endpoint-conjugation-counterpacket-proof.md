---
rg: 2
id: low-koopman-endpoint-conjugation-counterpacket-proof
kind: route
title: Conjugate one exact vertex by a first fourth-power mode and compute its projected Weyl derivative
target: endpoint-conjugation-refutes-iwahori-energy
requires: []
---

Fix an odd `L>=3` and put `N=4^L-1`. In
`SL_2(Z/NZ)/{+-1}` use

```text
x=[[0,-1],[1,0]],
r=[[2,0],[0,2^(-1)]],
t=[[1,1],[0,1]].                                      (LKP1)
```

Let `G_N` be the finite group they generate and let `(X,R,T)` be its left
regular representation. Direct multiplication gives

```text
X^2=(XR)^2=(XT)^3=(XT^2R)^3=1,
RTR^(-1)=T^4                                           (LKP2)
```

in the projective quotient. The order of `T` is `N`, and the
multiplicative order of `4 mod N` is exactly `L`.

Put `psi=Ad(R^(-1))`, `zeta=exp(2 pi i/L)`, and

```text
a_0=L^(-1/2) sum_(j=0)^(L-1) zeta^j T^(4^j),
a=2^(-1/2)(a_0+a_0^*).                                (LKP3)
```

Because `L` is odd, the two exponent orbits `{4^j}` and `{-4^j}` are
disjoint. In normalized Hilbert--Schmidt norm,

```text
a=a^*,       ||a||_2=1,       tau(a)=0,
||a-psi(a)||_2=|1-zeta|=g_L.                           (LKP4)
```

Take `z_epsilon=exp(i epsilon a)` and
`X_epsilon=z_epsilon X z_epsilon^(-1)`. Since `z_epsilon` commutes with
`T`, `(LKC2)` follows by conjugating the two exact words in `(LKP2)`.
Put `R_epsilon=z_epsilon^(-1)Rz_epsilon`. Conjugating the other word
values by `z_epsilon` and telescoping gives

```text
||(X_epsilon R)^2-1||_2
 =||(X R_epsilon)^2-(XR)^2||_2
 <=2||R_epsilon-R||_2,

||(X_epsilon T^2R)^3-1||_2
 =||(XT^2R_epsilon)^3-(XT^2R)^3||_2
 <=3||R_epsilon-R||_2.                                (LKP5)
```

Moreover

```text
||R_epsilon-R||_2
 =||z_epsilon-psi(z_epsilon)||_2
 <=epsilon||a-psi(a)||_2=epsilon g_L,                 (LKP6)
```

where the last inequality is the Hilbert--Schmidt Lipschitz bound for the
unitary exponential. This proves `(LKC3)` and the row-energy upper bound.

It remains to lower-bound the projected Weyl energy. Let
`Z={T}'` and let

```text
E_Z(y)=N^(-1)sum_(j=0)^(N-1) T^j y T^(-j)             (LKP7)
```

be the trace-preserving conditional expectation. Write
`theta=Ad(X)`. For every nonzero unit `n mod N`, the group elements

```text
t^j (x t^n x^(-1)) t^(-j),       j in Z/NZ,           (LKP8)
```

are pairwise distinct, and the families for distinct `n` are disjoint.
Indeed their matrix representatives are

```text
[[1-jn, j^2 n],[-n,1+jn]].                             (LKP9)
```

The lower-left entry recovers `n`, and then the upper-left entry recovers
`j` because `n` is a unit. Equality up to a minus sign is impossible:
all matrices in `(LKP9)` have trace `2`, whereas their negatives have trace
`-2`, and `N` is odd. None is a nontrivial upper unipotent because its
lower-left entry is a unit.

Group-element orthogonality in the left regular representation and
`(LKP7)--(LKP9)` therefore give the exact identities

```text
||E_Z(theta(a))||_2=N^(-1/2),
<a,E_Z(theta(a))>_2=0.                                (LKP10)
```

Let `P_reg` remove the `psi`-fixed algebra and put

```text
h=P_reg E_Z(a-theta(a)).                              (LKP11)
```

The vector `a` lies in the `zeta,zeta^(-1)` Koopman eigenspaces, so
`(LKP10)` implies that its component in the corresponding dyadic band is
perturbed by at most `N^(-1/2)`.

Since `X_epsilon^2=1`, its Weyl residual is

```text
W_epsilon=X_epsilon R X_epsilon^(-1)R=(X_epsilon R)^2.
```

Differentiating at zero and using that `R` normalizes `<T>` gives

```text
(d/d epsilon)|_0 P_reg E_Z(W_epsilon-1)
 =i(1-psi)h.                                          (LKP12)
```

Choose the dyadic `t_L` with `g_L<=t_L<2g_L`. Equations
`(LKP10)--(LKP12)` show

```text
t_L^(-1)||P_(t_L)(1-psi)h||_2
 >=1/2-N^(-1/2).                                      (LKP13)
```

For large `L` the right side is at least `1/4`. Finite-dimensional
differentiability now yields, for all sufficiently small positive
`epsilon` (depending on `L`),

```text
sum_t t^(-2)||P_t P_reg E_Z(W_epsilon-1)||_2^2
 >=epsilon^2/32.                                      (LKP14)
```

Together with `(LKP5)--(LKP6)` and `g_L<=2 pi/L`, this contradicts every
dimension-free aggregate constant.

Finally, the exact left regular quotient characters converge to the
regular character along `N=4^L-1 -> infinity`: after clearing its fixed
power-of-two denominator, a fixed nonidentity matrix cannot become
`+-I mod N` for all large `N`. Also
`||X_epsilon-X||_2<=2epsilon`. Choosing odd `L -> infinity` and then
`epsilon_L ->0` proves the regular-character assertion.
