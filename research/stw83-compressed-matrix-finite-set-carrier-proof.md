---
rg: 2
id: stw83-compressed-matrix-finite-set-carrier-proof
kind: route
title: Dilate a partition-of-unity interpolation by a closed moving matrix frame
target: stw83-compressed-one-colour-carries-circle-matrix-finite-sets
requires:
  - stw83-rotating-order-zero-compression-escapes-circle-gap
---

Choose points `t_1,...,t_m` and an open cover `U_1,...,U_m` of the
circle such that

```text
norm(x(t)-x(t_j))<epsilon
for x in Omega and t in U_j.                             (3)
```

After repeating one set if necessary, we may take `m>=2`.  Let
`w_1,...,w_m` be a continuous partition of unity subordinate to this
cover.  The evaluation map

```text
phi(x)=(x(t_1),...,x(t_m))
```

is a unital star homomorphism from `M_k(C(T))` to
`F=direct-sum_j M_k`.

Let `xi_1,...,xi_m` be the standard basis of `C^m` and define

```text
r(t)=sum_j sqrt(w_j(t)) xi_j.                            (4)
```

This is a continuous unit-vector loop.  There is a continuous unitary loop
`R:T->U(m)` with

```text
R(t)* xi_1=r(t).                                         (5)
```

For completeness, lift `r` over the interval `[0,2 pi]` through the
locally trivial bundle

```text
U(m)->S^(2m-1),       V |-> V* xi_1.
```

The two endpoint lifts differ by left multiplication by an element of the
stabilizer of `xi_1`.  That stabilizer is `U(m-1)), hence path connected.
Multiplying the lift by a path in the stabilizer closes it without changing
its image in the sphere, proving (5).

Embed `F` block diagonally by

```text
rho(a_1,...,a_m)=sum_j e_(jj) tensor a_j
                 in M_m tensor M_k.
```

Define

```text
psi(a)(t)
 =(R(t) tensor 1_k) rho(a) (R(t)* tensor 1_k).           (6)
```

Pointwise unitary conjugation makes `psi` a unital star homomorphism.  Put
`p=e_(11) tensor 1_k`.  Equations (4)--(6) give, in the constant
rank-`k` corner,

```text
p psi(phi(x))(t) p
 =sum_j w_j(t) x(t_j).                                   (7)
```

Consequently (3) implies

```text
norm(p psi(phi(x))(t) p-x(t))
 <=sum_j w_j(t) norm(x(t_j)-x(t))
 <epsilon
```

for every `x in Omega` and `t in T`, proving (1).

If `a in M_k` is a constant section, then

```text
rho(phi(a))=1_m tensor a.
```

This commutes with `R(t) tensor 1_k`, so (6) gives (2) exactly.

Both legs of the factorization are star homomorphisms.  The only
non-order-zero operation is the final compression by `p`.  Its complement
contains the extra conjugated evaluation blocks from (6).  Suppressing those
blocks while keeping an order-zero outgoing map would turn (7) into a
one-colour approximation of `M_k(C(T))), contradicting its nuclear
dimension one.  Hence the leakage is not a dispensable artifact of the
proof; coordinating it with the Toeplitz buffer is precisely the remaining
global recolouring problem.
