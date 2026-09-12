---
rg: 2
id: isr-holonomy-kernel-proof
kind: route
title: Pull the recovered base back through the regular group-factor realization
target: isr-actors-force-holonomy-into-an-abelian-kernel
requires:
  - normalizer-kernel-generation-forces-haar-action
---

The cocycle identity gives `v_gv_h=v_(gh)`. The regular trace condition in
`(ISR2)` implies

```text
< v_g,v_h >_2
 =(tr_n tensor tau_R)(v_(h^(-1)g))
 =1_(g=h).                                              (ISRP1)
```

Consequently the algebraic map

```text
C[Gamma] -> M_n(L(R)),
sum_g a_g lambda_g |-> sum_g a_g v_g
```

preserves the canonical trace and the `L^2` norm. It extends to an
injective normal trace-preserving star homomorphism

```text
Phi:L(Gamma)->M_n(L(R))                                 (ISRP2)
```

whose range is `N_b`.

Put `A=L^infinity(X) tensor 1_n` and `B=Phi^(-1)(A)`. Each `v_g`
normalizes `A`: matrix-valued base functions commute with scalar matrices,
so

```text
v_g(f tensor 1_n)v_g^*
 =(f after g^(-1)) tensor 1_n.                          (ISRP3)
```

Hence every `lambda_g` normalizes `B`. By `(ISR1)`, there is a normal
subgroup `Sigma normal Gamma` with `B=L(Sigma)`. Since `Phi(B)=A` and
the probability space is diffuse, `L(Sigma)` is diffuse and abelian.
Therefore `Sigma` is infinite and abelian.

For `s in Sigma`, `(ISRP2)` gives `v_s in A`. It therefore commutes
with every element of `A`. Comparing this with `(ISRP3)` yields

```text
f after s^(-1)=f  for every f in L^infinity(X).          (ISRP4)
```

Thus `s` acts trivially almost everywhere. Hence
`Sigma<=ker(Gamma curvearrowright X)`. Finally,

```text
W*(v_s:s in Sigma)=Phi(L(Sigma))=Phi(B)=A,              (ISRP5)
```

which proves `(ISR3)`.

Chifan--Das--Sun, *Invariant subalgebras of von Neumann algebras arising from
negatively curved groups*, Theorem A (`arXiv:2207.13775`), prove `(ISR1)`
for every ICC acylindrically hyperbolic group. They also show that such a
group has no nontrivial normal amenable subgroup. Since `Sigma` is infinite
abelian, `(ISR3)` is impossible in that class.

When `n=1` and `N_b=L(R)`, `A` is the source Cartan. The regular-trace
group `{v_g:g in Gamma}` normalizes `A` and generates `L(R)`. Its
intersection with `U(A)` contains `{v_s:s in Sigma}`, whose von Neumann
algebra is `A` by `(ISRP5)`. The kernel-generation hypothesis of
`normalizer-kernel-generation-forces-haar-action` therefore holds, and
that theorem reconstructs the compact-abelian Haar action. This proves the
final assertion.
