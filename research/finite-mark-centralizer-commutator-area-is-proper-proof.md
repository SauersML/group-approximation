---
rg: 2
id: finite-mark-centralizer-commutator-area-is-proper-proof
kind: route
title: Measure centralizer loops in the nontrivial local system over the marked-subgroup Schreier graph
target: finite-mark-centralizer-commutator-area-is-proper
requires: []
---

Choose a prime divisor `p|m`.  Compose `K=<b> -> C_p` with the character
sending the image of `b` to `zeta=exp(2 pi i/p)`, and take the direct sum over
all Galois embeddings `sigma_k(zeta)=zeta^k`, `1<=k<=p-1`.  Use the resulting
rank-`p-1` local system on the right Schreier graph `K\G`.  Equivalently, use
the monomial induced module

```text
direct-sum_(k=1)^(p-1) Ind_K^G(sigma_k chi)
```

and its oriented-edge module.  Give every oriented edge fiber the norm

```text
||(z_1,...,z_(p-1))||_Gal=sum_k |z_k|
```

and sum this norm over unoriented edges.  A word in `X` determines a twisted
edge chain as follows.  Choose one representative `t_v in G` for each right
coset vertex `v in K\G`, with `t_K=1`.  For a positively oriented edge
`e=(v,x)` define `kappa(e) in K` by

```text
t_v x = kappa(e) t_(vx),
```

and set

```text
H(e)=diag(sigma_1 chi(kappa(e)),...,sigma_(p-1) chi(kappa(e))).
```

For the reverse edge impose `[bar(e)]=-H(e)^(-1)[e]`.  If a word path has
successive oriented edges `e_1,...,e_n`, define

```text
C(e_1...e_n)=sum_(j=1)^n H(e_1)...H(e_(j-1))[e_j].       (C1)
```

Changing the transversal merely applies an isometry in each vertex/edge
fiber.  Formula `(C1)` also makes the concatenation identity

```text
C(PQ)=C(P)+Hol(P)C(Q)                                   (C2)
```

literal.  Every monomial transport is an isometry of `||.||_Gal`.

Let `P_eta` be the twisted chain of the `eta` path from `K` to `Kh`.  Its
edge coefficients lie in the diagonal image of `Z[zeta]`.  Reduce those
coefficients modulo the prime ideal `(1-zeta)`.  All powers of `zeta` become
`1`, so the reduction of `P_eta` is exactly the ordinary cellular path chain
over `F_p`.  Its boundary is `[Kh]-[K]`.  Therefore the support of that
reduced chain has a connected component containing both endpoints and hence
contains at least

```text
d=d_(K\G)(K,Kh)
```

distinct edges.  On every such edge the original coefficient is a nonzero
algebraic integer `a in Z[zeta]`.  Since its algebraic norm is a nonzero
integer,

```text
sum_(k=1)^(p-1) |sigma_k(a)| >= 1.                       (P1)
```

Since `h` centralizes `b`, the word `beta` is a loop both at `K` and at
`Kh`, with diagonal holonomy
`Z=diag(zeta,zeta^2,...,zeta^(p-1))` in suitable endpoint frames.  Traverse

```text
[beta,eta]=beta^(-1) eta^(-1) beta eta.
```

After the first `beta^(-1)` loop, one copy of the reversed `eta` path is
multiplied by `Z^(-1)`; after the remote `beta` loop, the other copy has
coefficient `1`.  Apart from the two `beta` loops, the chain is therefore

```text
(Z^(-1)-I) P_(eta^(-1)).
```

Apply the preceding reduction argument to `eta^(-1)`.  Because `h`
centralizes the finite group `K` and the word metric is symmetric,

```text
d_(K\G)(K,Kh^(-1))=d_(K\G)(K,Kh)=d.
```

Put `a_p=min_(1<=k<p)|zeta^k-1|=2 sin(pi/p)`.  By `(P1)`, every one of the
`d` support edges found above contributes at least `a_p` after multiplication
by `Z^(-1)-I`.  Each `beta` loop has norm at most `(p-1)|beta|`.  The triangle
inequality gives

```text
||chain_chi([beta,eta])||_1
  >= a_p d-2(p-1)|beta|.                                (FMC2)
```

Now let a van Kampen diagram for `[beta,eta]` have `L` cells.  Lift its
one-skeleton to the twisted Schreier local system.  Its boundary chain is the
sum of the translated twisted boundary chains of its cells; internal edges
cancel with opposite orientations and identical transported coefficients.
The boundary chain of a defining relator has norm at most `(p-1)` times its
word length, and translation does not change that norm.  Hence

```text
a_p d_(K\G)(K,Kh)-2(p-1)|beta| <= L(p-1)ell,
```

which proves `(FMC1)`.

Finally, `K` is finite and the Schreier graph is locally finite.  Every
bounded ball contains only finitely many right cosets, so an infinite set of
distinct cosets in `C_G(b)/K` has unbounded distance.  This proves properness
uniformly over word representatives.

For the averaged statement, left multiplication by any `h_i in C_G(b)` is a
well-defined automorphism of `K\G`.  Hence

```text
d(Kh_i,Kh_j)=d(K,K h_i^(-1)h_j).
```

The centralizer acts by the displayed left automorphisms, so every radius-`R`
ball centered at a packet vertex `Kh_i` has the same finite cardinality
`B_R=|Ball_R(K)|`.  For each `i`, at most `B_R` choices of `j` lie within
distance `R`; at most `M B_R` ordered pairs are therefore close.  If
`M>=2B_R+1`, at least half of the ordered pairs have distance greater than
`R`.  Averaging `(FMC1)` gives `(FMC3)`.  Since `R` was arbitrary and `B_R`
is finite, the average areas diverge with `M`.
