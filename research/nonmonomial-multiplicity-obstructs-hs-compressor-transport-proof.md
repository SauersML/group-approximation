---
rg: 2
id: nonmonomial-multiplicity-obstructs-hs-compressor-transport-proof
kind: route
title: Use the irreducible icosahedral multiplicity space to forbid a transported rank-one partition
target: nonmonomial-multiplicity-obstructs-hs-compressor-transport
requires: []
---

Take

```text
Gamma = SL_3(Z),
J = A_5,
G = Gamma x J.
```

`Gamma` is infinite, finitely generated, and has property `(T)`; `J` is
finite, hence has property `(T)`, so `G` is again finitely generated and has
property `(T)`.  Let `a_1,...,a_m` generate `A_5` and put
`t_i=(1,a_i)`.  Then

```text
G=<Gamma,t_1,...,t_m>,
t_i Gamma t_i^(-1)=Gamma.
```

Let `sigma:A_5 -> U(3)` be the standard irreducible three-dimensional
icosahedral representation and define

```text
pi(g,a)=sigma(a).
```

This is a genuine representation of `G`, and `pi|_Gamma=1`.

First consider an exact fine block `q`.  For every `Gamma` generator `s`,

```text
q pi(s) q = q.
```

Hence the left side of the scalar adjoint Poincare inequality on `q M_3 q`
is zero for every self-adjoint `x`.  If the gap constant is positive, the
right side can vanish for every such `x` only when

```text
q M_3 q = C q,
```

i.e. `rank(q)=1`.  Thus any exact full fine decomposition with positive
`Gamma`-gap consists of exactly three rank-one projections.

If every compressor transports each fine block to a fine block, the three
lines are permuted by every `sigma(a_i)`, hence by all of `A_5`.  This gives a
homomorphism

```text
A_5 -> Sym(3).
```

Because `A_5` is simple, such a homomorphism is either injective or trivial.
It cannot be injective since `|A_5|=60>|Sym(3)|=6`; if it is trivial, each of
the three lines is invariant under `sigma(A_5)`, contradicting irreducibility.
So the exact transport partition does not exist.

It remains to exclude the possibility that the asymptotic formulation evades
this by changing the partition with `delta`.  Let `delta_n -> 0` and suppose
partitions satisfying an error `eps_n=eps(delta_n)->0` existed for the same
exact `pi`.  With normalized trace on `M_3`, every nonzero projection has
trace at least `1/3`.  For all large `n`, `eps_n<1/3`, so the allowed discarded
projection is zero and `p_n=1`.  The positive `Gamma`-gap argument above again
forces exactly three rank-one fine blocks

```text
p_(n,1)+p_(n,2)+p_(n,3)=1.
```

The compact space of orthogonal rank-one triples in `M_3` has a convergent
subsequence; relabel along that subsequence and write

```text
p_(n,j) -> p_j.
```

For each finitely many pairs `(i,j)`, the compressor clause chooses one of
three target indices.  Pass to a further subsequence on which all these
choices are constant, say `f_i(j)`.  Taking limits in

```text
||sigma(a_i) p_(n,j) sigma(a_i)^* - p_(n,f_i(j))||_2 <= eps_n
```

gives

```text
sigma(a_i) p_j sigma(a_i)^* = p_(f_i(j)).
```

The three left-hand projections are pairwise orthogonal, so each `f_i` is
injective and hence a permutation.  We have therefore recovered the forbidden
exact `A_5`-action on three lines, a contradiction.

The obstruction is solely the fine compressor transport.  If desired, the
ambient coarse decomposition in this example can be the single block `1`:
`pi(G)=sigma(A_5)` is irreducible, so its adjoint action has only scalar fixed
vectors and therefore has a positive finite-dimensional spectral gap.
