---
rg: 2
id: orthogonal-finite-fourier-reps-are-orbit-cocycles
kind: claim
title: Orthogonal finite-Fourier representations are exactly finite-range orbit cocycles
distinct_from:
  piecewise-group-transport-gives-corner-unitaries: that constructs one algebraic corner unitary from prescribed source and range projections in a group algebra; this works in a measurable crossed product and gives the complete multiplication and trace equations for an entire represented group.
  three-actor-grades-support-an-exact-hadamard-cell: that constructs a nonnormalizing matrix-mixing unitary; this classifies the complementary orthogonal normalizer branch and exhibits a three-grade piecewise transposition.
  cyclic-aperiodicity-collapses-two-actor-grade-unitaries: that proves homogeneity for unrestricted two-grade unitaries under an ergodicity hypothesis; this shows why no analogous collapse can begin at three orthogonal grades.
---

Let a countable group `G` act trace-preservingly on a probability space
`(X,mu)`, put `B=L^infinity(X)` and `M=B rtimes G`, and use
`u_g f u_g^*=alpha_g(f)`.  For every `a` in a countable group `Lambda`, let
`S_a subset G` be finite and let `(p_(a,g))_(g in S_a)` be projections in
`B` such that both

```text
sum_g p_(a,g)=1,             sum_g alpha_g(p_(a,g))=1                 (OFC1)
```

are orthogonal partitions.  Then

```text
V_a = sum_(g in S_a) u_g p_(a,g)                                    (OFC2)
```

is a unitary normalizer of `B`.  The assignment `a |-> V_a` is a unitary
representation of `Lambda` if and only if, after putting absent projections
equal to zero, the finite partition equations

```text
p_(ab,k)
 = sum_(gh=k) p_(b,h) alpha_(h^(-1))(p_(a,g))          for all a,b,k (OFC3)
```

hold.  The summands on the right are automatically orthogonal.  Moreover

```text
tau(V_a)=mu(p_(a,e)).                                                (OFC4)
```

Thus an orthogonal finite-Fourier realization of the regular character of
`Lambda` is exactly a finite-range measurable orbit cocycle satisfying
`(OFC3)` and `mu(p_(a,e))=0` for every `a!=e`.  Trace preservation then makes
the induced map `L(Lambda)->M` injective.

Support orthogonality does **not** force homogeneous actor grades.  If
`g in G` and a positive-measure set `E` satisfies `E cap gE=empty`, put
`p=1_E`, `q=alpha_g(p)`, and `r=1-p-q`.  Then

```text
V = u_g p + u_(g^(-1)) q + r                                      (OFC5)
```

is an exact self-adjoint unitary with Fourier support
`{g,g^(-1),e}`.  It is the full-group transposition exchanging `E` and
`gE`, even when `g` has infinite order.  Hence the Mihailova bounded-support
normalizer branch cannot be closed by a general support-collapse theorem.
Its precise residual problem is to construct, or exclude, a regular-trace
finite-range cocycle satisfying `(OFC3)` for the desired source algebra.
