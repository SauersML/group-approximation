# Determinant and Fredholm data do not constrain the marked HNN trace

## Setup

For

```text
C=SL_3(Z) < A=SL_3(Z[1/2]),
G=<A,t | [t,C]=1>,
h=diag(2,1,1/2),
```

the first mixed marked word is

```text
w=[t,h].
```

In a matrix assignment write `T` and `H` for the images of `t` and `h`.
This note records an exact finite-coordinate fence: determinant and additive
Fredholm/index data cannot force `|tr([T,H])|` away from zero.  The argument
does not assert that the displayed raw matrix pairs satisfy the global
presentation of `A`; it proves that any successful obstruction must use
those global relations or their joint Hecke-multiplicity consequences.

## Determinant is tautological

For every pair of finite-dimensional unitaries,

```text
det([T,H])=det(T H T^* H^*)=1.                         (JDI1)
```

This contains no trace information.  In fact trace zero is compatible with
`(JDI1)` in every dimension `d>=2`, and can be realized by a commutator.

Let `zeta=exp(2 pi i/d)` and choose a scalar `alpha` with

```text
alpha^d=(-1)^(d-1).
```

Put

```text
r_j=alpha zeta^j,       0<=j<d,
W_d=diag(r_0,...,r_(d-1)).
```

Then

```text
tr_d(W_d)=0,            det(W_d)=1.                    (JDI2)
```

Indeed the `d`th roots sum to zero and their product is `(-1)^(d-1)`.
Let `S` be the cyclic shift.  Since `product_j r_j=1`, choose diagonal
entries `q_j` cyclically so that `q_j/q_(j-1)=r_j`, and put
`Q=diag(q_j)`.  A direct calculation gives, up to the harmless choice of
commutator convention,

```text
[Q,S]=W_d.                                              (JDI3)
```

Thus the maximal canonical separation `tr_d(w)=0` is realized inside the
determinant-one commutator locus itself.  Tensoring with spectators preserves
zero trace and determinant one, so no divisibility refinement repairs the
problem.

## Additive index is equally tautological

For any square complex matrix `X`,

```text
dim ker(X)-dim ker(X^*)=0,                              (JDI4)
```

because `rank(X)=rank(X^*)`.  For a projection `P` and a unitary `H`, the
conjugate projection `Q=HPH^*` has the same rank, and the finite-dimensional
relative index is

```text
ind(P,Q)=dim(P cap Q^perp)-dim(P^perp cap Q)
        =Tr(P)-Tr(Q)=0.                                 (JDI5)
```

Consequently an additive Fredholm index attached to the two conjugate
carriers is identically zero.  A rectangular compression can have nonzero
index only after selecting unequal-rank source and target spaces; a bounded
rank imbalance has zero normalized density under spectator amplification.
This is not an amplification-stable lower bound for the normalized trace of
`w`.

## What remains

Exact finite-dimensional representations of the full arithmetic double
already fold, by `sl3-arithmetic-double-finite-representations-fold`.  Hence
the obstruction cannot be found by refining the exact determinant or index
of the marked word.  A surviving finite-coordinate argument must instead
extract extensive information from the **joint** approximate extension:
the two arithmetic vertices, their common `C` restriction, and the Hecke
transport of multiplicity spaces by `h`.

A concrete sufficient residue is a majority common-phase sector.  For a
canonical double microstate with fold word `W_n`, find a projection `p_n`
assembled from coherent joint Hecke-multiplicity packets, a phase `z_n`, and
one `kappa>0` such that

```text
tr(p_n)>=1/2+kappa,
||(W_n-z_n I)p_n||_2 -> 0.                              (JDI6)
```

Then

```text
|tr(W_n)| >= tr(p_n)-tr(1-p_n)-o(1)
           >= 2 kappa-o(1),                            (JDI7)
```

contradicting the canonical trace `tr(W_n)->0`.  The word "coherent" is
load-bearing: separate source multiplicities or scalar Hecke coefficients
do not select one common phase, as
`source-hecke-data-leave-projective-square-free` proves.

This majority-sector statement is strictly less than correction of either
whole `A` vertex and strictly less than forcing `|tr(W_n)|->1`.  It is the
smallest explicit finite-coordinate multiplicity target exposed by the
determinant/index audit.
