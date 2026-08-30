---
rg: 2
id: stw82-overlap-quasidiagonal-extension-proof
kind: route
title: Apply quasidiagonal extension permanence after computing the overlap quotient
target: stw82-projectional-overlap-cuts-preserve-dimension
requires:
  - stw82-complement-symmetry-and-overlap-reduction
  - stw82-raw-two-cut-reuse-iff-quasidiagonal
artifacts:
  - research/artifacts/stw82-projectional-overlap-cuts-audit-2026-08-30.md
---

If `p in A`, then `K=A`.  If `q=1-p in A`, then `K=A+C1` is the minimal
unitization of `A`.  The conclusion follows immediately in either case.
Assume henceforth that neither complementary projection belongs to `A`.

Every multiplier of `A` preserves its ideals, so `I` is an ideal of
`K=A+C p`.  Hypothesis `(POC1)` says that `(e_n)` is an approximate unit of
projections for this ideal.  It is quasicentral on `A` by the first limit
and on the added generator `p` by the second.  Since `K` is the closed
linear span of `A` and `p`, it is quasicentral in all of `K`.

Thus `(POC3)` is a quasidiagonal extension.  The maximum theorem for
separable quasidiagonal extensions gives

```text
dim_nuc(K)=max(dim_nuc(I),dim_nuc(K/I)).                 (OQE1)
```

The overlap quotient was computed in
`stw82-complement-symmetry-and-overlap-reduction`:

```text
K/I isomorphic to (A/L) direct_sum (A/R)~.               (OQE2)
```

Ideal and quotient monotonicity, finite-direct-sum permanence, and
unitization invariance imply

```text
dim_nuc(I)<=dim_nuc(A),
dim_nuc(K/I)
 =max(dim_nuc(A/L),dim_nuc(A/R))
 <=dim_nuc(A).                                           (OQE3)
```

Combining `(OQE1)--(OQE3)` gives `dim_nuc(K)<=dim_nuc(A)`.  Conversely `A`
is an ideal in `K`, so ideal monotonicity gives the reverse inequality.
This proves `(POC2)`.

Notice that fullness of `p,q` on the linking core `I` is compatible with,
but not needed to manufacture, the cuts.  Its role is structural: the cuts
control exactly the common off-diagonal transition ideal identified by the
linking-core theorem, while `(OQE2)` removes both residual diagonals at once.

## A strict two-sided example

Let `H=ell^2(N)` and choose a sequence `(t_j)` in `(0,1]` which is dense and
meets every nonempty open subset infinitely often.  Define

```text
rho(f)=diag(f(t_1),f(t_2),...)       for f in C_0((0,1]).
```

This representation is faithful, and `rho(f)` is compact only for `f=0`:
if `f` is nonzero, infinitely many diagonal entries have modulus bounded
away from zero.  Put

```text
P=K(H)+rho(C_0((0,1])) subset B(H).
```

Then

```text
0 -> K(H) -> P -> C_0((0,1]) -> 0                       (OQE4)
```

is a split quasidiagonal extension.  If `Q_n` is the initial-coordinate
rank-`n` projection, then `Q_n` commutes with `rho(C_0((0,1]))` and is a
quasicentral approximate unit for `K(H)` in `P`.

Inside `M_2(B(H))`, set

```text
A=[P K;K P],       I=M_2(K),
p=diag(1,0),       q=diag(0,1).
```

The displayed matrices define a C-star algebra, `p,q in M(A)`, and neither
projection belongs to `A` because `P` is nonunital.  Direct multiplication
gives

```text
L=closure(ApA)=[P K;K K],
R=closure(AqA)=[K K;K P],
L intersect R=I.                                        (OQE5)
```

Both supports are proper.  The ideal `I` is essential in `A`, since the
compacts are essential in `P`; hence `L` and `R`, which contain `I`, are
proper essential ideals and cannot be complemented.  Thus both `p,q` are
nonfull.

The projections

```text
e_n=diag(Q_n,Q_n)
```

form an approximate unit for `I`, commute exactly with `p`, and are
quasicentral in `A`.  Therefore the new theorem applies.

It does not reduce to the one-sided support theorem.  Indeed

```text
L/I isomorphic to C_0((0,1]),       R/I isomorphic to C_0((0,1]).
```

The connected noncompact space `(0,1]` has no nonzero compact-open subset,
so its C-star algebra has no nonzero projection.  An approximate unit of
projections in `L` would descend to one in `L/I`, which is impossible; the
same holds for `R`.

Finally `(e_n)` makes both

```text
0 -> I -> A -> C_0((0,1]) direct_sum C_0((0,1]) -> 0,
0 -> I -> A+C p
  -> C_0((0,1]) direct_sum C_0((0,1])~ -> 0
```

quasidiagonal.  Their ideals have dimension zero and their quotients have
dimension one, so the quasidiagonal maximum theorem gives dimension one for
both middle algebras.
