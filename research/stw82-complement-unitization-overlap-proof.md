---
rg: 2
id: stw82-complement-unitization-overlap-proof
kind: route
title: Identify the common unitization and split the quotient along the two support ideals
target: stw82-complement-symmetry-and-overlap-reduction
requires:
  - stw82-split-af-is-one-multiplier-projection-problem
artifacts:
  - research/artifacts/stw82-complement-symmetry-overlap-audit-2026-08-30.md
---

## 1. Common unitization

Let `B_p=A+C p` and `B_q=A+C q`.  If either algebra is already unital, its
unit as a subalgebra containing the essential ideal `A` is necessarily
`1_(M(A))`; otherwise adjoining that multiplier unit gives its minimal
unitization.  Since `q=1-p`, in every case

```text
(B_p)~=A+C1+C p=A+C1+C q=(B_q)~.                        (CUO1)
```

The standard unitization permanence theorem says

```text
dim_nuc(B~)=dim_nuc(B)                                  (CUO2)
```

for every C-star algebra `B`.  Equations `(CUO1)--(CUO2)` prove complement
symmetry.  Applying the full-support result from
`stw82-split-af-is-one-multiplier-projection-problem` to whichever of `p,q`
is full proves `(CSO3)`.

## 2. The support ideals cover A

For every `a in A`, both `ap` and `pa` belong to `L`.  For example,

```text
(ap)(ap)^*=apa^* in L,
```

and ideals are hereditary; the other inclusions follow by adjoints.  The
same argument applies to `q` and `R`.  Thus

```text
a=ap+aq in L+R,
```

which proves `L+R=A`.

The Chinese-remainder map therefore gives

```text
A/I -> (A/L) direct_sum (A/R),
a+I |-> (a+L,a+R)                                      (CUO3)
```

as an isomorphism.  On the first coordinate the induced multiplier `p` is
zero because `pA+Ap subset L`; on the second, `q` is zero and hence `p` is
the multiplier unit.  Since `p notin A`, quotienting `K=A+C p` by `I`
therefore yields

```text
K/I isomorphic to (A/L) direct_sum ((A/R)+C1)
    =(A/L) direct_sum (A/R)~.                           (CUO4)
```

Quotient monotonicity, finite-direct-sum permanence, and unitization
invariance give

```text
dim_nuc(K/I)
 =max(dim_nuc(A/L),dim_nuc(A/R))
 <=dim_nuc(A).                                          (CUO5)
```

## 3. Both projections are full on the overlap

First, `p` is full as a multiplier of `L`.  Indeed every dense generator
`apb` of `L` already has the form

```text
apb=(ap) p (pb),       with ap,pb in L,
```

so `L=closure(LpL)`.  The overlap `I` is an ideal of `L`.  If `(e_lambda)`
is an approximate unit for `I`, approximate `x in I` by finite sums
`sum_j l_j p m_j` in `L`, and then compress on both sides by `e_lambda`.
The resulting terms

```text
(e_lambda l_j) p (m_j e_lambda)
```

belong to `IpI` and converge to `x`.  Hence

```text
I=closure(IpI).                                         (CUO6)
```

Every multiplier of `A` preserves its ideals, so `p` restricts to `M(I)`.
Thus `(CUO6)` says that restriction is full.  Interchanging `p` and `q`
proves `I=closure(IqI)` as well.

If `I=0`, `(CUO4)` describes `K` itself and `(CUO5)`, together with ideal
monotonicity `dim_nuc(A)<=dim_nuc(K)`, proves equality.  Otherwise all
unresolved gluing is confined to the extension by this common full-support
overlap.

## 4. The nonquasidiagonal Toeplitz case

For `A=T tensor K` and `p=(1-SS*) tensor 1`, the existing finite-spectrum
repair no-go proves that `L=K tensor K` is proper essential and that the
residual extension has nonzero index.  On the other hand, with
`q=SS* tensor 1`,

```text
(S* tensor k_1) q (S tensor k_2)=1_T tensor k_1k_2.
```

Such products generate the full ideal `T tensor K`, so `q` is full in
`M(A)`.  The complement-full clause therefore establishes the dimension
formula without constructing any quasidiagonal cut.
