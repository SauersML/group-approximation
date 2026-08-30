---
rg: 2
id: stw82-finite-rank-tail-splitting-proof
kind: route
title: Split the multiplier tail off every finite coefficient matrix stage
target: stw82-stabilized-coefficient-projections
requires:
  - stw82-overlap-is-a-full-linking-core
artifacts:
  - research/artifacts/stw82-stabilized-coefficient-projection-audit-2026-08-30.md
---

## 1. Exact finite stages

Choose finite-rank projections

```text
P_1<=P_2<=... in K(H),       P_n ->1 strongly,
```

and put

```text
A_n=B tensor P_n K(H) P_n,
p_n=e tensor P_n,
r_n=p-p_n=e tensor (1-P_n).
```

The projection `p_n` belongs to `A_n`.  The tail `r_n` annihilates `A_n` on
both sides: if `k=P_n k P_n`, then

```text
r_n(b tensor k)=eb tensor (1-P_n)k=0,
(b tensor k)r_n=be tensor k(1-P_n)=0.                   (FRS1)
```

Therefore

```text
E_n=C*(A_n,p)=A_n direct_sum C r_n
    isomorphic to (B tensor M_(rank P_n)) direct_sum C.  (FRS2)
```

These algebras are nested.  Indeed

```text
r_n=r_(n+1)+e tensor (P_(n+1)-P_n),                     (FRS3)
```

and the second summand lies in `A_(n+1)`.  Their union contains `p`, while
the union of the matrix corners `A_n` is dense in `A=B tensor K(H)`.
Consequently

```text
A+C p=closure(union_n E_n).                             (FRS4)
```

Matrix amplification and finite-direct-sum permanence give

```text
dim_nuc(E_n)=dim_nuc(B).
```

Inductive-limit permanence yields
`dim_nuc(A+C p)<=dim_nuc(B)`.  Conversely `A` is an ideal of `A+C p`, and
stabilization invariance gives

```text
dim_nuc(B)=dim_nuc(A)<=dim_nuc(A+C p),
```

proving `(SCP1)`, including the case of infinite nuclear dimension.

## 2. A two-sided nonquasidiagonal overlap

Let `T=C*(S)` be the Toeplitz algebra and `K=K(ell^2(N))`.  Define the
unital algebra

```text
B={ [a k; l b] in M_2(T) : a,b in T and k,l in K }      (FRS5)
```

and let `I_0=M_2(K)`.  Then `I_0` is essential in `B` and

```text
B/I_0 isomorphic to C(T) direct_sum C(T).                (FRS6)
```

Gardner--Tikuisis, [*The nuclear dimension of extensions of commutative
C-star algebras by the compact
operators*](https://arxiv.org/abs/2202.04695), applies to this essential
extension and gives `dim_nuc(B)=1`.

Let `e=diag(1,0) in B`, set `A=B tensor K(H)`, and
`p=e tensor 1_(B(H))`.  Direct multiplication gives the coefficient support
ideals

```text
L_0=closure(BeB)=[T K;K K],
R_0=closure(B(1-e)B)=[K K;K T],
L_0 intersect R_0=I_0.                                  (FRS7)
```

After tensoring by `K(H)`, these are the two support ideals and overlap for
`p` in `A`.  Both supports are proper.  They contain the essential ideal
`I=I_0 tensor K(H)`, so they are essential and cannot be complemented.
Thus both `p` and `1-p` are nonfull.

Put `E=A+C p`.  The overlap extension

```text
0 -> I -> E
  -> (C(T) tensor K(H))
       direct_sum (C(T) tensor K(H))~ ->0               (FRS8)
```

is not quasidiagonal.  To see this, let `q=1-p`.  Its multiplier corner is

```text
qEq=qAq=T tensor K(H),
qIq=K tensor K(H).
```

The corresponding corner quotient is `C(T) tensor K(H)`.  Thus the
stabilized Toeplitz extension maps into `(FRS8)`.  Its index boundary sends
the circle generator to a nonzero generator of `K_0(qIq)`.  Since `q` is
full on the overlap `I`, the corner inclusion

```text
K_0(qIq) -> K_0(I)
```

is an isomorphism.  Naturality therefore makes the boundary map of `(FRS8)`
nonzero.  A quasidiagonal extension has zero boundary maps, so `(FRS8)` is
not quasidiagonal and `I` has no approximate unit of projections
quasicentral in `E`.

Nevertheless the finite-rank tail splitting applies and gives

```text
dim_nuc(E)=dim_nuc(B)=1.                                 (FRS9)
```

This is a genuinely two-sided, nonfull, noncomplemented, nonquasidiagonal
instance of multiplier-projection colour reuse.
