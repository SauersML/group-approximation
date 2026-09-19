---
rg: 2
id: atlas-q14-exact-allows-full-coefficient-cyclicity
kind: claim
title: Exact q14 still allows the full multiplicity matrix algebra and a one-dimensional wandering seed
distinct_from:
  atlas-q14-relative-chart-rank-correction: that proves q14 can be made exact at flexible rank-small cost; this proves that doing so supplies no proper coefficient-algebra invariant subspace.
  atlas-morita-coefficient-cyclicity-reduction: that gives an unrestricted full-coefficient example; this keeps q14 exact in that example.
  atlas-left-ideal-rank-nonwandering: that uses all twelve packet cubes and collision after q14; this shows q14 alone cannot contribute the needed nonwandering conclusion.
---

ESTABLISHED.  For every `m>=2`, there are two repeated-natural binary Atlas
charts on `E=F2^4 tensor F2^m` such that q14 holds exactly, while the
multiplicity coefficient algebra of their relative chart change is

```text
C_T=M_m(F2).                                          (QFC1)
```

Consequently every nonzero one-dimensional multiplicity seed is cyclic for
the two chart algebras even under exact q14.

### Construction

Choose coordinates in which the marked natural transvection has nilpotent
part

```text
n=E_(23) in M_4(F2).
```

On `F2^m`, let

```text
X=sum_(i=1)^(m-1) E_(i,i+1),       Y=E_(m,1),
T=1+E_(13) tensor X+E_(14) tensor Y.                 (QFC2)
```

Both `E_(13)` and `E_(14)` commute with `E_(23)`, so `T` commutes with
`n tensor 1`.  Hence the two marked transvections are identical and q14 is
exact.  The added matrix in `(QFC2)` squares to zero, so `T^(-1)=T`.
Diagonal inverse blocks are identities; therefore the coefficient algebra
`C_T=<T_(ia)S_(bj)>` contains `X` and `Y`.  As in the Morita calibration,

```text
X^a Y X^b=E_(m-a,b+1)       (0<=a,b<=m-1),           (QFC3)
```

so every matrix unit belongs to `C_T`, proving `(QFC1)`.

This is not an augmented residual countermodel: no packet or collision
smallness is claimed.  It is an exact no-go for extracting the required
proper `C_T`-invariant subspace from q14 or the repeated-natural chart types
alone.
