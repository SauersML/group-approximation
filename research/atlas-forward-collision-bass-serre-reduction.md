---
rg: 2
id: atlas-forward-collision-bass-serre-reduction
kind: claim
title: The minimal forward-collision carrier is one relator over an explicit virtually free graph of finite groups
artifacts:
  - research/artifacts/atlas-a4-forward-collision-bass-serre-reduction.json
distinct_from:
  atlas-shared-forward-fan-is-2four-by-3two: that computes the finite 144-state carrier for one forward edge and its adjacent core edge; this adjoins both internal S3 supports needed by collision and reduces the sole remaining constraint to one cyclically reduced word.
  atlas-a4-collision-assisted-opaque-star-compiler: that asks for a dimension-independent matrix estimate on the full packet; this is an exact algebraic reduction of the smallest forward-collision support and leaves the one-relator quotient's vertex injection unresolved.
---

Let

```text
F=<r,z,c | r^3=z^3=c^2=[r,z]=[c,r]=1, c z c=z^-1>
  ~= C3 x S3,
A=<r,z> ~= C3 x C3,
C=<r,z,b | r^3=z^3=b^2=[r,z]=(r^-1 b)^3=(z b)^3=1>
  ~= C2^4 semidirect (C3 x C3),
K=<t,s | t^3=s^2=(s t)^2=1> ~= S3,
B=<b> ~= C2,                 b=s t.
```

Here `C` is the 144-state shared-forward-fan carrier, `F` supplies the
missing first-chart `S3` reflection `c`, and `K` supplies the second-chart
collision letters.  Before imposing collision their universal completion is

```text
G0 = F *_A C *_B K.                                  (A4-BS-1)
```

It is an infinite virtually free group with rational Euler characteristic

```text
chi(G0)=1/18+1/144+1/6-1/9-1/2=-55/144.              (A4-BS-2)
```

Moreover the three vertex regular representations glue at every atlas
multiplicity.  On a common `20160k`-dimensional Hilbert space take

```text
1120k Reg(F),          140k Reg(C),          3360k Reg(K).
```

Their restrictions to `A` are both `2240k Reg(A)`, and their restrictions
to `B` are both `10080k Reg(B)`.  Thus there is no representation-ring or
regular-multiplicity obstruction before the collision word is imposed.

In these generators the collision is

```text
q=t c s c t^-1 c s t c.
```

Writing `D=F *_A C` and using `s t=b`, its cyclically reduced normal form in
`D *_B K` has six alternating syllables

```text
t | c | s | c | t^-1 | c b c.                        (A4-BS-3)
```

In particular `q` is nontrivial and hyperbolic in `G0`; it is not a
translation in the normal `C2^4` of `C`.  Therefore the tempting shortcut in
which collision is a nonzero translation whose normal closure kills the
144-state carrier does not apply.  The exact remaining finite-model question
is the binary vertex-injection problem for

```text
Gamma=G0/<<q>>: do F,C,K embed in a finite quotient of Gamma?             (A4-BS-4)
```

A positive answer gives compatible finite regular carriers; a proof that
`b=1` in `Gamma` gives the desired algebraic obstruction.  Neither conclusion
is asserted here.  Also, the length-six relator does **not** satisfy relative
`C'(1/6)`: the repeated `c` is a one-syllable piece and strict `C'(1/6)`
would require its length to be less than one.
