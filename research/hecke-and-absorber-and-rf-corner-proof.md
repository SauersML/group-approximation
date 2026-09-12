---
rg: 2
id: hecke-and-absorber-and-rf-corner-proof
kind: route
title: Compute the D8 AND compression and detect every algebraic RF corner in a finite quotient
target: hecke-zero-compression-has-fixed-density-bass-serre-absorber
requires:
  - finite-character-hecke-intersection-formula
  - central-marked-two-cycle-zero-compression-cell
  - perfect-qc-separation-yields-finite-bcs-with-no-matrix-model
  - amenable-edge-cycles-cannot-create-an-lcs-gap
---

# Compute the D8 AND compression and its finite absorber

## 1. The packet is exactly D8

Let

```text
H=<x,y | x^2=y^2=1,[x,y]=1> ~= C_2^2
```

and let alpha be the automorphism

```text
alpha(x)=x,                 alpha(y)=xy.                 (1)
```

It has order two. The presentation (HAZ1) is therefore the semidirect
product

```text
D=H semidirect_alpha C_2.                               (2)
```

In particular, every element has a unique normal form h t^epsilon,
with h in H and epsilon in {0,1}, so |D|=8 and H embeds. If r=ty, then
r^2=x and r has order four; conjugation by t inverts r. Thus (2) is the
usual dihedral group of order eight.

The two commuting projections

```text
P_x=(1-x)/2,                  P_y=(1-y)/2
```

have product p as in (HAZ2). It is the joint spectral projection for the
character chi(x)=chi(y)=-1.

## 2. Exact character transport gives zero compression

Conjugating the Fourier sum term by term gives

```text
t p t^(-1)
 =1/4 (1-alpha(x))(1-alpha(y))
 =1/4 (1-x)(1-xy)
 =:p'.                                                     (3)
```

The projections p,p' are orthogonal. One direct calculation is

```text
(1-y)(1-xy)=(1+x)(1-y),                                  (4)
```

so multiplication by the factor 1-x in p makes pp'=0. Equivalently, the
two transported characters disagree on H, which is the special case of
finite-character-hecke-intersection-formula. Equation (3) now gives

```text
p t p=p(tpt^(-1))t=pp't=0.                              (5)
```

The canonical trace of p is its identity coefficient. Since the four
elements 1,x,y,xy are distinct,

```text
tau_D(p)=1/4.                                            (6)
```

The left regular representation is consequently an exact eight-dimensional
model of all group relations and (5) in which p has rank two. This already
disproves any implication from exact zero compression to vanishing AND mass.

## 3. The normalized-HS estimate

Let X,Y,T,P,P' be as in (HAZ5). Because X,Y are commuting reflections,
P,P' are projections and the calculation (4) gives PP'=0. Expanding the
conjugate of P yields

```text
TPT^*
 =1/4(1-TXT^*-TYT^*+TXYT^*).                           (7)
```

Moreover,

```text
TXYT^*=(TXT^*)(TYT^*),             Y=X(XY),
```

and multiplication by unitaries is isometric in normalized Hilbert--Schmidt
norm. Hence

```text
||TXYT^*-Y||_2
 <=||TXT^*-X||_2+||TYT^*-XY||_2
 =delta_x+delta_y.                                      (8)
```

Subtracting P'=(1-X-XY+Y)/4 from (7) and using (8) gives

```text
||TPT^*-P'||_2 <=(delta_x+delta_y)/2.                   (9)
```

Finally,

```text
||PTP||_2
 =||PTPT^*||_2
 =||P(TPT^*-P')||_2
 <=||TPT^*-P'||_2,                                      (10)
```

which proves (HAZ6). Notice what (10) controls: covariance defect forces
the compression to be small. Neither (9) nor (10) controls tr(P). The
regular D8 model has delta_x=delta_y=0 and tr(P)=1/4.

## 4. Every nonzero algebraic corner of an RF group reaches matrices

Write the nonzero algebraic projection in (HAZ7) uniquely as

```text
q=sum_(s in S) c_s s,                  c_s!=0,           (11)
```

where S is a finite subset of Gamma. For every pair s!=s' in S,
residual finiteness supplies a finite quotient in which their images differ:
apply it to s^(-1)s'!=1. Taking the product of these finitely many quotients
gives one finite quotient

```text
varphi:Gamma -> Q
```

whose restriction to S is injective. The group elements of Q are a linear
basis of C[Q], so

```text
qbar=sum_(s in S)c_s varphi(s) !=0.                    (12)
```

The quotient map induces a unital star homomorphism

```text
C^*(Gamma) -> C^*(Q).
```

It sends q to the nonzero projection qbar. Composing (HAZ8) with it gives

```text
A -> qbar C^*(Q) qbar.                                  (13)
```

Represent C^*(Q) on ell^2(Q) by the left regular representation and
restrict (13) to qbar ell^2(Q). This space is finite-dimensional and
nonzero, and 1_A acts on it as the identity qbar. Thus (13) is a unital
finite-dimensional star representation of A. Injectivity of the original
map never entered.

Apply this to the finite SynchBCS algebra whose lack of matrix
representations is proved in
perfect-qc-separation-yields-finite-bcs-with-no-matrix-model.
It cannot have a unital realization in any nonzero algebraic corner of an
RF group.

## 5. Finite Bass--Serre consistency ports are absorbed exactly

The fundamental group of a finite graph of finite groups is virtually free,
hence residually finite. This is the finite-cell specialization recorded
in amenable-edge-cycles-cannot-create-an-lcs-gap.

Suppose such a graph contains D as a vertex group. Bass--Serre normal form
embeds every vertex group. In the preceding residual-finiteness argument,
enlarge S by all eight elements of D before separating pairs. The resulting
finite quotient is simultaneously injective on supp(q) and on D. Therefore
(12)--(13) still hold, while the quotient regular trace restricts to the
canonical trace on the embedded D8 packet. Equations (5)--(6) survive
exactly:

```text
p t p=0,                    tr(p)=1/4.                  (14)
```

All amalgam and HNN relations in the finite graph also hold exactly. Thus a
finite collection of consistency ports cannot convert the local Hecke
mismatch into a mass decoder: at zero presentation error and zero
compression error it retains the full forbidden quarter.

This leaves a sharp boundary. A successful one-sided return must either
make the algebraic marked corner invisible to every finite quotient, or use
a non-Bass--Serre relation whose consequence is genuinely restricted to
finite matrix coordinates. Pure finite-trace rank inequalities are not
enough: they also hold in the faithful canonical group trace, where the
packet atom (6) is positive.
