---
rg: 2
id: leavitt-balanced-corners-modulo-four-proof
kind: route
title: Lift a hypothetical corner equivalence through a square-zero ideal and compare traces
target: leavitt-balanced-corners-separated-modulo-four
requires:
  - leavitt-trace-balanced-nested-idempotents
  - lifted-trace-detects-finite-subgroup-projectives
---

## Explicit obstruction without a completion

Work in T=(Z/4)[Q]. For a group element u of order three,
(2+u+u^2)^2=2+u+u^2 modulo four. Since g and h commute, E and C
are commuting idempotents, and F=EC is an idempotent with EF=FE=F.
Reduction gives precisely e,c,f. Independence of g,h ensures no
nonidentity term in the product contributes to the identity coefficient,
so T(E)=2 and T(F)=2*2=0 modulo four.

Suppose x in eSf, y in fSe satisfy xy=e and yx=f. Choose arbitrary
finite-support lifts and corner them to obtain X in ETF and Y in FTE.
Write XY=E+N where N is in 2ETE. As N^2=0,

    (E+N)^(-1)=E-N in ETE.

Set Y'=Y(E-N). Then XY'=E and K=Y'X is an idempotent in FTF,
reducing to f. Hence F-K lies in 2T and is idempotent, while every
element of 2T squares to zero. It follows that K=F. The coefficient
trace is cyclic on T, so

    2=T(E)=T(XY')=T(Y'X)=T(F)=0 in Z/4,

a contradiction. This proves the unstabilized assertion directly.

## K_0 and all common stabilizations

In Z_2[<g,h>] the lifts may instead be written

    E_2=(2-g-g^2)/3,   C_2=(2-h-h^2)/3,   F_2=E_2 C_2.

They are idempotents because E_2=1-(1+g+g^2)/3 and similarly for
C_2. They reduce to e,c,f and satisfy

    T(E_2)=2/3,       T(F_2)=4/9,
    t_2([eS]-[fS])=2/9 != 0.

By `lifted-trace-detects-finite-subgroup-projectives`, this trace is
invariant under projective isomorphism and additive. Thus eS and fS
remain inequivalent after adding any common finitely generated
projective module. This does not depend on whether that additional
projective comes from a finite subgroup.
