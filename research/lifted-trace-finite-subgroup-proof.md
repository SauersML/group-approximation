---
rg: 2
id: lifted-trace-finite-subgroup-proof
kind: route
title: Lift idempotents and equivalences p-adically and compute finite regular ranks
target: lifted-trace-detects-finite-subgroup-projectives
requires: []
---

## The complete coefficient ring

Put C=c_0(G,Z_p), with convolution and the supremum p-adic norm. Finite
support is dense, multiplication is continuous, and C/pC=F_p[G]. The
coefficient at 1 is a continuous cyclic trace: it is cyclic on finite
supports by reindexing g with g^(-1), and therefore on C by continuity.
For matrices use the sum of diagonal identity coefficients, denoted T.
It also satisfies T(XY)=T(YX) for compatible rectangular matrices.

Every element of 1+p M_n(C) is invertible by a convergent geometric
series. An idempotent in p M_n(C) is zero: if its norm is r, then
0 <= r <= 1/p and r <= r^2, forcing r=0.

## Lifting and invariance

Every idempotent e over F_p[G] has an idempotent lift E over C. Start
with a finite-support coefficient lift a and repeatedly replace a by
3a^2-2a^3. This preserves the reduction modulo p, and if delta=a^2-a,
the new defect is delta^2(4delta-3). Consequently the defects converge
to zero at least quadratically and the iterates are Cauchy. All formulas
are polynomials in one element, so they hold in a noncommutative ring.

Two lifts E,E' of the same idempotent are conjugate. Indeed

    W=E'E+(1-E')(1-E)

reduces to 1, so is invertible, and WE=E'W. Their traces agree.

Equivalences also lift. Suppose xy=e and yx=f, with x in e M(C/pC) f
and y in f M(C/pC) e, using compatible rectangular matrices if needed.
For chosen idempotent lifts E,F, choose corner lifts X=E X_0 F and
Y=F Y_0 E. Then XY is invertible in the E-corner because XY=E modulo p.
Set Y'=Y(XY)^(-1). Thus XY'=E. The element Y'X is an idempotent in the
F-corner reducing to f. Hence F-Y'X is an idempotent in p M(C), so zero.
Therefore Y'X=F and T(E)=T(XY')=T(Y'X)=T(F).

Thus T(E) depends only on the isomorphism class of the projective
represented by e. It is additive under direct sum, and defines a map
t_p:K_0(F_p[G])->Z_p. No finiteness or soficity of G was used.

## Evaluation on a finite subgroup

For e in M_n(F_p[H]) with H finite, the polynomial iteration stays
inside the finite free Z_p-algebra M_n(Z_p[H]). Thus we may choose its
limit E in that algebra. Acting on Z_p[H]^n, E splits a finite free
Z_p-module. Its image is free of rank

    d=dim_(F_p)(e F_p[H]^n),

because reduction modulo p preserves the direct-sum splitting. Over Q_p
the ordinary linear trace of E is d. On the other hand, the regular
action of a group element h has zero trace unless h=1, in which case
its trace is |H|. Therefore

    |H| T(E)=d,       T(E)=d/|H| in Q_p.

As E has integral coefficients, this value lies in Z_p. If e!=0 then
d>0, so this rational value is nonzero and has infinite additive order.
The computation is unchanged on inducing from H to G, since E and its
identity coefficient are unchanged.

## Consequences

For f<e in M_n(F_p[H]), e-f is a nonzero idempotent orthogonal to f,
and [e]-[f]=[e-f]. Its lifted trace is a strictly positive rational
number. Thus the difference class is nonzero and has infinite order;
in particular no common projective stabilization can identify e and f.

If BA=I over F_p[G], AB is idempotent and equivalent to I, so

    [I-AB]=[I]-[AB]=0 in K_0(F_p[G]).

A nonzero idempotent I-AB supported in a finite subgroup would have
nonzero lifted trace, a contradiction. Likewise a nonzero finite direct
sum of finite-subgroup projectives has lifted trace a sum of positive
rational numbers and hence cannot be the defect module. Positivity is
used only for these rational numbers; no order on Z_p is assumed.

This supplies no positivity statement for projectives of arbitrary
infinite support-generated subgroup. Establishing or violating the
necessary zero-class condition there remains part of the headline problem.
