---
rg: 2
id: purely-infinite-all-rank-mf-quotient-proof
kind: route
title: Two orthogonal unit corners reduce arbitrary units and close the rank-one MF classification
target: purely-infinite-all-rank-mf-quotient
requires:
  - full-complementary-idempotent-elementary-full-mf-radical
  - supported-unit-commutators-lie-in-corner-units
artifacts:
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsPeirce.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsReductionProof.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsMatrixReduction.lean
  - GroupApproximation/Algebra/PurelyInfiniteSimpleMatrix.lean
---

Let H = R^x, let N be its MF-hom kernel, and let C be the subgroup generated
by all images in H of EL_m(S), m >= 2, for countable rings S with a full
complementary idempotent. The first prerequisite gives C <= N. Countability
and the internal countable-abelian-MF theorem give N <= [H,H].

We prove the remaining reduction explicitly. This proof uses no generalized
matrix-ring representation of R and no unstated elimination citation.

## 1. Normality and the two corners

C is normal: conjugating any homomorphism EL_m(S) -> H by a unit of R gives
another homomorphism included in the definition of C. Consequently every
conjugate of every generating image is again contained in C.

Pure infiniteness supplies s_0,t_0,s_1,t_1 with

    t_i s_j = delta_ij.

Indeed, the existing shifted-complement construction produces two orthogonal
nonzero idempotents, and single-sandwich comparability embeds a copy of 1
inside each. Normalizing those equivalences gives the displayed witnesses.
Put e_i = s_i t_i. They are nonzero orthogonal idempotents.

For every c in R the units

    T_ij(c) = 1 + s_i c t_j,       i != j,

belong to C. They are images of elementary matrices under the homomorphism

    A |-> 1 - e_0 - e_1 + sum_ij s_i A_ij t_j.

The source ring R has a proper isometry with full defect, so this is one of
the families defining C. In particular, any x with e_i x = x = x e_j
satisfies 1+x in C, since x = s_i(t_i x s_j)t_j.

## 2. All Peirce operations at either corner belong to C

Fix e=e_i and f=e_j, i != j. Write a=s_i t_j and b=s_j t_i, so ab=e,
ba=f, a=eaf and b=fbe. Both 1+a and 1+b belong to C.

First suppose ex=x and xe=0. Set y=xf and z=x-y. Then y=eyf, so 1+y is
in C. Also ez=z, ze=zf=0, and

    a(bz)=z,       (bz)a=0,       a^2=(bz)^2=0.

For square-zero A,B with BA=0 the direct multiplication identity is

    [1+A,1+B] = 1+AB.

Apply it with A=a and B=bz. Normality of C and 1+a in C put 1+z in C.
Finally yz=0, so (1+y)(1+z)=1+x belongs to C.

If instead ex=0 and xe=x, set y=fx and z=x-y. Here 1+y is in C, and

    (za)b=z,       b(za)=0,       (za)^2=b^2=0.

The same identity and 1+b in C give 1+z in C. Again yz=0, and 1+x is in C.
Thus both off-diagonal Peirce families at e_0 and e_1 lie in C, including
their components outside e_0+e_1.

## 3. Make the first corner nonzero

Take any unit u and set e=e_0. We have eu != 0, since eu=0 would imply
e=euu^(-1)=0. If eue != 0, no move is needed. Otherwise choose p,q with
p(eu)q=1, and put x=(1-e)qe. Section 2 shows 1+x in C. For u'=u(1+x),

    eu'e = euqe != 0.

Nonvanishing follows because p(euqe)=e != 0. The coefficient
a=t_0 u' s_0 is therefore nonzero, since eu'e=s_0 a t_0.

Every step here preserves the coset modulo C, including right multiplication,
because C is normal.

## 4. Plant an identity in the second corner

Write a=t_0 u' s_0 and b=t_0 u' s_1, and choose p,q with paq=1. Let

    rho=q(1-pb),      u_1=u' T_01(rho).

Its (0,1) coefficient is b+a rho, whose product on the left by p equals 1.
If d=t_1 u_1 s_1, set

    u_2=T_10((1-d)p) u_1.

The (1,1) coefficient of u_2 equals d+(1-d)p(b+a rho)=1. Hence, for f=e_1,

    f u_2 f=f.

Both multiplying factors belong to C by Section 1.

## 5. Clear the second row and column

Let x=-f u_2(1-f) and w=1+x. Section 2 puts w in C. With d=u_2 w,

    fd=fu_2-(fu_2f)u_2(1-f)=fu_2-fu_2(1-f)=f.

Next put y=-(1-f)df and v=(1+y)d. Section 2 also puts 1+y in C.
Since fd=f and f^2=f, multiplication gives fv=f and vf=f. Expanding the
complementary corner now gives the exact supported form

    v=f+(1-f)v(1-f).

Throughout we multiplied on the left or right by elements of C, so uv^(-1)
is in C. This proves the arbitrary-unit reduction, with f != 0. Notice that
no commutator or K1 assumption on u was used.

## 6. Close the MF quotient theorem

Now take u in [H,H]. The reduction gives uv^(-1) in C <= N <= [H,H], so v
also belongs to [H,H]. The second prerequisite puts this supported v in C.
It follows that u=(uv^(-1))v belongs to C. Thus

    [H,H] = C = N.

There is also an intrinsic conclusion. For a homomorphism C -> M to an MF
group, compose with each generating homomorphism EL_m(S) -> C. The first
prerequisite makes every such composite trivial. Its kernel therefore
contains every generating image and hence all of C. Thus C=[H,H] itself has
full MF radical. This argument concerns all homomorphisms defined on C;
it does not assume that they extend to H.

The quotient is the countable abelianization and is MF. Every homomorphism
H -> M to an MF group kills N=[H,H] and descends to abelianization; the
surjectivity of the quotient map makes the descent unique.

For n >= 1, M_n(R) is countable purely infinite simple by the internally
proved matrix-ring theorem. Applying the unit-group argument to M_n(R)
gives the claimed classification at every rank. No identification with
canonical algebraic K1 is used in this last step.
