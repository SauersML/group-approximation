# A native second-argument marginal forces even feedback collisions

Date: 2026-09-08. Exact handwritten Boolean proof. No search, code,
build, or computational verification was run. This gives a collision
for the six-term encoder in Section 6 of
`forward-memory-cover-and-native-prefix-test-2026-09-08.md`, and for
a larger family with its same second-argument marginal.

## 1. The native marginal and the larger excluded family

Use the binary Leavitt unit group Q, with prefix addition and deletion
operators s_0,s_1,t_0,t_1. For a finite word v, s_v adds v and t_v
deletes a matching prefix v, returning zero on a mismatch. The complete
ordered chart partitions are

    D_1=(01,1,000,001),       D_2=(00,1,010,011).

In each chart b_i is the copy of the matrix b below. Its inverse is
displayed as well; both matrices act on columns.

    b = [1 0 0 0]            b^-1 = [1 0 0 0]
        [0 1 0 0]                   [0 1 0 0]
        [0 1 1 1]                   [0 0 0 1]
        [0 0 1 0]                   [0 1 1 1].

The three primitive roots in the second argument of that encoder are

    y=q32(e*)=1+s_1 t_010,
    w=q32(f*)=1+s_1 t_011,
    u=q32(1) =1+s_1 t_01.                              (1)

All three are involutions. For a binary configuration U on Q define

    L(U)(g)=U(g)+U(gb_1)+U(gb_2)+U(gy)+U(gw)+U(gu).    (2)

Let m>=2 be even. Allow different equivariant finite-memory bilinear
operations B_i in the cyclic rule

    F_i(X)=X_i+B_i(X_(i+1),X_(i+2)),       i modulo m.   (3)

Suppose only that, for every odd i and every U,

    B_i(1,U)=L(U),                                    (4)

where 1 is the constant-one configuration. Then F is noninjective.
The operations in even output coordinates are arbitrary. No symmetry,
alternation, or condition on the first-argument addresses is assumed.

In particular (4) holds for any bilinear rule

    B_i(A,U)(g)=sum_(j=1)^6 A(gr_(i,j)) U(gc_j),
    (c_1,...,c_6)=(b_1,b_2,y,w,u,1),                  (5)

with arbitrary first-argument addresses r_(i,j) in Q. Repeated first
addresses are allowed. More generally, adding any bilinear operation
C_i with C_i(1,U)=0 preserves the obstruction.

## 2. An exact nonzero kernel mask

Let Omega be the eventually-zero infinite binary words, and let V be
the free F_2-vector space on basis e_omega, omega in Omega. The prefix
operators act on V and satisfy the Leavitt relations, so every group
element g in Q acts invertibly. All vectors in V have finite support.

Let epsilon sum the coefficients of a vector. Define another linear
functional by

    lambda=epsilon composed with (t_11+t_010+t_0111).  (6)

Thus lambda counts, modulo two, basis vectors in the three disjoint
cylinders 11, 010, and 0111. In particular it is well defined without
summing an infinite configuration. Put

    T=b_1^-1+b_2^-1+y+w+u                             (7)

as an operator on V. We prove lambda T=0.

Using the displayed inverse matrix in each complete chart, and (1),
expansion on the common complete prefix partition gives

    T s_000 = s_001,
    T s_001 = s_000+s_001,
    T s_010 = s_011+s_1+s_10,
    T s_011 = s_010+s_011+s_1+s_11,
    T s_1   = s_1+s_001+s_011.                        (8)

For example b_1^-1 s_010=s_010 and
b_2^-1 s_010=s_011. The root sum is

    y+w+u=1+s_1(t_010+t_011+t_01),

whose value on s_010 is s_010+s_1+s_10; the two s_010
terms cancel. The other four rows follow from the same column
expansion, so (8) is an identity of prefix operators, with arbitrary
tails still present.

Direct prefix deletion in (6) gives

    lambda s_000=lambda s_001=lambda s_10=0,
    lambda s_010=lambda s_11=epsilon,
    lambda s_011=lambda s_1=epsilon composed with t_1. (9)

Each row of (8) is annihilated by (9). The words
000,001,010,011,1 form a complete prefix partition; their images
span V. Therefore lambda T=0 on all of V.

Choose omega_*=110^infinity and define the actual binary configuration

    U(g)=lambda(g^-1 e_(omega_*)),       g in Q.       (10)

It is nonzero: U(1)=1. The inverse in (10) is essential. Indeed

    U(gb_1)+U(gb_2)+U(gy)+U(gw)+U(gu)
      =lambda(T g^-1 e_(omega_*))=0,                 (11)

where the three roots equal their inverses. Combining (2) and (11)
proves

    L(U)=U.                                         (12)

No finite support is claimed for U. A full-shift collision does not
require finite support.

## 3. Literal collisions, independent of decoder degree and memory

For each odd i set X_i=U; for each even i set X_i=1. By (4) and
(12), every odd output of F(X) is U+U=0. Write the even outputs as

    V_i=1+B_i(U,1),       i even.

Now set X'_i=0 on odd tracks and X'_i=V_i on even tracks. Every
quadratic term in F(X') has a zero operand, so

    F(X)=X'=F(X').                                   (13)

The inputs differ at the identity of every odd track because U(1)=1.
This proves noninjectivity of the whole family in Section 1.

For the specific four-track operation

    J(A,U)(g)=A(ga_1)U(gb_1)+A(ga_2)U(gb_2)
              +A(gx)U(gy)+A(gz)U(gw)
              +A(gv)U(gu)+A(g)U(g),

the first arguments disappear when A=1, giving precisely (2).
Consequently, with V_0=1+J(U,1), the candidate from the forward-memory
artifact has the explicit collision

    F(U,1,U,1)=(0,V_0,0,V_0)=F(0,V_0,0,V_0).         (14)

It admits no left inverse of any degree, locality, or memory size.
Authenticating the native Leavitt commutator relation in a larger
decoder window cannot change the collision of the specified encoder.

## 4. Scope relative to the other feedback obstructions

The bipartite-operand proof in
`gottschalk-quadratic-block-elimination-2026-09-08.md` already shows
that injectivity would imply surjectivity for every even cyclic
bilinear rule. This artifact establishes the stronger negative
conclusion of noninjectivity for the particular native marginal (2).
Changing the first-argument addresses, or even changing every even
output operation, cannot repair this family while (4) remains true.

The mask here differs from the coefficient-sum mask used for the
alternating consecutive-chart rule in
`gottschalk-consecutive-chart-dual-boundary-collision-2026-09-08.md`.
That mask annihilates 1+a_i^-1+b_i^-1; the present weighted-cylinder
functional annihilates (7), which includes the three primitive roots.
Neither collision gives a conclusion about arbitrary CA on Q.

For another algebraic description, put P=b_1+b_2+y+w+u in F_2[Q]
and Phi(g)=U(g) on group-basis vectors. Equation (11) says
Phi(gP)=0 for every g, while Phi(1)=1. Thus F_2[Q]P is a proper
left ideal. This does not refute stable finiteness of F_2[Q]; no
one-sided inverse for P is asserted. It identifies the exact linear
obstruction within this nonlinear construction.
