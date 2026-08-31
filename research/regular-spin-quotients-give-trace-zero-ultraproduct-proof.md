---
rg: 2
id: regular-spin-quotients-give-trace-zero-ultraproduct-proof
kind: route
title: Use regular finite quotients to keep the shared center at trace zero
target: property-t-actor-keeps-fd-invisible-center-in-lef-models
requires:
  - shared-center-extraspecial-wreath-has-fd-invisible-spin-sector
  - shared-center-extraspecial-wreath-sector-and-normalizer-proof
---

# Use regular finite quotients to keep the shared center at trace zero

All matrix traces and Hilbert--Schmidt norms below are normalized.

## 1. The group and its exact finite-dimensional radical

Let G=SL_3(Z), let X=G with the left regular action, and set

~~~text
Pi_reg=E(G) semidirect G.
~~~

Fix a finite symmetric generating set S of G. Transitivity and the
shared-center relations give

~~~text
Pi_reg=<S,A_e,B_e>,               J=[A_e,B_e].            (1)
~~~

The finite-support normal form in E(G) shows that J is a nonidentity
central involution.

Let rho:Pi_reg -> U(d) be exact. Since rho(J) is a central involution, its
negative eigenspace H_- is invariant. For any finite set F subset G of
cardinality m, the restriction of H_- to E(F) is a direct sum of copies of
the unique irreducible representation with J=-1. That irreducible has
dimension 2^m. Hence

~~~text
2^m divides dim(H_-)                  for every m.         (2)
~~~

Because dim(H_-) is finite, (2) forces H_-=0. Thus rho(J)=I. Notice that
this argument uses all finite windows simultaneously.

## 2. Residual finiteness gives quotients injective on balls

The group G is residually finite: it is a finitely generated linear group,
or directly one may use reduction modulo integers after separating a
nonidentity matrix entry.

Let B_G(n) be the radius-n ball for S. For each ordered pair g!=h in that
finite ball, residual finiteness supplies a finite-index normal subgroup
which does not contain h^(-1)g. Intersect these finitely many subgroups.
The resulting quotient

~~~text
q_n:G -> Q_n                                             (3)
~~~

is injective on B_G(n). No nesting assumption is needed.

For a finite set Y, write E(Y) for the finite shared-center extraspecial
group with one Pauli pair at every y in Y. The left regular action of Q_n
on itself permutes these pairs, so

~~~text
P_n=E(Q_n) semidirect Q_n                                (4)
~~~

is a finite group. Mark it by

~~~text
s |-> q_n(s)       (s in S),
A_e |-> A_1,
B_e |-> B_1.                                            (5)
~~~

The common commutator [A_1,B_1] in P_n is the nontrivial central
involution J_n of E(Q_n).

## 3. Exact local convergence of the marked finite groups

We verify the marked-group convergence explicitly. Every element of Pi_reg
has a unique form

~~~text
J^c product_(g in F) A_g^(a_g) B_g^(b_g) times h,        (6)
~~~

where c,a_g,b_g are in {0,1}, F is finite, and h is in G. Fix once and for
all an ordering when writing the finite product. Multiplication of two
forms (6) uses only:

- multiplication of their actor components;
- left translation of one finite support by an actor component;
- equality tests between the finitely many resulting sites;
- the single-site rule B_g A_g=J A_g B_g.

Now take a marked word v of length at most R in
S union {A_e,B_e}. While collecting v into (6), every site which occurs is
an actor prefix of v and hence lies in B_G(R); the actor component also
lies in B_G(R). If n>=R, injectivity of q_n on that ball preserves every
site equality test and the actor component. Therefore collection of v
inside P_n gives exactly the q_n-labelled copy of its normal form (6).

It follows that

~~~text
v=1 in Pi_reg       implies       v(P_n)=1 for n>=|v|,   (7)
v!=1 in Pi_reg      implies       v(P_n)!=1 for n>=|v|.  (8)
~~~

For (8), either the actor component is nontrivial and is preserved by
injectivity, or its finite base normal form has a nonzero exponent and
remains a nontrivial normal form in E(Q_n). Equations (7)--(8) say that
the marked finite groups P_n converge to Pi_reg. Equivalently, Pi_reg is
LEF.

This is a local map, not a homomorphism Pi_reg -> P_n. Far-apart sites of
G can collide in Q_n, and then an off-site A--B commutator would become the
central J_n. The point is exactly that no collision occurs inside any
fixed word window once n is large enough.

## 4. The trace-zero matrix ultraproduct

Let lambda_n:P_n -> U(l2(P_n)) be the left regular representation. A
nonidentity element of a finite group acts without fixed points in its
left regular action, so

~~~text
tr(lambda_n(p))=0                   for p!=1.             (9)
~~~

Compose the marking (5) with lambda_n. Equation (7) says that every fixed
relation of Pi_reg has eventually zero defect, in operator norm as well as
in normalized Hilbert--Schmidt norm. Equations (8)--(9) say that every
fixed nonidentity word has eventually trace zero. Thus these markings give
an asymptotically faithful tracial matrix model.

In particular J_n!=1 and J_n^2=1, so for every n,

~~~text
tr(lambda_n(J_n))=0,
||lambda_n(J_n)-I||_2^2
 =2-2 Re tr(lambda_n(J_n))
 =2.                                                       (10)
~~~

The metric ultraproduct therefore contains an exact representation of
Pi_reg in which J is a trace-zero involution. This is the ultraproduct
loophole in its strongest fixed-window form: at stage n the negative spin
representation has the finite dimension 2^(|Q_n|), so no finite
divisibility contradiction occurs.

## 5. Property (T) and local reflexivity do not remove the models

The classical Kazhdan theorem gives property (T) for SL_3(Z). Let
(K,kappa) be a Kazhdan pair for G. If a unitary representation of Pi_reg
has a (K,kappa)-almost-invariant vector, its restriction to G has a
nonzero G-invariant vector. Hence

~~~text
(Pi_reg,G) has relative property (T).                    (11)
~~~

This is a genuine relative-property statement but it concerns
almost-invariant vectors. The spin vectors used in Section 4 are not
almost invariant for the actor, and (11) gives no estimate involving the
number of visible sites or the matrix dimension.

There is also no local-reflexivity escape. The group E(G) is locally
finite, hence amenable, and

~~~text
C_r^*(Pi_reg)
 = C_r^*(E(G)) reduced_crossed_product G.                (12)
~~~

The algebra C_r^*(E(G)) is nuclear. The group G is exact because countable
linear groups are exact; equivalently, one may invoke the
Guentner--Higson--Weinberger exactness theorem for linear groups. Reduced
crossed product by an exact group preserves exactness of an exact
coefficient algebra. Therefore C_r^*(Pi_reg) is exact. Kirchberg's
exactness theorem then gives local reflexivity.

Sections 3--4 already provide exact finite models of every fixed
operator-system/relation window. Local reflexivity cannot turn those local
models into the global all-window divisibility assertion (2).

## 6. Exact boundary of the no-go

The example proves that none of the following data, alone or in
combination, promotes exact finite-dimensional invisibility of J to
asymptotic normalized-HS invisibility:

~~~text
- a finitely generated group and a central involution;
- relative property (T) for the actor subgroup;
- exactness and local reflexivity of the reduced group algebra;
- exact finite-dimensional realization of every fixed relation window.
~~~

It does not establish LLP for either full or reduced group C*-algebra, and
it does not establish that either algebra is MF. These properties are not
formal consequences of LEF or of exactness. Accordingly the construction
is an obstruction to using LLP-like *local* lifting without a uniform
dimension/window modulus, but it is not a counterexample to a theorem
whose hypotheses genuinely include LLP or MF and exploit more than fixed
windows.

The example is also not asserted to be finitely presented. The
Q8/BS(2,3) terminal group supplies a separate finitely presented
hyperlinear countermodel, while Pi_reg supplies the property-(T) and
local-reflexivity countermodel. Combining those interfaces in one
finitely presented group with a quantitative spin-window theorem remains
open. No nonhyperlinear group is proved.
