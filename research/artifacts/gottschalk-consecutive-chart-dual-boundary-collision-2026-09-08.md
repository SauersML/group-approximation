# Exact dual-boundary collision for consecutive chart feedback

Date: 2026-09-08. The proposed consecutive-chart encoder is not
injective. This note gives a concrete full-shift collision and a
nonzero functional on its constant-control quotient module. No
computation, approximation, or unproved group property is used.

## The specified encoder

For the binary Leavitt atlas generators define

    C(U,V)(g)=U(g a_1)V(g b_1)+U(g b_1)V(g a_1),
    D(U,V)(g)=U(g a_2)V(g b_2)+U(g b_2)V(g a_2).

The four-track rule from
`experiments/gottschalk-consecutive-chart-feedback-2026-09-08.md` is

    F(x)=(x_1+C(x_2,x_3), x_2+C(x_3,x_4),
          x_3+D(x_4,x_1), x_4+D(x_1,x_2)).

It is triangular and reversible on inputs supported inside either
isolated finite chart. The collision below is a global configuration
and passes beyond those isolated controls.

## A common kernel from coefficient parity

Let Omega be the eventually-zero infinite binary words, and let V
be the free F_2-vector space with basis e_omega for omega in Omega.
Prefix addition s_i and matching-prefix deletion t_i act on V and
satisfy the binary Leavitt relations. Every Leavitt unit g therefore
acts invertibly on V. Define

    epsilon(sum c_omega e_omega)=sum c_omega in F_2.

All vectors in V have finite support, so every displayed sum is
finite. No summation of an infinite configuration is involved.

In each atlas chart the inverses of the native matrices are

    a^-1 = [1 1 0 0]          b^-1 = [1 0 0 0]
           [1 0 1 0]                   [0 1 0 0]
           [0 0 1 0]                   [0 0 0 1]
           [0 0 0 1]                   [0 1 1 1].

Their column-sum vectors are respectively (0,1,0,1) and
(1,0,1,0). Consequently, for both complete prefix chart embeddings,

    epsilon composed with (I+a_i^-1+b_i^-1)=0.             (1)

The complete prefix partition makes (1) valid for every vector in V,
not merely for four basis vectors with one chosen tail.

Fix omega_0=0^infinity. Define the actual binary configuration on Q

    U(g)=epsilon(g^-1 e_(omega_0)).                         (2)

It is nonzero, since U(1)=1. For every g in Q and i=1,2,

    U(g)+U(g a_i)+U(g b_i)
      =epsilon((I+a_i^-1+b_i^-1)g^-1 e_(omega_0))=0.        (3)

Thus, with the constant configuration W=1,

    C(U,1)=D(U,1)=U.                                      (4)

This is the missing common eigenmask. In representation language,
the constant coefficient-sum functional is a common-kernel vector
in the contragredient natural boundary module, where g acts by
g^(-T). The inverse and transpose are essential; the covariant
tensor-square control in the design note has zero common kernel.

## Literal collision of the four-track rule

Alternation gives C(U,U)=D(U,U)=0. Substitution of (4) yields

    F(U,1+U,U,1+U)=(0,1,0,1)=F(0,1,0,1).                 (5)

The inputs differ already at the identity because U(1)=1. Equation
(5) is an exact collision on the full shift. The configuration U is
defined by (2); finite support is neither asserted nor required.
Hence F admits no left inverse and cannot refute surjunctivity.

## The left-ideal obstruction is decided: the ideals are proper

Let R=F_2[Q], P_i=1+a_i+b_i, and let tau be the order-two prefix
swap of 00 and 01 fixing 1. The chart dictionaries give
P_2=tau P_1 tau. Since tau permutes the boundary basis,
epsilon composed with tau equals epsilon. Equation (2) therefore
also satisfies U(g tau)=U(g).

Define a linear functional Phi:R to F_2 on the group basis by
Phi(g)=U(g). Equations (3) and tau-invariance give, for every g,

    Phi(g P_1)=Phi(g P_2)=Phi(g(1+tau))=0,
    Phi(1)=1.

It follows rigorously that BOTH left ideals

    R P_1+R P_2,       R P_1+R(1+tau)

are proper. The corresponding quotient modules are nonzero.
In particular no finite Bezout identity expressing 1 in either
ideal exists. This resolves the specified constant-W obstruction
in favor of a collision, not in favor of a decoder.

## Scope of the obstruction

The same epsilon identity holds for a,b embedded in any complete
finite binary prefix chart. Thus all alternating operations built
from these same two native matrices, in arbitrary such charts,
share the eigenmask (2). Reassigning those operations among the four
cyclic coordinates still gives collision (5). Any further design
must change that matrix-level column-sum identity or change the
nonlinear architecture; changing only the chart assignment cannot
repair this family.

This excludes the specified feedback family. It neither proves
surjunctivity of Q nor constructs a counterexample to Gottschalk's
conjecture.
