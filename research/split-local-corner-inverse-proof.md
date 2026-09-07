---
rg: 2
id: split-local-corner-inverse-proof
kind: route
title: Lift the quotient unit and reduce its perturbation to one finite corner
target: split-local-corner-extensions-preserve-stable-finiteness
requires: []
---

Suppose B A=I_n over R. In S the image Abar is invertible, because S is
stably finite. The section lifts it to the invertible matrix
A_0=s_n(Abar) with inverse s_n(Bbar). Thus

    C=A_0^(-1) A=I_n+i,    i in M_n(I),
    D=B A_0,              D C=I_n.

Choose a local unit e in I for all entries of i, and put E=diag(e,...,e).
Then Ei=iE=i, so C is block diagonal relative to E:

    C=(I_n-E)+(E+i).

From D C=I_n, multiplication by E on both sides gives

    (E D E)(E+i)=E.

The two factors belong to E M_n(I) E=M_n(e I e), a stably finite ring.
Consequently (E+i)(E D E)=E as well. It follows that

    C ((I_n-E)+E D E)=I_n.

A left inverse and a right inverse of the same element agree; hence
D=(I_n-E)+E D E and C D=I_n. Undoing the invertible A_0 gives A B=I_n.

For a direct sum of finite-support matrix algebras, take a finite sum of
diagonal matrix units covering all rows and columns that occur in a finite
set of elements. Its corner is a finite product of finite matrix rings
over the coefficient rings, and is stably finite. Such corners suffice for
the preceding argument. More generally any idempotent corner of a stably
finite ring is stably finite: add the complementary idempotent to each
factor of a one-sided inverse pair and use stable finiteness in the ambient
matrix ring.
