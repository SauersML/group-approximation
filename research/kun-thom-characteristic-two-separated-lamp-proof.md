---
rg: 2
id: kun-thom-characteristic-two-separated-lamp-proof
kind: route
title: Apply residual-two augmentation separation to the binary lamp kernel
target: kun-thom-binary-wreaths-stably-finite-in-characteristic-two
requires:
  - residually-p-kernels-preserve-modular-stable-finiteness
---

The kernel N=direct_sum_X C_2 is residually a finite two-group, by its
projections onto finite sets of coordinates. It remains to establish
stable finiteness of k[G] for a residually finite G; this has an elementary
proof over every field and does not need the general sofic theorem.

Suppose B A=I_n in M_n(k[G]) but D=I_n-A B!=0. Take the finite union of
the supports of the entries of D. Residual finiteness supplies a finite
quotient G->F injective on that set. The image D_F remains nonzero. But
M_n(k[F]) is a finite-dimensional k-algebra, hence directly finite:
left multiplication by elements of an inverse pair gives linear maps on
a finite-dimensional vector space, where a one-sided inverse is two-sided.
Thus B_F A_F=I_n forces D_F=0, a contradiction.

Apply residually-p-kernels-preserve-modular-stable-finiteness with p=2
to the extension 1->N->W->G->1. This proves the statement for every
characteristic-two field, not just F_2.

In this special case the separation is especially concrete. Put
y_x=a_x-1 for the binary lamp at x. Then

    k[N]=k[y_x:x in X]/(y_x^2:x in X),

with a basis of finite squarefree monomials. The G-action permutes these
variables and preserves total degree. The lamp augmentation ideal J in
k[W] consists of positive-degree terms, and J^m has degree at least m.
No nonzero finite sum can lie in every J^m. An inverse defect D lies in
J because it vanishes after setting all lamps equal to the identity;
idempotency forces it into all powers J^m and therefore makes it zero.

This is compatible with the existing witness u=y_x g for which 1-u is
not invertible. That witness shows J is not contained in the Jacobson
radical. It does not produce an idempotent in J and does not obstruct
the separated-powers proof.
