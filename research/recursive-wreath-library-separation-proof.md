---
rg: 2
id: recursive-wreath-library-separation-proof
kind: route
title: Control finite products at each wreath depth and separate a finite support at one residual stage
target: recursive-wreath-libraries-have-stably-finite-group-algebras
requires:
  - wreath-finiteness-transfers-from-product-closed-classes
---

## Keep product closure as part of the induction

Each C_(n+1) is closed under subgroups and finite direct products by its
definition. Also C_n subset C_(n+1): any G in C_n is the wreath product
1 wr_X G, for instance with X a singleton. C_0 has the required subgroup
and product closure.

Fix k. We prove stable finiteness of k[H] for all H in C_n by induction
on n. The base is residual finiteness: any nonzero finite inverse defect
survives in a finite quotient group algebra, where a one-sided inverse
is two-sided by finite-dimensional linear algebra.

Suppose the conclusion holds on C_n. The product-class transfer theorem
makes k[A wr_X G] stably finite for A,G in C_n. To pass to C_(n+1) we
must also handle finite products of such wreath groups; we do not assume
that stable finiteness passes to arbitrary tensor products of algebras.

Let W_i=A_i wr_(X_i) G_i, i=1,...,m, with all A_i,G_i in C_n. Put

    A=product_i A_i,    G=product_i G_i,    X=disjoint_union_i X_i,

where G acts on the i-th site component through its G_i factor. There is
an injective homomorphism

    product_i W_i -> A wr_X G.

At a site in X_i, insert its A_i lamp into the i-th coordinate of A and
put all other coordinates equal to the identity; the base tuple maps
identically to G. This preserves products and the action, and both kernel
and base coordinates show injectivity. Since A,G belong to C_n, the target
group algebra is stably finite by the transfer theorem. The source group
algebra and those of its subgroups are unital subrings, hence stably finite.
This completes the induction. Increasingness and finite maximum depth
give the stated closure properties of C_fin.

## Residual separation is enough for finite group-algebra supports

Let H be residually C_fin and suppose B A=I over k[H] but D=I-A B!=0.
Let F be the finite union of the supports of the entries of D. For every
pair of distinct f,f' in F choose a homomorphism to a C_fin group that
separates f^(-1)f' from 1. Their finite product is a homomorphism H->K
with K in C_fin that is injective on F. If F has at most one element,
the map to the trivial group already preserves the nonzero coefficient
in that one-point support.

The image of D is nonzero, while B A=I still holds. This contradicts
stable finiteness of k[K]. Therefore k[H] is stably finite.

Projection to a coordinate separates a nonidentity element of a subgroup
of a direct product. Inverse limits, viewed as groups, are subgroups of
the product of their stage groups. This proves the stated consequences.
No passage from a proper quotient back to a group is used.

## Directed colimits also preserve the conclusion

Let H be a directed colimit of groups H_i in C_fin, with structure maps
not necessarily injective. The finitely many group elements and
coefficients of a proposed matrix pair B A=I over k[H] lift to a common
stage. The finitely many equalities needed to cancel the coefficients
of B A-I in the colimit hold at some common later stage: an equality of
two elements in a directed group colimit is witnessed at a later stage,
and only finitely many product terms occur. Thus the lifted pair has
B A=I at that stage. Its group algebra is stably finite, so A B=I there,
and this equality maps to the colimit. This proves the colimit assertion.

## Infinite tree depth with finite activity at each level

Let the vertices at depth n be the words in X_0 x ... x X_(n-1).
At a vertex of depth i the allowed local permutation is in G_i.
Local permutations determine a tree automorphism; finiteness of the set
of nonidentity labels at each level is preserved under products and
inverses because automorphisms permute each level.

At finite depth n, this group acts through a finite iterated restricted
permutational wreath product of G_0,...,G_(n-1). To see restriction of the
wreath product, observe that only finitely many first-level subtrees can
contain an active label among the first n levels: it is a finite union
of finite sets. Within each such subtree apply the same argument one
level lower. Thus its finite-depth image is a subgroup of a member of
C_fin. This remains true even when a level has infinitely many vertices.

A nonidentity tree automorphism moves some finite word, and its action is
therefore detected at finite depth. The whole group is residually C_fin,
so the preceding result proves stable finiteness of its group algebra.
There is no bound on how deep a detecting truncation must be. The proof
uses its existence for each finite support, which is the precise
faithfulness hypothesis that an abstract self-referential presentation
must supply before this argument applies.
