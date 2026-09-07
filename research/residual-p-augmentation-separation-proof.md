---
rg: 2
id: residual-p-augmentation-separation-proof
kind: route
title: Separate augmentation powers by finite p-group quotients and annihilate the inverse defect
target: residually-p-kernels-preserve-modular-stable-finiteness
requires: []
---

## Separated ideals cannot contain a nonzero inverse defect

Let R be unital and J a two-sided ideal with intersection_m J^m=0.
Suppose R/J is stably finite and B A=I_n over R. Reduction modulo J
gives A B=I_n modulo J, so D=I_n-A B lies in M_n(J). Also

    D^2=I_n-2 A B+A(BA)B=I_n-A B=D.

Therefore D=D^m belongs to M_n(J^m) for every m, and entrywise separation
gives D=0. This proves stable finiteness. Taking n=1 proves the analogous
direct-finiteness implication. No inverse for a general element 1+j is
constructed or needed.

## The augmentation ideal of a residually finite p-group is separated

Put I=ker(k[N]->k). For any nonzero u in k[N], its support is finite.
Residual p-finiteness supplies a homomorphism N->P into a finite p-group
that is injective on this support: separate all pairwise differences by
finitely many p-group quotients and take their product. Consequently the
image of u in k[P] is nonzero.

The augmentation ideal of k[P] is nilpotent in characteristic p. Here is
the standard short proof. A nontrivial finite p-group has a central element
z of order p. In k[P], the central ideal K=(z-1)k[P] has K^p=0, and
k[P]/K=k[P/<z>]. By induction on |P|, some power I_P^m lies in K;
then I_P^(mp)=(I_P^m)^p lies in K^p=0. The trivial group starts induction.

If u belonged to every I^m, its image in every k[P] would belong to every
I_P^m and hence be zero, contradicting the separated support. Thus

    intersection_(m>=1) I^m=0.                           (RPA1)

This is an algebraic separation argument, not a claim that the finite
p-group quotients of N extend to quotients of W.

## Pass from the normal subgroup to the whole extension

In R=k[W], let J=I k[W]. Normality of N makes I and all its powers
invariant under conjugation by W. Therefore J is two-sided and

    J^m=I^m k[W],          R/J ~= k[G].                  (RPA2)

Choose any transversal t_g for N in W. As a left k[N]-module,

    k[W]=direct_sum_(g in G) k[N] t_g,
    I^m k[W]=direct_sum_(g in G) I^m t_g.

Each ring element has finitely many such coefficients. Equation (RPA1)
therefore implies intersection_m J^m=0. The first part applies to (RPA2)
and proves the extension theorem, including nonsplit extensions.

For N=direct_sum_X P with P finite of p-power order, projection onto any
finite set of factors is a finite p-group quotient. Such projections
separate elements, so N is residually a finite p-group. In the split wreath
product, k[G] is also a unital subring of k[W]. Since direct and stable
finiteness pass to unital subrings, the asserted equivalence follows.
