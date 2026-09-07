---
rg: 2
id: two-finite-subgroup-nesting-amalgam-proof
kind: route
title: Lift the two multiplication rectangles to a finite-group amalgam and separate the idempotents in a finite quotient
target: nested-two-finite-subgroup-idempotents-have-strict-rank
requires:
  - lifted-trace-detects-finite-subgroup-projectives
---

## The two rectangles retain all their equalities

Put L=H intersect K and Gamma=H *_L K. The inclusions of H and K
in G induce a homomorphism q:Gamma->G. This need not be injective
on Gamma, but it is injective on the product set HK in Gamma.
Indeed an equality h_1 k_1=h_2 k_2 in G implies

    h_2^(-1)h_1=k_2 k_1^(-1) in L,

and this same identification holds already in the amalgam. The reverse
implication holds because q is a homomorphism. The same argument works
for KH, separately. These sets include H union K because they contain
the identity factors.

Lift the coefficients of e and f to their copies of H and K in Gamma,
calling the resulting matrices E and F. Their idempotency holds in
the factors. Every entry of EF-F is supported in HK and every entry
of FE-F in KH. Injectivity on the respective rectangles therefore
gives EF=FE=F. Also E-F!=0, because q is injective on H union K.

## A finite quotient sees the strict inclusion

An amalgam of two finite groups over a common subgroup is residually
finite and virtually free. One standard reference is Lemma 5.2 of
the graph-of-finite-groups argument in
https://ems.press/content/serial-article-files/26328.
For this use, the usual proof can be summarized as follows. On a
finite set whose size is a common multiple of |H| and |K|, take free
H- and K-actions. Their restrictions to L are isomorphic free L-sets;
identifying them gives a finite permutation representation of Gamma
injective on both vertex groups. Its kernel acts freely on the
Bass--Serre tree and is a finite-index free group. Free groups are
residually finite, and taking the intersection of finitely many
conjugates of a finite-index normal subgroup in this free kernel
gives residual finiteness of Gamma.

Choose a finite quotient pi:Gamma->D injective on the finite set
H union K. This preserves E-F!=0, as well as injectivity of each
factor. Let E_D,F_D be the matrices over k[D]. They are nested
idempotents with nonzero difference. Their images on k[D]^n obey

    im(E_D)=im(F_D) direct_sum im(E_D-F_D).

The second summand is nonzero: the regular module action of a
nonzero matrix over k[D] is faithful. Thus rank_k(E_D)>rank_k(F_D).

As a left k[H]-module, k[D] is a direct sum of |D|/|H| regular
modules, using the right cosets of H. Since E_D acts by left
multiplication with entries in k[H],

    rank_k(E_D)=(|D|/|H|) dim_k(e k[H]^n).

Similarly rank_k(F_D)=(|D|/|K|) dim_k(f k[K]^n).
Dividing the strict rank inequality by |D| proves (TFR1), over any
field, including when its characteristic divides |D|. This is a
dimension calculation over k, not division inside k.

## Ambient projective equivalence is excluded in characteristic p

For k=F_p, the lifted-trace theorem identifies the two rational
numbers in (TFR1) with their Z_p-valued projective traces after
inducing to G. Their positive rational difference is nonzero in Q_p,
so the K_0 classes differ by an element of infinite additive order.
An arbitrary common projective stabilization cannot erase that
difference. In particular xy=e, yx=f would identify those classes
and is impossible. No finite quotient of G was assumed or constructed.

Finally, group conjugation carries a finite subgroup H isomorphically
onto uHu^(-1) and preserves the finite regular rank of e. The two
rational ranks in (TFR1) are consequently equal for e and ueu^(-1).
Strict nesting in either direction would contradict (TFR1).
