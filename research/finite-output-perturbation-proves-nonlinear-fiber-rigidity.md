---
rg: 2
id: finite-output-perturbation-proves-nonlinear-fiber-rigidity
kind: route
title: Count finite output fibers, then use local certificate dependence and compactness
target: nonlinear-certificate-fibers-are-all-surjective-or-all-strict
requires: []
---

The counting step appears in [Phung, proof of Theorem 9.1, pp. 15--16](https://arxiv.org/pdf/2201.13283).
That step does not require amenability; below it is followed by a
full-certificate compactness argument. No novelty claim is made.

## An injective finite-output perturbation of a surjection is bijective

Let J be any set, A a finite nonempty alphabet, and T:A^J->A^J a
surjection. Suppose S:A^J->A^J is injective and there is a finite set
F subset J such that

    S(x)|_(J minus F)=T(x)|_(J minus F) for every x.

Fix y_out in A^(J minus F). Its target fiber

    Y={y in A^J : y|_(J minus F)=y_out}

has exactly |A|^|F| elements. Put X=T^(-1)(Y). Surjectivity of T gives
|X|>=|Y|. The displayed agreement and injectivity of S give an injection
X->Y, so |X|<=|Y|. Hence both sets have equal finite cardinality and
S(X)=Y. Also T|_X is bijective. Varying y_out shows that S and T are
both bijective. No continuity or locality is required for this lemma.

## Finite certificate changes give finite output changes

Return to E(x,c)=(T_c(x),c). Its injectivity implies that each T_c is
injective. Choose a finite certificate memory D subset G so that
T_c(x)(g), with the data x fixed arbitrarily, depends on c only through
c|_(gD).

Suppose T_(c_*) is surjective for one c_* in B^G; it is then bijective.
If c differs from c_* only on a finite set K, an output coordinate g
can see a changed certificate only if gD meets K. Such g lie in the
finite set K D^(-1). Consequently

    T_c(x)(g)=T_(c_*)(x)(g)

for every data x and every g outside K D^(-1). Apply the counting
lemma to S=T_c and T=T_(c_*). This proves that T_c is surjective
for every finite modification c of c_*.

## Surjectivity extends from finite modifications to every certificate

Fix an arbitrary c in B^G and desired output y in A^G. For each finite
F subset G, choose c_F which agrees with c on F D and with c_* outside
F D. It is a finite modification of c_*, so T_(c_F) is onto. There is
therefore x_F with T_(c_F)(x_F)=y. Local dependence on certificates gives

    T_c(x_F)|_F=y|_F.

For each finite F, the set

    Z_F={x in A^G : T_c(x)|_F=y|_F}

is nonempty and closed: the output on F depends on finitely many data
coordinates. Also Z_(F_1 union ... union F_m) is contained in the
intersection of Z_(F_1),...,Z_(F_m). Thus these closed sets have the
finite intersection property. Compactness of A^G yields an x in their
intersection, and T_c(x)=y. This works for arbitrary groups, with no
countability or sequence-of-certificates assumption.

This argument also proves directly that the set of certificates c for
which T_c is surjective is closed: any finite target pattern realizable
at arbitrarily close certificates is realizable at c, and compactness
then realizes the whole target configuration. Since finite modifications
of c_* are dense in B^G, the preceding conclusion is the corresponding
closedness argument written with explicit finite coordinate sets.

## The dichotomy and the ordinary constant-fiber automata

We have shown that existence of one surjective fiber implies that all
fibers are surjective. If there is no such fiber, every T_c is injective
and nonsurjective. Because E keeps c unchanged, E is surjective exactly
when every T_c is surjective. This proves the stated dichotomy.

Equivariance of E gives

    T_(g.c)(g.x)=g.T_c(x).

A constant certificate c_b is fixed by every g, so T_(c_b) is
G-equivariant. It has finite data memory by the local rule of E, and
therefore is an ordinary cellular automaton on A^G. In the strict case
the dichotomy makes every one of these ordinary automata injective and
nonsurjective. No analogous equivariance is claimed for a general
nonconstant certificate.

## Autonomous certificate updates

Suppose E(x,c)=(T_c(x),chi(c)), with chi a reversible cellular automaton
on B^G. Composing E with the reversible map (y,d)->(y,chi^(-1)(d))
gives (T_c(x),c). This preserves injectivity and surjectivity and proves
the asserted extension, including the strictness of every constant data
fiber when E is strict.

For the stronger stated corollary, assume only that chi is surjective,
E is injective, and one T_c is surjective. Every T_c is injective because
inputs sharing the same certificate have the same output certificate.
Thus the map E'(x,c)=(T_c(x),c) is an injective cellular automaton, and
the theorem makes every T_c bijective.

If chi(c_1)=chi(c_2), choose any y in A^G and take x_i with
T_(c_i)(x_i)=y for i=1,2. Then E(x_1,c_1)=E(x_2,c_2); injectivity
forces c_1=c_2. Hence chi is injective as well as surjective. Given any
(y,d), choose c with chi(c)=d and then x with T_c(x)=y. This proves
surjectivity of E, and E is therefore bijective. No claim is made here
for arbitrary certificate updates depending on the data.
