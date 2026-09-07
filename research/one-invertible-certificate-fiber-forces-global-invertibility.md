---
rg: 2
id: one-invertible-certificate-fiber-forces-global-invertibility
kind: claim
title: One invertible fiber of a locally split linear family forces every full-shift certificate fiber to be invertible
distinct_from:
  certificate-linear-automata-have-local-linear-decoders: that constructs a local left inverse; this proves that a globally split family cannot mix invertible and strictly one-sided fibers.
  certificate-linear-counterexamples-compile-to-lamp-algebras: that originally embedded inverse pairs into a larger lamp group; this shows every constant certificate already preserves the defect over the original group.
  injective-automata-have-local-stable-secant-dilations: that constructs a reversible auxiliary-track family; this concerns the actual unstabilized one-sided inverse pair and propagates its invertibility between certificates.
---

Let k be any field, B a finite nonempty alphabet, G any group, and
C=B^G. Suppose A_c,B_c are certificate-local k-linear operators on
(k^n)^G, with uniformly finite data and certificate memories, and

    B_c A_c=I for every c in C.

If A_(c_*) B_(c_*)=I for even one certificate c_*, then A_c B_c=I for
every c. The certificate c_* need not be constant, periodic, or generic.
Equivalently, a globally split family with a nonzero reverse defect
has that defect in every fiber.

Consequently, with R_C=C_lc(C,k) semidirect G, for each fixed n>=1,

    M_n(R_C) is directly finite iff M_n(k[G]) is directly finite.

In particular R_C is stably finite iff k[G] is stably finite. If matrices
B A=I, A B!=I occur over R_C, evaluating their coefficients at any
constant certificate preserves both identities over k[G], at the same
matrix size. This is a statement about one-sided inverse defects; it
does not assert that constant evaluation is injective on R_C.

Over a finite field, an injective certificate-preserving linear-data CA
is nonsurjective if and only if its restriction to any one constant
certificate is nonsurjective. In fact either every fiber is bijective
or every fiber is injective and nonsurjective. The local decoder theorem
supplies the globally split family needed here.

Applied to output-pair secants, a noninjective nonlinear decoder with
a locally split secant family therefore already gives a strict matrix
inverse pair over k[G]. Such a family cannot normalize even one diagonal
certificate to an invertible operator: the required algebraic defect
must survive there too, although the secant equation on that diagonal
has zero input difference.

The proof uses finite-rank perturbations and density of finite changes
to a certificate. It requires the full certificate shift. It makes no
claim for a proper subshift whose finite-change classes are not dense.

Related work studies finite perturbations of linear cellular automata;
see Phung, *Stable finiteness of twisted group rings and noisy linear
cellular automata*, https://arxiv.org/abs/2209.06002. The route gives the
specific full-certificate argument directly, without assuming a theorem
about arbitrary nonuniform systems or claiming novelty for the
finite-rank linear algebra.
