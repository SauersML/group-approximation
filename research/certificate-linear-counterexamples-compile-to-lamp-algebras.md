---
rg: 2
id: certificate-linear-counterexamples-compile-to-lamp-algebras
kind: claim
title: A full-shift counterexample with certificate-controlled linear data yields a prime-field group-algebra inverse pair
distinct_from:
  certificate-controlled-routing-is-surjunctive: that excludes pure routing; this compiles arbitrary certificate-controlled linear mixing and does not exclude it.
  certificate-linear-automata-have-local-linear-decoders: that constructs a decoder in a family of nonuniform operators; this realizes the entire family as matrices in an ordinary group algebra.
  stable-finiteness-failure-refutes-surjunctivity: that passes from group algebra to dynamics; this passes from a specified nonlinear full-shift class to group algebra after enlarging the group.
  kun-thom-wreath-stably-finite: that now proves finiteness for the residually finite-base permutational wreath family; this gives a conditional counterexample reduction using regular finite-abelian wreath products over an arbitrary base group.
---

Let p be prime, B a nonempty finite certificate alphabet, and G any group.
Suppose the cellular automaton

    E(x,c)=(T_c x,c) on ((F_p)^n x B)^G

is injective and nonsurjective, where each T_c is linear in x and its
coefficients depend locally on c. Then there is an explicitly specified
finite abelian group L and matrices A,B_0 over F_p[W], W=L wr G, with

    B_0 A=I,        A B_0!=I.

One may choose:

* p odd: L=(C_2)^a with 2^a>=|B|, and matrix size n;
* p=2: L=(C_3)^a with 3^a>=|B|, and matrix size 2n.

Here a>=1 may be any integer satisfying the bound, and wr means the
restricted regular wreath product (direct_sum_G L) semidirect G.
Thus F_p[W] fails stable finiteness and W is nonsurjunctive.
The source E already makes G nonsurjunctive; no failure of stable finiteness
of F_p[G] itself is claimed.

More precisely, put R_B=C_lc(B^G,F_p) semidirect G, with algebraic crossed
product multiplication. It is stably finite if and only if every such
injective E, over all finite data dimensions, is surjective. The forward
inverse and its nonzero reverse defect embed faithfully into the displayed
lamp group algebra, with restriction of scalars in characteristic two.

Affine data offsets and a reversible certificate update independent of the
data do not enlarge this class for purposes of the reduction: compose with
their local inverse transformations to reach the displayed form.

This is an exact translation, not an existence proof for E. It permits
arbitrarily complicated finite certificate predicates and genuine sums of
multiple data values, but does not cover a certificate update depending on
the data or general nonlinear dependence on the data. Restricting the
certificate to valid histories in a proper subshift is also insufficient.

The Fourier realization is standard; compare Ara--Claramunt,
*Approximating the group algebra of the lamplighter by infinite matrix
products*, Proposition 5.8, https://arxiv.org/abs/2005.12374. The route
gives the finite-field construction explicitly for the group and alphabet
needed here.

## Attempts to extend the source class

`boolean-secants-do-not-supply-operator-left-inverses` excludes the direct
telescoping-difference extension to arbitrary Boolean automata. Comparing
two executions yields a matrix that transports their particular
disagreement. Even for a reversible gate that matrix can be singular on
other vectors. The resulting certificate-linear family therefore need
not satisfy the injectivity hypothesis used here. A different nonlinear
compiler would have to establish that hypothesis separately.

`injective-automata-have-local-stable-secant-dilations` gives local
invertible block operators for every nonlinear inverse pair over a
finite-field alphabet, after adding an auxiliary data track. The full
compiled family is always reversible. Restricting it to the entire
zero-auxiliary data subspace requires QP=I for every certificate, and
a strict restriction additionally requires PQ!=I for some certificate.
The construction only clears the auxiliary component on genuine
execution differences, so it does not yet supply those hypotheses.

`output-secants-with-local-sections-force-matrix-defects` removes the
separate defect-preservation requirement by changing to arbitrary output
pairs as certificates. A missing output b and its retraction tau sigma(b)
are distinct but have the same decoder value, so their secant has an
explicit nonzero kernel vector. A local right inverse of the entire
secant family would then yield QP=I and PQ!=I. That right inverse may
initially be nonlinear: `nonlinear-local-sections-of-linear-families-linearize`
extracts a linear one with the same memory. Existence of such a local
right inverse remains the unproved step.
