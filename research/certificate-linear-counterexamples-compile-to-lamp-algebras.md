---
rg: 2
id: certificate-linear-counterexamples-compile-to-lamp-algebras
kind: claim
title: A certificate-controlled linear full-shift counterexample already yields an inverse defect over the original group algebra
distinct_from:
  certificate-controlled-routing-is-surjunctive: that excludes pure routing; this compiles arbitrary certificate-controlled linear mixing and does not exclude it.
  certificate-linear-automata-have-local-linear-decoders: that constructs a decoder in a family of nonuniform operators; this realizes the entire family as matrices in an ordinary group algebra.
  stable-finiteness-failure-refutes-surjunctivity: that passes from group algebra to dynamics; this passes from a specified certificate-controlled class back to the original group algebra by constant evaluation.
  kun-thom-wreath-stably-finite: that now proves finiteness for the residually finite-base permutational wreath family; this gives a conditional counterexample reduction using regular finite-abelian wreath products over an arbitrary base group.
---

Let p be prime, B a nonempty finite certificate alphabet, and G any group.
Suppose the cellular automaton

    E(x,c)=(T_c x,c) on ((F_p)^n x B)^G

is injective and nonsurjective, where each T_c is linear in x and its
coefficients depend locally on c. Then for every constant certificate
c_b there are n-by-n matrices A_b,B_b over F_p[G] with

    B_b A_b=I,        A_b B_b!=I.

They are obtained by evaluating the original local coefficients and
those of a local linear decoder at c_b. Thus F_p[G] itself fails stable
finiteness, with no enlargement of the group or the data matrix size.
Every fiber of E is injective and nonsurjective.

There is also a faithful finite-lamp realization of the entire
certificate-dependent algebra, retaining all coefficients rather than
evaluating them. For W=L wr G one may choose:

* p odd: L=(C_2)^a with 2^a>=|B|, and matrix size n;
* p=2: L=(C_3)^a with 3^a>=|B|, and matrix size 2n.

Here a>=1 may be any integer satisfying the bound, and wr means the
restricted regular wreath product (direct_sum_G L) semidirect G.
This additionally gives failure of stable finiteness for F_p[W]. The
stronger original-group conclusion follows from
`one-invertible-certificate-fiber-forces-global-invertibility`.

More precisely, put R_B=C_lc(B^G,F_p) semidirect G, with algebraic crossed
product multiplication. It is stably finite if and only if F_p[G] is
stably finite, equivalently if every such injective E, over all finite
data dimensions, is surjective. Constant evaluation need not preserve
arbitrary nonzero elements, but it preserves every nonzero reverse defect
of a one-sided inverse pair.

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
