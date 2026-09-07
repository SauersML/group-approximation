---
rg: 2
id: output-secants-with-local-sections-force-matrix-defects
kind: claim
title: Output-pair certificates retain decoder collisions and turn local sections of their secants into strict matrix inverse pairs
distinct_from:
  injective-automata-have-local-stable-secant-dilations: that uses certified input differences and still needs a separate reverse defect; this uses arbitrary output pairs so a missing image point supplies that defect automatically.
  certificate-linear-counterexamples-compile-to-lamp-algebras: that assumes an injective nonsurjective certificate-linear encoder; this obtains one from a noninjective nonlinear decoder provided its secant family admits a local section.
  nonlinear-local-sections-of-linear-families-linearize: that extracts linear right inverses; this supplies a nonzero reverse defect from a collision of the original nonlinear map and compiles it into a finite-lamp group algebra.
---

Let p be prime, X=(F_p^n)^G for a group G, and let sigma:X->X be a
noninjective cellular automaton. Use the full certificate alphabet
B=F_p^n x F_p^n, so a certificate c is an arbitrary pair (a,b) in X^2.
Suppose Q_c is a certificate-local linear family satisfying

    Q_(a,b)(b-a)=sigma(b)-sigma(a) for all a,b.           (OSC1)

Such secant families always exist by finite telescoping of the local
rule. Suppose, in addition, that Q has a certificate-preserving local
right inverse, allowed to be nonlinear in its data:

    Q_c s_c(z)=z for every data z and every certificate c. (OSC2)

Then there are matrices P,Q over

    R_B=C_lc(B^G,F_p) semidirect G

with QP=I and PQ!=I. More precisely, if a!=b and sigma(a)=sigma(b),
the nonzero configuration d=b-a satisfies

    Q_(a,b)d=0,              (I-P_(a,b)Q_(a,b))d=d.      (OSC3)

More strongly, evaluating P,Q at any constant certificate gives the same
strict inverse identities in M_n(F_p[G]), by
`one-invertible-certificate-fiber-forces-global-invertibility`. The
original group algebra therefore fails stable finiteness, without a
change of group or matrix size.

The finite-lamp compiler also embeds the entire family into F_p[L wr G]:
one may take L=(C_2)^r with 2^r>=p^(2n) for odd p, and L=(C_3)^r with
3^r>=2^(2n) for p=2. Here r>=1; the matrix sizes are respectively n and
2n. Thus the displayed group algebra fails stable finiteness, and the
certificate-linear map (z,c)->(P_c z,c) is injective and nonsurjective
on the full shift over G.

For the intended Gottschalk route, start with sigma tau=id. If tau is
nonsurjective, choose b outside its image and put a=tau(sigma(b)). Then
a!=b and sigma(a)=sigma(b), giving the explicit witness (OSC3). Thus
using arbitrary output-pair certificates automatically preserves the
range defect of tau; it need not be imposed as another compiler axiom.

The unproved construction step is (OSC2). A nonlinear right inverse of
sigma itself is not a right inverse of its frozen-certificate linear
secants. The claim is a conditional reduction, not an existence proof
of any counterexample, and not a proof of a general equivalence between
Gottschalk and Kaplansky.

In particular, the canonical telescoping family need not satisfy (OSC2)
even when sigma is reversible: the three-bit example in
`boolean-secants-do-not-supply-operator-left-inverses` has a singular
secant. A surviving construction must choose different secants or another
representation; existence of local secants alone is insufficient.

There is a stronger restriction on any proposed replacement. It cannot
make Q invertible at even one certificate, including one with a=b.
An invertible fiber would force all fibers to be invertible, contradicting
(OSC3). Thus a diagonal normalization Q_(a,a)=I is incompatible with a
locally split family for a noninjective decoder. Its one-sided defect
must already survive in the constant-certificate operators over F_p[G].
