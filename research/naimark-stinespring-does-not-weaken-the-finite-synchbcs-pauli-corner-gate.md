---
rg: 2
id: naimark-stinespring-does-not-weaken-the-finite-synchbcs-pauli-corner-gate
kind: claim
title: Naimark and matrix-unit dilation do not weaken the finite SynchBCS Pauli-corner gate
distinct_from:
  perfect-qc-synchronous-separation-yields-a-finite-bcs-with-no-matrix-model: that supplies the finite SynchBCS algebra whose every trace is non-Connes-embeddable; this audits the proposed finite amplification, Naimark, Stinespring, inverse-semigroup, and Pauli crossed-product compilers.
  unitary-corner-compressions-force-reduction: that treats compressed unitaries; this proves the projection and full multiplicative-domain versions needed for PVMs and matrix-unit refinements.
  inverse-semigroup-globalization-cannot-groupify-nonru-bcs: that rules out one global inverse semigroup abstractly; this places the same obstruction inside the exact finite SynchBCS-to-Pauli dilation and couples it to the non-CE trace.
  finite-phase-pauli-basis-dilation-is-a-twisted-group-factor-compiler: that compiles a successful invariant-basis crossed product; this proves that the standard dilation devices cannot construct the required embedding for free.
---

Let `A_I` be the finite SynchBCS algebra supplied by
`perfect-qc-synchronous-separation-yields-a-finite-bcs-with-no-matrix-model`.
It has tracial states, but **every** tracial state on `A_I` is
non-Connes-embeddable.

Let

~~~text
B=L_omega(K) crossed_product_beta G
~~~

be a finite-phase Pauli-basis crossed product, let `n<infinity`, and let
`p in M_n(B)` be nonzero.  Any of the following exact constructions already
solves the group problem:

1. a unital star-homomorphism

   ~~~text
   Phi:A_I -> p M_n(B) p;                                (NSP1)
   ~~~

2. ambient Naimark projections whose compressions by `p` are the SynchBCS
   PVMs and satisfy all forbidden-overlap relations; or
3. an ambient matrix-unit/Stinespring refinement whose compression by `p`
   is multiplicative on `A_I`.

Indeed, if `P` and `p` are projections and `pPp` is a projection in the
corner, then

~~~text
pPp-(pPp)^2=pP(1-p)Pp,                                  (NSP2)
~~~

so positivity forces `[p,P]=0`.  More generally, if compression of a
star-representation is multiplicative on a subalgebra, the multiplicative
domain identity forces `p` to reduce that subalgebra.  Thus exact Naimark or
Stinespring dilation gives precisely (NSP1), not a weaker object.

Composing (NSP1) with the normalized canonical trace of the corner gives a
tracial state on `A_I`.  Its generated von Neumann algebra is a subalgebra
of `pM_n(B)p` and is non-CE.  Therefore `B` is non-CE.  The finite-phase
basis compiler then produces a countable nonhyperlinear finite central
extension of `K semidirect G`.  No injectivity of `Phi` and no advance choice
of the source trace are needed.

Consequently no hyperlinear/CE Pauli crossed product can host even a finite
amplified corner realization of the exact SynchBCS relations.  A claimed
Naimark construction inside such a host must fail by making at least one
compressed effect nonprojective, one forbidden atom nonzero, or the
compression nonmultiplicative.

A single inverse semigroup does not evade the conclusion.  Its source and
range projections are idempotents in one commuting semilattice.  If all
SynchBCS atoms are represented there, all question projections commute
globally and give a classical finite-dimensional model, which `A_I` does
not have.  Separate context inverse semigroups retain noncommuting cycle
holonomy; globalizing that holonomy into a Pauli crossed product is exactly
(NSP1).

Local matrix-unit refinement remains valid but terminal.  Each individual
finite predicate algebra embeds in a finite Pauli/signed-Hecke block, and
rational overlap multiplicities can be matched.  The missing common
reducing corner is the entire non-CE embedding problem; Naimark, finite
amplification, and matrix units do not manufacture it.

Thus the source-specific route is sharply reduced but **OPEN**: construct
(NSP1) directly in a genuinely non-CE Pauli crossed product, or find new
non-Cartan group-algebra elements whose multiplication already realizes the
SynchBCS algebra.  No nonhyperlinear group is claimed here.

DERIVATION
projection-compression-and-multiplicative-domain-close-the-synchbcs-dilation-shortcuts
