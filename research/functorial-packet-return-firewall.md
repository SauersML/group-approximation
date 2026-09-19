---
rg: 2
id: functorial-packet-return-firewall
kind: claim
title: Fixed tracially functorial packet compression cannot produce the trace-cyclic proper returns
distinct_from:
  universal-block-return-violates-the-regular-firewall: that rules out fixed group-algebra block identities; this also rules out deriving the blocks by fixed finite packet exactification, averaging, spectral cuts, polar decomposition, or conditional expectation whenever those operations are available in arbitrary finite tracial von Neumann algebras.
  fixed-d8-holonomy-has-no-determinant-density: that gives a finite-matrix remainder construction for fixed projective tests; this is the complementary regular-representation firewall for fixed analytic packet decoders.
---

Let `Gamma` be a group and let `H in M_r(C Gamma)` be a positive rational
group-algebra projection with

```text
(tr_r tensor tau_Gamma)(H)>0.                          (FFC1)
```

Suppose a proposed fixed actuator assigns to every exact tracial
representation `pi:Gamma->U(M)` block operators `E_pi,X_pi,Y_pi` by a
construction which is available in every finite tracial von Neumann
algebra and is natural under trace-preserving embeddings.  This includes
any fixed composition of:

- evaluation of finitely many prescribed group words and matrix algebra;
- averaging over a fixed finite packet group;
- spectral projections or continuous functional calculus;
- polar decomposition and support projections;
- conditional expectation onto a fixed finite-dimensional packet algebra
  or its commutant; and
- fixed matrix amplification and compression by projections obtained by
  the preceding operations.

Then the construction cannot satisfy, for every exact `pi`,

```text
tr(Y_pi X_pi)=tr(E_pi),
tr(X_pi Y_pi)=tr(E_pi-pi(H)).                          (FFC2)
```

Indeed apply it to the left regular representation in
`M_r(L(Gamma))`.  Every listed operation exists there and preserves the
normalized finite trace.  Cyclicity gives

```text
tr(Y_pi X_pi)=tr(X_pi Y_pi),
```

so `(FFC2)` forces `tr(pi(H))=0`, contradicting faithfulness and `(FFC1)`.

The same argument applies to the two-oriented and three-edge variants: if
the two proper-return scalar identities are obtained functorially in every
finite tracial von Neumann algebra, their cyclic ledger forces the positive
holonomy projection to have trace zero in the regular representation.

Thus fixed finite packet exactification does not by itself make a return
matrix-only.  Gowers--Hatami averaging, finite spectral rounding, Julia
unitaries, Steinberg block matrices, and fixed polar/support cuts are all
still meaningful in the regular finite von Neumann algebra.  The missing
step must use a genuinely matrix-coordinate operation not natural in a
II_1 algebra, such as an integer multiplicity matching or a rank choice
whose definition depends on finite matrix size.  The native prescribed
words must force that choice to lose positive **density**, rather than only
a bounded remainder.
