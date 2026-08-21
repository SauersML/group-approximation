---
rg: 2
id: bounded-template-average-blr-occurrence-decoder
kind: claim
title: Recover average dense BLR energy from bounded-template occurrences
distinct_from:
  bounded-template-all-pairs-additive-decoder: that asks for an all-pairs almost-action; polar BLR self-correction now reduces it to this strictly weaker average-energy interface.
---

OPEN.  Construct a bounded-degree, bounded-template, perfect-completeness
same-basis occurrence test whose defect `epsilon` decodes, on one common
positive-mass carrier, a unitary table `f:F_2^n->U(d)` satisfying

```text
E_(x,y)||f(x)f(y)-f(x+y)||_2^2 <=omega(epsilon),              (BTA1)
```

with `omega(epsilon)->0` independent of `n,d`.  Average change from the tested
occurrences to the decoded table must obey the same kind of modulus.  No
pointwise or maximum-over-pairs conclusion is required.

The remaining issue is incidence/noncontextual agreement, not finite-group
stability: `unitary-blr-average-self-corrects-uniformly` upgrades `(BTA1)` to
the uniform almost-action required downstream, and abelian HS stability then
rounds in the same dimension.

## Minimal metapixel

It is enough to construct a family of bounded-degree constant-arity
constraint complexes `T_n` with distinguished binary coordinates indexed by
`F_2^n` such that:

1. their exact classical coordinate tables are precisely the affine/simplex
   tables (auxiliary proof coordinates are allowed);
2. every near-perfect tracial reflection strategy decodes on the same Hilbert
   space to one coordinate table satisfying `(BTA1)` in average normalized HS
   norm;
3. the decoder is noncontextual: it does not connect all occurrences of a
   coordinate by an equality fiber; and
4. the local constraint and answer alphabets, coordinate incidence, and
   soundness modulus are independent of `n`.

This is an operator-valued LTC/PCP of proximity for the binary simplex code.
Classical syndrome expansion alone is insufficient because a sparse binary
parity system can have nonclassical reflection representations of its solution
group.

## Published-test audit

- Natarajan--Vidick's quantum low-degree test does give a single global
  same-Hilbert low-degree measurement, but its robust parameter contains the
  growing `poly(d/q)` term.  Keeping it uniform requires a growing field and
  growing plane-answer packets, while its point--plane incidence has abundant
  rectangles.  See [Low-degree testing for quantum states](https://arxiv.org/abs/1801.03821).
- Ji--Natarajan--Vidick--Wright--Yuen's quantum tensor-code soundness theorem
  also constructs one global codeword measurement.  For a fixed base code,
  however, a point belongs to one axis line in each of the `m` tensor
  directions, so incidence grows with `m`, and the theorem's error is
  `poly(m,t)` times the test errors.  Growing the base length to compensate
  grows the line-answer packet.  See [Quantum soundness of testing tensor
  codes](https://people.eecs.berkeley.edu/~jswright/papers/tensor-codes.pdf),
  Theorems 1.2/4.1 and Lemmas 4.2--4.4.
- The bounded-degree left--right-Cayley constructions of Dinur--Evra--Livne--
  Lubotzky--Mozes are genuine classical constant-locality LTCs, but their
  theorem controls classical Hamming distance to a code.  It does not provide
  the noncontextual same-Hilbert measurement decoder required for arbitrary
  tracial reflection strategies.  See [Locally Testable Codes with Constant
  Rate, Distance, and Locality](https://arxiv.org/abs/2111.04808).
- The Pauli braiding test has robustness independent of the number of qubits,
  but its product test samples the complete pair distribution on
  `{0,1}^m`, and one question asks for an `m`-bit answer.  Thus it supplies
  operator soundness but neither bounded incidence nor a fixed answer
  template.  See Appendix A.4 of [Verifier-on-a-Leash](https://theoryofcomputing.org/articles/v020a003/v020a003.pdf).

No cited theorem simultaneously has all four properties of the minimal
metapixel above.

The most direct two-copy attempt is also false.  Testing a constant-size
local codeword PVM at each vertex of an expander and checking endpoint
agreement on the shared coordinate does not force one global commuting PVM.
`two-copy-overlap-consistency-has-pauli-cycle-countermodel` puts Pauli `X`
and `Z` on two macroscopic disjoint cycle sectors: every local even-parity
view is commuting and every overlap agrees exactly, but many distant
coordinates anticommute.  Therefore the higher-arity object needs, at a
minimum, robust expansion of the exterior-square/local-rank-two obstruction
in addition to classical agreement expansion.  Precisely,
`local-exterior-square-kernel-yields-pauli-strategy` proves that the local
restriction map must robustly detect every decomposable `u wedge v` of the
classical global section space; otherwise a one-qubit Pauli labeling is an
exact or asymptotically perfect counterstrategy.

That necessary first layer is achievable without densifying the template.
`expander-edge-overlay-detects-simplex-exterior-square` overlays a
constant-degree spectral expander on the simplex coordinates and uses an
unrestricted two-coordinate joint-PVM view on each edge.  Balanced affine
fibers give the uniform inequality `D <= (8/5)L_G`; the overlay has no
equality clouds, and two edge contexts never share two coordinates.  Thus the
Pauli-cycle countermodel does not prove an impossibility for simplex sections.
The remaining gap is ordered correctly: decode arbitrary operator local views
to global simplex sections while preserving the edge commutation energy.

## Attempts

- A direct candidate is a bounded-degree subset of the projective-line BLR
  checks `{x,y,x+y}` whose parity-check kernel is the binary simplex code and
  whose syndrome expands distance to that code.  Scalar LDPC soundness is not
  enough: arbitrary reflection solutions form the nonabelian solution group
  of the sparse parity system, so an operator/noncontextual soundness theorem
  is still required.
- A single cyclic orbit of line checks can have constant incidence, but its
  constraint graph is a bounded-generator Cayley graph of a cyclic group.
  Such graphs have spectral gap tending to zero, so they cannot yield the
  required uniform syndrome/agreement modulus.
- Dense BLR plus equality fibers controls an average representative, but a
  fixed mixed-test port can be corrupted at cost `O(1/m)` in a fiber of size
  `m`.  Sampling the mixed edge uniformly over the fiber requires many lifts
  of the same logical pair, recreating the two-pair contour.  This quantitative
  rooted-port obstruction is recorded in the parent decoder claim.
