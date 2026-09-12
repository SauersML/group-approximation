---
rg: 2
id: quadratic-redundant-check-overlay-gives-uniform-face-gap
kind: claim
title: Pairwise redundant parity checks abelianize the face group with a uniform gap
distinct_from:
  quadratic-repetition-supports-complete-commutation-overlay: that adds an explicit two-coordinate commutation face for each logical coordinate pair; this uses only bounded-width redundant parity checks and derives all-pairs commutation from them
  complete-overlay-code-group-has-uniform-conjugation-gap: that computes the coordinate-generator gap after all commutations are present; this constructs a bounded-occurrence parity-face presentation and transfers that gap to its whole-face pinchings
  tanner-separated-codewords-create-dihedral-soft-mode: that identifies disconnected codeword support as a dihedral obstruction; this overlay connects every nonzero support and excludes the obstruction
---

Let a binary code `C<=F_2^L` have a parity-check matrix with `M=Theta(L)`
distinct nonzero rows `(h_a)_(a in A)`, row weight at most `q`, and every
column occurring between `1` and `D` times.  Assume `C` has relative distance
at least `delta>0`.  In addition to every original parity face `h_a`, add
for every unordered pair `a!=b` the redundant parity face

```text
h_(a,b)=h_a+h_b.                                         (QRF1)
```

Its width is at most `2q`; it does not change the scalar kernel.

The homogeneous face group of this augmented presentation is exactly the
finite abelian code-dual group.  In particular, every nonzero codeword has
connected support in the augmented Tanner hypergraph, and the dihedral soft
mode is absent.

More quantitatively, let `Phi_f` be the pinching onto the commutant of the
exact joint PVM for augmented face `f`, and let

```text
H_F=(1/|F|) sum_(f in F) (I-Phi_f).                       (QRF2)
```

For every exact finite-dimensional representation of all augmented faces,
with generated algebra `N`, there is a constant
`gamma=gamma(delta,q,D,M/L)>0`, independent of `L` and matrix dimension,
such that

```text
<X,H_F X> >= gamma ||X-E_(N')(X)||_2^2.                  (QRF3)
```

Thus the augmented repeated-good-LDPC construction satisfies
`repeated-ldpc-adjoint-face-hamiltonian-gap`.

The overlay costs `Theta(M^2)=Theta(L^2)` bounded-width faces.  Each logical
coordinate occurs in `O(M)=O(L)` of them.  The existing repetition
`R=A L` therefore assigns their occurrences to private copies with bounded
degree after increasing the universal constant `A`.  Coordinate lists and
their empirical measures do not change, so the private mixed Weyl matching,
the exterior matching, code distance, and scalar LTC properties are all
preserved.
