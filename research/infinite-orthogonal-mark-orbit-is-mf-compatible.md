---
rg: 2
id: infinite-orthogonal-mark-orbit-is-mf-compatible
kind: claim
title: An infinite orthogonal orbit of a torsion normal generator is compatible with MF
distinct_from:
  orthogonal-root-self-copy-is-mf-compatible: that uses two commuting finitary elementary-group copies and root normal generation; this uses the actual nontrivial spectral projection of one finite-order normal generator and gives it infinitely many pairwise orthogonal conjugates in one faithful norm-corona representation.
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that proves the orbit statement for every surviving nontrivial binary-Leavitt root character; this gives a locally finite countermodel to the inference from that orbit statement and normal generation to MF invisibility.
  norm-corona-locally-finite-compression-countermodel: that preserves a Pauli compression defect under a one-sided tensor shift; this is a direct marked spectral-orbit model with no compressor or relative commutant.
  one-seed-infinite-character-expansion-collapses-mark: that assumes a uniform nonamenable Schreier gap and a Pauli seed on the entire nontrivial character sector; the finitary alternating orbit here is locally finite and has no such expansion input.
artifacts:
  - research/finitary-alternating-mark-orbit-mf-proof.md
---

**ESTABLISHED CALIBRATION.**  Let

```text
A_fin=union_(n>=5) A_n
```

under the standard inclusions fixing all new letters, and put

```text
w=(1 2)(3 4).
```

Then `A_fin` is locally finite and hence operator-MF, while `w` is an
involution which normally generates `A_fin`.  Moreover there is a faithful
homomorphism

```text
rho:A_fin -> U(product_n M_n(C)/directSum_norm M_n(C))             (IOM1)
```

such that the nontrivial spectral projection

```text
p=(1-rho(w))/2                                                     (IOM2)
```

has infinitely many pairwise orthogonal unitary conjugates by elements of
`rho(A_fin)`.  The coordinate projections representing each conjugate have
eventual rank two.

Consequently the following implication is false, even for a simple locally
finite group and inside the literal norm matrix corona:

```text
finite-order normal generator
+ infinitely many orthogonal conjugates of its marked spectral atom
=> marked element belongs to the MF radical.                       (IOM3)
```

In particular, combining
`surviving-leavitt-corona-character-has-infinite-parabolic-orbit` with normal
generation of the marked binary-Leavitt root does not establish
`binary-leavitt-atomic-morita-return`.  Orthogonal outward packing gives
arbitrarily many copies of `p` below the ambient unit, but it gives no copy
of `p+p` below `p`.  The load-bearing extra datum must be an authenticated
**return to the same atom**, not merely infinitude, simplicity, or normal
generation of the outward orbit.

Indeed the corner in `(IOM2)` is represented by rank-two matrix corners.
The Atomic Leavitt Gap therefore prevents any four operators in those
corners from satisfying the two inverse rows and the completeness row with
defect tending to zero.  Thus this faithful MF model simultaneously has the
strongest possible orthogonal conjugacy packing and fails the terminal AMR
conclusion on the marked atom.

No Property `(T)`, trace-density hypothesis, stability input, or literature
theorem is used.

DERIVATION
finitary-alternating-mark-orbit-mf-proof
