# Alternating Reynolds averages contract every coefficient signal

Date: 2026-08-13

## Outcome

The canonical Pauli-orbit fingerprint does not bootstrap separate finite
packet recovery into simultaneous raw/comb coefficient alignment.  Exact
alternation of the two available conditional expectations fixes only the
scalar identity and contracts every centered coefficient direction by a
factor at most `19/64`.

Let `A` be the five-dimensional abelian algebra with atoms

```text
F_(--), F_(-+), F_(+-), F_(++), 1-q,
```

of traces `1/8,1/8,1/8,1/8,1/2`.  Let `P'` be the transported order-32
Pauli packet, let `E_(P')` be conjugation averaging over `P'`, and let `E_A`
be the trace-preserving expectation onto `A`.  In the displayed atom basis,
the restriction

```text
T=E_A E_(P') |_A
```

has the exact matrix

```text
1/256 *
[ 75  31  15  15 120 ]
[ 31  75  15  15 120 ]
[ 15  15  75  31 120 ]
[ 15  15  31  75 120 ]
[ 30  30  30  30 136 ].                              (ARC1)
```

The last row uses the different trace of `1-q`; `(ARC1)` is self-adjoint for
the trace-weighted inner product, as a conditional-expectation product must
be.

## Exact spectrum

The five eigenvalues and convenient eigenvectors are

```text
1       : ( 1, 1, 1, 1, 1),
19/64   : ( 1, 1,-1,-1, 0),
11/64   : ( 1,-1, 0, 0, 0),
11/64   : ( 0, 0, 1,-1, 0),
1/16    : ( 1, 1, 1, 1,-1).                           (ARC2)
```

The eigenvector matrix has determinant `-16`, so `(ARC2)` is the complete
spectrum.  In particular

```text
Fix(T)=C 1,
||T^n x||_2 <= (19/64)^n ||x||_2   for tau(x)=0.       (ARC3)
```

Equation `(ARC3)` is also the finite-dimensional alternating-projection
theorem in explicit coordinates: the raw coefficient algebra and the
transported Pauli fixed algebra have no common centered vector in this
packet.

The `11/64` gap found in
`TRUE_TRANSPORTED_PAULI_ORBIT_FINGERPRINT.md` is visible in `(ARC2)` as a
pair-difference eigenvalue.  It is a robust label for decoding a cut once a
simultaneous model is supplied, but iteration damps it geometrically.  It is
not an alignment seed.

## Consequence for the proof search

The following proposed route is closed:

```text
separately exactify raw and transported Pauli packets
  -> alternate their Reynolds expectations
  -> converge to a common nontrivial coefficient module.
```

It converges to scalars instead.  Amplification does not alter the five
eigenvalues, and convex direct sums cannot create eigenvalue one in a
centered mode.

This does not refute the desired simultaneous matrix-coordinate recovery
theorem.  It shows that such a theorem must use a genuinely nonfinite
cross-chart relation—such as a multiplication module or a relative
correspondence—and cannot be manufactured from the two finite packet
expectations alone.

## Certificates

`experiments/atlas_coefficient_alternating_reynolds.py` computes `(ARC1)`
from exact binary Leavitt-prefix elements and rational group-algebra traces.
Its checked output is
`experiments/atlas-coefficient-alternating-reynolds.json`.

`GroupApproximation/Sofic/CoefficientAlternatingReynolds.lean` verifies the
exact rational diagonalization, determinant, and strict spectral bound.
Both checks were run on MSI; no local code was run.
