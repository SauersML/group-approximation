---
rg: 2
id: three-higman-bs-seams-vanish-fourth-is-product-holonomy
kind: claim
title: Three Higman BS seams vanish; the fourth is exactly a four-matcher product holonomy
artifacts:
  - research/artifacts/higman-bs-packet-product-holonomy-2026-08-21.md
distinct_from:
  split-higman-cycle-has-haar-marginals-and-maximal-role-gap: that uses the canonical common basis and leaves all four seams asymptotically maximal; this chooses optimal spectral gauges and makes any prescribed three consecutive seams vanish.
  one-product-holonomy-does-not-sew-four-bs-clocks: that adds one product word to four far split packets; this derives the actual necessary-and-sufficient product constraint for four vanishing operator seams.
  higman-hs-microstates-are-near-glued-exact-bs-cycles: that reduces Higman microstates to arbitrary exact BS packets with small seams; this classifies the packets and scalarizes the remaining obstruction for the periodic-clock family.
---

Every finite-dimensional exact `BS(1,2)` packet

```text
C D C^(-1)=D^2                                      (PH1)
```

has the following normal form.  The finite weighted spectrum of `D` is a
union of squaring orbits of roots of unity of odd order.  On one orbit

```text
lambda,lambda^2,...,lambda^(2^(m-1))
```

all eigenspaces have a common multiplicity `k`; `D` is diagonal on their
sum and `C` is the cyclic shift with an arbitrary `U(k)` wrap monodromy.
After diagonalizing the monodromy, the packet is an orthogonal sum of
multiplicity-one packets with scalar wrap phases.  This is the `n=2` form of
the periodic-solenoid classification.

Fix any exact packet `(P,D)` and four independently conjugated copies with
gauges `G_i`:

```text
C_i=G_i P G_i^*,       Z_(i+1)=G_i D G_i^*.
```

Put `H_i=G_(i-1)^* G_i`, with indices cyclically ordered.  Then the seam at
generator `i` is exactly

```text
||Z_i-C_i||_2=||D-H_i P H_i^*||_2,                  (PH2)
```

and the matcher increments satisfy

```text
H_1 H_2 H_3 H_0=I.                                  (PH3)
```

Conversely, any four unitaries satisfying `(PH3)` determine gauges and hence
an exact split BS cycle with seam errors `(PH2)`.  Thus, within one packet
type, the vanishing-seam problem is **exactly**:

```text
find four asymptotic spectral matchers P -> D
whose ordered product is I.                          (PH4)
```

Arbitrary multiplicity and monodromy enlarge the matcher sets through the
centralizers of `P` and `D`, but do not remove the product equation `(PH3)`.

There is a sharp three-seam escape.  For the periodic clocks `(P_q,D_q)` of
`periodic-bs-clock-defeats-spectral-first-hit-checksum`, choose primes so
both empirical spectral measures converge to Haar.  Optimal matching of
normal-matrix eigenvalues gives unitaries `H_q` with

```text
epsilon_q=||D_q-H_q P_q H_q^*||_2 ->0.               (PH5)
```

Take `G_i=H_q^i` for `i=0,1,2,3`.  The first three seams equal `epsilon_q`,
whereas the last satisfies

```text
seam_0 <= epsilon_q
          +||H_q^4 P_q H_q^(-4)-P_q||_2.             (PH6)
```

Every conjugator `C_i` is conjugate to `P_q`, so

```text
||C_i-I||_2^2=2-2/q ->2.                              (PH7)
```

Hence no dimension-free inequality using any three seams, the local packet
classification, or marginal spectral transport can collapse the Higman
mark.  The only remaining obstruction for this family is an **order-four
spectral matcher**: choose the four matchers separately with product one, or
in the homogeneous ansatz make `H_q^4` asymptotically centralize `P_q`.
Proving a constant lower bound for `(PH4)` would collapse this clock sector;
constructing such matchers would give a nontrivial vanishing-seam Higman
microstate family.

## Attempts

`folner-block-shifts-do-not-dilute-four-matcher-holonomy` tests the natural
long-path amplification.  A cyclic block shift does reduce the one-step
matcher wrap to `O(L^(-1/2))`, but its fourth power compares the four-step
gauge return on `L-4` interior blocks.  The residual converges to
`||S^4PS^(-4)-P||_2`, rather than zero.  With varying gauges, the ordered
product of each four consecutive matchers is tested at positive density.
Thus fixed four-generator folding cannot convert the holonomy into a single
Folner boundary defect.
