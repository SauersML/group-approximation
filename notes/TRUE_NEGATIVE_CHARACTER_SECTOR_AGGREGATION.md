# Aggregate every negative root character before applying the Leavitt floor

Date: 2026-08-14

## 1. Outcome

The growing Heisenberg/radical-quotient route does not need to select one
central character of positive mass.  Individual character sectors shrink as
the finite root window grows, but their canonical negative-phase sum always
has trace one half.

Let `A` be a finite elementary abelian `2`-group containing a distinguished
nonzero element `1_A`, and let `u(1_A)` denote its unitary in a
regular-character matrix model.  For every additive character
`ell:A->F_2`, let `p_ell` be the corresponding spectral projection.  Then

```text
(1-u(1_A))/2 = sum_(ell(1_A)=1) p_ell.               (NCA1)
```

The regular trace gives

```text
tau(p_ell)=1/|A|,
tau((1-u(1_A))/2)=1/2.                               (NCA2)
```

Thus the mass of one `p_ell` tends to zero when `|A|` grows, while the union
of all phases relevant to the Leavitt pairing remains fixed at `1/2`.

In a trace-preserving normalized-HS microstate, exactification of the fixed
involution `u(1_A)` gives the same conclusion asymptotically.  Exactifying a
whole finite root window gives the individual character PVM and `(NCA1)`
coordinatewise.

## 2. Direct-sum decoder

For every `ell` with `ell(1_A)=1`, suppose a finite-multiplicity construction
produces contractions

```text
T_(0,ell), S_(0,ell), T_(1,ell), S_(1,ell)
```

on one square coefficient space `K_ell`.  No equality of the dimensions
`dim K_ell` is required.  Form their orthogonal direct sums over all negative
characters:

```text
T_i=directSum_ell T_(i,ell),
S_i=directSum_ell S_(i,ell).                          (NCA3)
```

These are contractions on the one common negative-phase coefficient space.
Their three product defects are the corresponding block direct sums.  The
multiplicative Leavitt floor can therefore be applied **once to `(NCA3)`**:

```text
max {
  ||T_0 S_0-1||_2,
  ||T_1 S_1-1||_2,
  ||T_0 S_1||_2
} >=2-sqrt(3).                                      (NCA4)
```

Here the norm is normalized on the full direct sum, automatically weighting
each character by its multiplicity.  There is no union bound, minimum atom
mass, fixed-rank subsector, or choice of a preferred `ell`.

Returning to the ambient microstate norm, `(NCA2)` and the corner-rescaling
identity in `TRUE_POSITIVE_DENSITY_LEAVITT_DECODER_ENDGAME.md` give the fixed
floor

```text
(2-sqrt(3))/sqrt(2)                                  (NCA5)
```

whenever the decoded coefficient space fills the negative phase sector.  If
the decoder retains only a subprojection of it, only the total retained
trace—not the mass of any single character—has to be controlled.

## 3. Why the algebraic quotient is compatible with aggregation

For the binary Leavitt ring `R`, a character `ell` defines

```text
b_ell(a,b)=ell(ab).
```

Its right radical is stable under left multiplication and its left radical
is stable under right multiplication.  Hence the coefficient operations are
defined separately on each radical quotient; they do not require identifying
two distinct characters.  The relations

```text
t_i s_j=delta_ij
```

hold blockwise once those quotient operations have been recovered.  Taking
their direct sum therefore preserves exactly the three products in `(NCA4)`.

This does not solve the reverse-decoding problem.  A normalized-HS group
microstate supplies finite root-character PVMs and Weyl commutator pairings,
not automatically the quotient operators on the multiplicity spaces.  The
new point is that the decoder should be formulated **measurably over the
whole negative character PVM**, rather than as a selection theorem for one
large atom.

## 4. Revised growing-packet target

The useful target is now:

> **Aggregated radical-quotient decoder.**  On an increasing exactified root
> window, construct the four coefficient contractions block-diagonally over
> every character satisfying `ell(1)=1`, with total ambient product defects
> tending to zero and with retained total trace bounded below.

If the construction uses the whole negative sector, the trace bound is
already the exact `1/2` in `(NCA2)`.  The dimension-free contradiction is
then `(NCA5)`.

The fixed Pauli packet remains the smaller coordinate system and should
still be tried first.  But its advantage is fixed representation type and a
four-label coherence problem—not the absence of a density theorem.  The
growing Heisenberg route has its own canonical positive-density aggregation.

## 5. Formal support

The local product floor is formalized in
`GroupApproximation/Sofic/LeavittTraceFloor.lean`.  The exact character
pairing and infinite-rank quotient argument are recorded in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md`, while the
finite-orbit theorem is kernel-represented in
`GroupApproximation/Leavitt/FiniteDualOrbit.lean`.  The present note isolates
the direct-sum/trace bookkeeping; it does not claim the missing aggregated
decoder and no build or computation was run.
