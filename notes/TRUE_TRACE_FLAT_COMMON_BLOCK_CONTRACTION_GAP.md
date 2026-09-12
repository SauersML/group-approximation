# Trace-flat common blocks cannot form a contraction

Date: 2026-08-14

## 1. Outcome

The exact `1/64` raw-to-comb block masses already proved in
`TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md` supply the amplitude missing from
the full-space Fourier contraction gap.  No unitary coefficient holonomy,
polar decomposition, or growing radical quotient is needed.

After normalizing the trace-half carrier, the four raw coefficient-character
cuts have trace `1/4`.  Choose equal-rank matrix units and write the comb
compression as an operator-valued matrix

```text
T=(T_ij)_(i,j in C_2^2) in M_4(N).                   (TCB1)
```

Because `T` is a compression of a group unitary, it is an operator-norm
contraction.  The exact ambient block mass `1/64` becomes

```text
||T_ij||_(2,N)^2=1/8                                 (TCB2)
```

for every one of the sixteen blocks.

Suppose the crossed-zero relation can be upgraded from block masses to
common-block coherence: after the fixed Fourier/Pauli phase correction,
there are `C_n in N_n` such that

```text
(1/4) sum_(i,j)||T_(ij,n)-C_n/2||_(2,N_n)^2 -> 0.    (TCB3)
```

Then no such contraction sequence exists.  This is the complete remaining
analytic endpoint for the fixed two-qubit packet.

## 2. Constant-block contraction gap

Let `N` be any finite tracial algebra, let `C in N`, and put

```text
K(C)=(1/2)J_4 tensor C in M_4(N).                    (TCB4)
```

If `p=(1/4)J_4 tensor 1` is the constant-label projection, then

```text
K(C)=2p(1 tensor C),
||K(C)||_2=||C||_2.                                  (TCB5)
```

For every contraction `T in M_4(N)`, right compression to `p` and the
reverse triangle inequality give

```text
||T-K(C)||_2
 >=||Tp-K(C)p||_2
 >=||C||_2-||Tp||_2
 >=||C||_2-1/2.                                     (TCB6)
```

Thus

```text
||T-K(C)||_2^2 >= max(0,||C||_2-1/2)^2.              (TCB7)
```

This is the `N=4` variable-coefficient form of the full-space Fourier gap.

## 3. Trace flatness forces the coefficient above the threshold

The normalized trace on `M_4(N)` gives

```text
||T-K(C)||_2^2
 =(1/4) sum_(i,j)||T_ij-C/2||_(2,N)^2.               (TCB8)
```

Hence `(TCB3)` is exactly `||T_n-K(C_n)||_2->0`, not a
dimension-dependent collection of pointwise estimates.

For any fixed block, the reverse triangle inequality and `(TCB2)--(TCB3)`
give asymptotically

```text
||C_n||_2/2 -> 1/sqrt(8),
||C_n||_2   -> 1/sqrt(2).                            (TCB9)
```

Equations `(TCB7)` and `(TCB9)` imply

```text
liminf ||T_n-K(C_n)||_2^2
 >=(1/sqrt(2)-1/2)^2
 =3/4-1/sqrt(2)>0,                                  (TCB10)
```

contradicting `(TCB3)`.

The same argument can use the averaged block norm instead of selecting one
block.  Because the family has only sixteen members, pointwise, summed, and
averaged convergence are equivalent without a growing-outcome loss.

## 4. Why this is stronger than the previous endpoint

The earlier reduced-Fourier route needed:

1. finite paired radical quotients of possibly growing rank;
2. diagonal relations to make the two coefficient arrows near-bijective;
3. deletion and invariance of the two trivial Fourier modes; and
4. a polar/contraction reduction followed by the `2-sqrt(3)` gap.

The fixed common-block route uses instead:

1. the already forced two-qubit Pauli factor;
2. the already proved four-by-four trace-flat block table; and
3. one total block-coherence estimate `(TCB3)`.

The first two items are exact and positive-density.  Only the third remains.
It is strictly stronger than equality of the sixteen block norms, but much
weaker than a classical whole-response-map law.

## 5. Reynolds form of the remaining gate

After a fixed Pauli phase untwist, the subspace of common-block matrices is
the fixed space for independent translations of the four row labels and the
four column labels.  Let `Lambda=C_2^2 times C_2^2` act on `M_4(N)` by those
row/column permutations and let

```text
E_Lambda(T)=|Lambda|^(-1) sum_(g in Lambda) g.T.      (TCB11)
```

Then `E_Lambda(T)` has all sixteen blocks equal.  Moreover, for this fixed
group, telescoping or the exact Reynolds energy identity turns small
translation defects into

```text
||T-E_Lambda(T)||_2->0.                              (TCB12)
```

Thus `(TCB3)` follows once finite-coordinate recovery provides the four
row/column translation operators and the raw/comb cross-root relations bound
their defects.  There is no Kazhdan constant or growing finite group in this
last averaging step.

This formulation also identifies precisely what the local Pauli
countermodel omits.  It realizes all local commutator signs and all block
masses, but it does not force the comb compression to be invariant under
the independent phase-corrected row and column translations.  Separate
block-mass marginals cannot replace `(TCB12)`.

## 6. Why the translations cannot be literal group words

The translations in `(TCB11)` cannot be supplied by a fixed family of group
words acting on the canonical coefficient atoms.  If printed group
relations forced literal row/column translations and made `T` invariant,
the same exact implication would hold in the regular representation.  The
trace-flat packet exists there, while `(TCB6)` is valid in every finite
tracial von Neumann algebra.  This would contradict the regular
representation itself.

This is the same obstruction proved from the conditional-variance viewpoint
in `FALSE_LITERAL_FIBER_MIXER_SHORTCUT.md`: a fixed-word action which both
mixes the fibers and preserves the branch statistic would make the statistic
measurable already in the regular model.

Consequently the next audit should **not** search for four literal
translation words.  The translations must be recovered from finite matrix
coordinates.  Equal-rank character blocks admit coordinate-dependent matrix
units and hence row/column shifts, even when no corresponding operator is a
group word or survives in the tracial ultraproduct.

## 7. Live matrix-coordinate target

The required theorem can now be stated without a whole-map decoder:

> Find, for each of the two row and two column Pauli generators, a bounded
> finite-coordinate shift between the four equal-rank character blocks.
> Use the multiplication-module relations to prove that the four shifts have
> vanishing phase-corrected defect on `T=qU^*q`.

The shifts may depend on the matrix coordinate and need not converge as
operators.  This is precisely what prevents the argument from applying to
the regular representation.  Once their four defects vanish, finite
Reynolds averaging gives `(TCB3)`, and the exact trace-flat masses plus
`(TCB10)` give the contradiction.

This is still a matrix-specific recovery theorem, but it asks for four
coordinate shifts on a fixed four-label packet.  It does not ask for an
unbounded commutant, a classical response-map law, or a growing family of
projections.

## 8. Scope

This note proves the analytic implication

```text
fixed Pauli packet + trace-flat masses + common-block coherence
  => fixed normalized-HS contradiction.             (TCB13)
```

It does not claim that the printed atlas relations already imply the
common-block coherence.  That last implication must be checked at the group
microstate-coordinate level; asserting it from trace flatness or literal
fixed-word relations alone would be false.
