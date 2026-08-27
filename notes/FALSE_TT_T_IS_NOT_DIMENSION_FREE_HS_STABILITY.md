# Property `(TT)/T` does not supply dimension-free Hilbert--Schmidt stability

Date: 2026-08-14

## Outcome

The proved property `(TT)/T` of the binary-Leavitt elementary group does not
close the nonhyperlinearity argument by rounding normalized
Hilbert--Schmidt microstates to honest representations.  The obstruction is
both definitional and quantitative.

Property `(TT)/T` controls quasi-cocycles into unitary representations after
removing invariant vectors.  It is not the same property as Burger--Ozawa--
Thom's `(TTT)`, and neither statement provides the dimension-uniform
stability modulus required here.

The relevant conclusion of Burger--Ozawa--Thom, Theorem 5.5, concerns
operator-norm `delta`-representations and has the form

```text
for every fixed d,
  lim_(delta -> 0) F_d(delta)=0.                       (TTH1)
```

Equivalently, its quantifiers are

```text
for every d and epsilon there exists delta(d,epsilon)>0. (TTH2)
```

A hyperlinear model has dimensions `d_n -> infinity` and multiplicative
defects `eta_n -> 0` only in normalized Hilbert--Schmidt norm.  There are
therefore two losses.  First, normalized HS control does not imply
operator-norm control uniformly in the dimension; the elementary estimate is

```text
||A||_op <= sqrt(d) ||A||_(2,d).                       (TTH2a)
```

Second, even after paying this factor in a fixed dimension, statement
`(TTH2)` gives no comparison between the resulting defect and
`delta(d_n,epsilon)`.  The thresholds may decay faster than the chosen
microstate defects.  The dimension is fixed before compactness is used in the
proof of `(TTH1)`, so that proof cannot be diagonalized into

```text
there exists delta(epsilon)>0 working for every d.     (TTH3)
```

The missing statement `(TTH3)`, with normalized-HS defect in its premise, or
a flexible version with controlled padding, is precisely a normalized-HS
stability theorem.  It cannot be silently inferred from `(TT)/T` or from the
operator-norm fixed-dimensional theorem.

There is a useful consistency check.  Becker--Lubotzky prove that an
infinite hyperlinear property-`(T)` group is not stable with respect to
unitary groups equipped with normalized Hilbert--Schmidt distance.  Thus a
generic implication

```text
property (T), (TT)/T, or quasi-cocycle rigidity
  => normalized-HS stability                              (TTH4)
```

would contradict known behavior on the hyperlinear side.

## Application to the atlas group

Let `Q` denote the binary-Leavitt atlas group.  The repository proves strong
relative quasi-cocycle rigidity for its elementary overgroup.  This remains
valuable for property and character applications, but it does not show that
an asymptotic representation

```text
phi_n:Q -> U(d_n)
```

is close to an honest representation when `d_n` diverges.

Every honest finite-dimensional representation kills the relevant atlas
survivor, while a faithful hyperlinear model would retain it at squared
distance `2`.  Therefore any one of the following would finish the
nonhyperlinearity proof:

1. a dimension-free stability modulus for the particular atlas relator
   packet;
2. flexible normalized-HS stability with padding `o(d_n)`; or
3. a direct word-kill inequality bounding the survivor by finitely many
   relator defects uniformly in `d`.

None is a consequence of the existing `(TT)/T` proof.  Item 3 is the most
targeted version: it is exactly the finite-coordinate multiplication or
leakage theorem already isolated by the Pauli/Leavitt reduction.

## Research consequence

Do not route the current proof through abstract `(TT)/T -> stability`.
Either prove a new dimension-uniform theorem for the explicit atlas packet,
or use the independent perfect-completeness/solution-group route.  Fixed-
dimension Ulam stability does not move the universal-hyperlinearity gate.

## Primary sources

- M. Burger, N. Ozawa, and A. Thom, *On Ulam stability*,
  [arXiv:1010.0565](https://arxiv.org/abs/1010.0565), especially Theorem 5.5.
- O. Becker and A. Lubotzky, *Group stability and Property (T)*,
  [arXiv:1809.00632](https://arxiv.org/abs/1809.00632).
- A. Dogon and I. Vigdorovich, *Hyperlinearity, stability and asymptotic
  spectral gap of higher rank lattices*,
  [arXiv:2506.20843v2](https://arxiv.org/abs/2506.20843v2), for the current
  flexible-HS-stability conditional endpoint.
