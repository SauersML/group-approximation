---
rg: 2
id: seven-cell-core-reduces-thompson-completion-to-one-equation
kind: route
title: Share the seven-cell anchors and use support and fixed germs to constrain a completion
target: leavitt-seven-cell-thompson-completion-requires-moved-pairs
requires:
  - leavitt-has-an-explicit-finite-c-killing-certificate
  - leavitt-eight-word-packet-is-quantitatively-equivalent
  - leavitt-finite-wreath-targets-have-eight-tail-normal-form
artifacts:
  - research/artifacts/leavitt-seven-cell-centralizer-completion-2026-09-08.md
  - experiments/leavitt_seven_cell_exact_replay.py
---

Permute seven prefix cells as the nonzero vectors of `F_2^3`.
Take the coordinate cycle for `C` and `x_12(1)` for both first
involutions. The constant compiler gives the coordinate swaps
`A=(12)` and `D=(13)`. Its two three-point orbits support a diagonal
copy of the authenticated Thompson presentation, fixing the remaining
cell. Hence its explicit `B_0` completes these same `A,C,D`.

The only missing condition for this construction is that a commuting
involution `Z` produce `B_0` under the actual shared compiler. The
finite-factor laws, the two anchors, and the six retained Thompson
rows then hold. The wreath normal form can restore an injective
marked second factor after such a completion exists.

If `Z` fixes the moved region of `Y` pointwise, the support of the
first compiled commutator is confined to three cells. The equation
`B=B_0` on one further cell forces `Z` to fix another entire cell.
The compiler then maps that cell onto a whole target cell, whereas
`B_0` maps it into the prescribed proper subcell, a contradiction.

The required map `R=X_0 B_0` has two contracting fixed germs with
eventually-one tails and two expanding fixed germs with eventually-zero
tails. Finite-prefix conjugation preserves both the signed length
change at a fixed point and its eventual-tail class. Thus `R` is not
conjugate to its inverse. But `Q_1=[C^-1 Z C,Y]` is reversed by `Y`;
if `P_1^2=1`, the identity `R=P_1 Q_1 P_1` would make `R` reversible.
This proves the further necessary condition `P_1^2!=1`.

The native certificate identifies `p_1=x_23(t_1)`, whose square
vanishes in characteristic two. Its unreduced lengths are `36` and
`72` for `p_1` and `p_1^2`. That additional true row excludes this
prescribed diagonal architecture. Tail complementation after each
source code leaf fixes `A,D` and inverts `B`. Twisting one component
this way restores reversibility of `R`, but its unique positive
fixed germ in each eventual-tail class prevents a square root.
An involutive `P_1` would make `R` conjugate to the square `Q_1`,
so this twist is excluded too.

For repeated components with `n_+` standard and `n_-` complemented
orientations, reversibility requires `n_+=n_-`. A square root would
permute each finite set of odd-exponent fixed germs in two-cycles,
forcing both counts even. These are necessary conditions only;
four balanced components are not asserted to complete the compiler.
No arbitrary-embedding exclusion or square relation among the eight
imposed packet rows is assumed.

The centralizer parametrization retains actions on both regions and
therefore does not discard the unresolved possibilities. No prefix
search, successful completion, or hyperlinear target is supplied.
