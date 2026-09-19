# The raw compressor exposes an exact two-sheet coefficient packet

Date: 2026-08-13

## Outcome

The multiplicative Pauli packet does more than reproduce the finite
extraspecial countermodel.  The raw compressor creates a second Pauli packet
with a distinct center, and the two packets cancel to a canonical coefficient
`C2^2` on a positive-density two-sheet carrier.

Let

```text
X_i = x12(t_i),       Z_j = x23(s_j),
R   = raw,
C_i = [R,X_i],        A_i = X_i C_i = R X_i R.
```

The original packet `<X0,X1,Z0,Z1>` has order `32` and its commutators encode
the multiplicative table

```text
[X_i,Z_j] = c^(delta_ij).
```

Exact prefix arithmetic proves:

```text
C_0 C_1 = C_1 C_0,
[C_i,Z_j] = d^(delta_ij),
[X_i,C_j] = 1,
c != d,
[c,d] = 1.
```

Both `c` and `d` are central in the mixed generators.  The mixed double-Pauli
cell has order `256`, while the raw-normalized closure has order `512` with
element-order histogram

```text
{1: 1, 2: 143, 4: 368}.
```

The raw action on the two centers is exact:

```text
R c R = c d,          R d R = d.                    (DPC1)
```

This is a two-sheet action inside the `d=-1` carrier: `R` exchanges the
`c=-1` and `c=+1` halves.  Moreover

```text
A_i^2 = 1,            [A_0,A_1]=1,
[A_i,Z_i] = c d,      [A_i,Z_j]=1 for i != j.       (DPC2)
```

On the joint corner `c=d=-1`, the `A_i` commute with every original Pauli
generator.  Hence they form a coefficient `C2^2`; the full sign cell
`<A0,A1,c,d>` is `C2^4` of order `16`.  Under the regular trace the `d=-1`
carrier has trace `1/2`, the joint `c=d=-1` corner has trace `1/4`, and every
coefficient character cut has fixed positive trace.

## The invariant two-sheet splice

Write, inside the `d=-1` carrier,

```text
P = (1-c)/2,
B_i = P A_i + (1-P) X_i.                            (DPC3)
```

Equation `(DPC1)` says `R P R=1-P`, while `R X_i R=A_i` and
`R A_i R=X_i`.  Therefore

```text
R B_i R = B_i.                                      (DPC4)
```

The chosen summand commutes with `Z_i` on each sheet: `A_i` on `P`, and
`X_i` on `1-P`.  Consequently

```text
B_i Z_j = Z_j B_i,
B_i^2=1,
[B_0,B_1]=1.                                        (DPC5)
```

Thus the raw compressor has canonically converted two Pauli shifts into a
raw-invariant coefficient `C2^2`.  This is the multiplication-to-coefficient
structure absent from the single-sign and ambient-finite-subgroup attempts.
The general algebraic parts of `(DPC3)--(DPC5)` are kernel-checked in
`GroupApproximation/Sofic/DoublePauliCoefficient.lean`: the file proves
sheet-swap invariance, sheetwise-to-global commutation, and preservation of
the involution relation.

## What this does and does not solve

The result is not yet the universal hyperlinearity contradiction.  Every
group displayed above is finite, so its regular representation is itself a
tracial matrix model.  The gain is instead a canonical coefficient carrier
which survives raw transport and has fixed density.

The remaining comb question is now concrete:

> Compute the blocks of `U* B_i U` relative to the raw-invariant coefficient
> cuts, and determine whether the cross-root multiplication relations force
> the transported trace-`1/4` Pauli carrier under the trace-`1/8` initial cut
> of `PauliBranchTransfer`.

Equivalently, the next audit must use the off-diagonal comb action on the new
coefficient factor.  Ordinary subgroup intersection cannot work: the
original Pauli packet has trivial intersection with both its `U` and `RU`
conjugates.  The exact raw-relative intersection is only
`<Z0,Z1> = C2^2`, which is precisely why the two-sheet cancellation above is
the relevant bridge.

## Reproducible certificate

`experiments/atlas_multiplicative_pauli_comb_intersection.py` checks all group
orders, intersections, commutators, center transport, and the coefficient
sign cell.  Its exact expected output is
`experiments/atlas-multiplicative-pauli-comb-intersection.json`.  The bounded
order-512 closure and Lean checking were run using the existing warm MSI
workspace on one core; no local code or build was run.

