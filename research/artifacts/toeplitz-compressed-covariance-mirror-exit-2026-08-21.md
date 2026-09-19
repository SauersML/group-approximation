# Compressed Toeplitz covariance has an exact positive-density mirror exit

## The natural word

For a source projection `E`, an ambient unitary `T`, and
`Q=TET^*`, the ordinary reflection word

```text
[(1-2E), T(1-2E)T^*]=[(1-2F),T(1-2E)T^*]=1             (A1)
```

says that the source, guarded target, and conjugate range cuts commute.  A
proper unilateral-shift model with `Q=E-H=F` satisfies `(A1)` and therefore
preserves the desired infinite completeness.

## Exact finite escape

In finite dimension choose

```text
E=F direct_sum H,             Q=F direct_sum C,
dim(C)=dim(H),                C<=1-E.                   (A2)
```

Let `T` fix `F` and swap `H,C`.  Then `Q=TET^*`, `(A1)` is exact, and

```text
FTE=F,                E-(FTE)^*(FTE)=H.                 (A3)
```

The missing Gram mass can have the native value `tr(H)=1/8`; the mirror
exit has the same value.  Thus the countermodel is positive-density, not a
long-chain boundary effect.

Finite trace sees only

```text
tr(E(1-Q))=tr((1-E)Q),                                  (A4)
```

so cyclicity balances the missing and mirror exits instead of charging
them.

## Exact expressibility boundary

On the proper nested model, the three occupied characters of the commuting
reflection pair are `(--),(-+),(++)`.  They form a faithful representation
of `C_2 times C_2`.  Therefore every ordinary word in the two reflections
which holds on the nested model also holds after adding the fourth `(+-)`
mirror cell.  Reflection words cannot orient the inclusion.

The orientation is the block equation

```text
(1-F)TE=0.                                              (A5)
```

This uses projection addition/compression.  The commutator word `(A1)` is
its multiplicative shadow and forgets exactly `(A5)`.  Translation reset
and old-spin Pauli localization do not recover it because the mirror cell
can occupy the scalar reset multiplicity factor.

The direct equality word `1-2F=T(1-2E)T^*` would remove the mirror, but it is
full projection conjugacy.  In the canonical finite trace it gives
`tr(E)=tr(F)` and hence kills the positive guarded projection `H`; this is
the regular firewall, not a compressed solution.
