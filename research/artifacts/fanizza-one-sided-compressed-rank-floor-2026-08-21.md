# One compressed ambient unitary already detects the guarded rank deficit

## Finite-dimensional inequality

Let `E,H` be projections in `M_d(C)` with `H<=E`, put

```text
F=E-H,
```

and let `U` be any unitary.  Define the compressed ambient word

```text
X=F U E.                                                (OCR1)
```

Then

```text
||X^*X-E||_2^2 >= tr_d(H).                              (OCR2)
```

Indeed `X^*X` is a positive contraction on `E C^d` and

```text
rank(X^*X)=rank(X)<=rank(F)=rank(E)-rank(H).            (OCR3)
```

Hence `X^*X` has kernel of dimension at least `rank(H)` inside `E C^d`.
On that kernel `X^*X-E=-I`, giving `(OCR2)`.

Equivalently, if `H` is the selected D8 holonomy projection with
`tr_d(H)->1/8`, every proposed source-full compressed return has the fixed
floor

```text
||X^*X-E||_2 >= 1/sqrt(8)-o(1).                        (OCR4)
```

No second return product, determinant, or phase orientation is needed.

## Infinite completeness

The obstruction is genuinely finite.  On a separable infinite Hilbert
space, two infinite projections `E` and `F<E` may be Murray--von Neumann
equivalent.  A unitary on a larger ambient space can have a compression
`X=FUE` with

```text
X^*X=E,       XX^*=F.                                  (OCR5)
```

This is the Toeplitz/Hilbert-hotel shape required by exact HALT
completeness.

## The fixed-group-algebra firewall

The same inequality holds in every finite tracial von Neumann algebra in
the Murray--von Neumann dimension sense.  If `E,F,X` were fixed elements of
a group algebra and the defining relators universally implied
`X^*X=E, XX^*=F`, applying the canonical trace in the group von Neumann
algebra would give

```text
tau(E)=tau(X^*X)=tau(XX^*)=tau(F),
```

and hence `tau(H)=0`.  Faithfulness would kill `H`.  Thus a literal fixed
partial-isometry relation cannot preserve a positive regular D8 mark.  This
recovers the regular firewall with only one compressed map.

Nor does replacing exact equality by a relator-telescoping estimate help:
any estimate derived functorially from fixed group-algebra identities also
holds at zero defect in the regular finite trace.

## Minimal surviving decoder

The load-bearing finite-coordinate statement is now especially small.  In
each matrix microstate, after exactifying the fixed packet, one must select
the actual guarded projections `H<=E` and a compressed ambient unitary
`X=(E-H)UE` such that

```text
||X^*X-E||_2 <= omega(def),       omega(t)->0.          (OCR6)
```

The selection/estimate must use integer multiplicity data unavailable in an
arbitrary finite tracial algebra; otherwise the firewall applies.  Combining
`(OCR2)` and `(OCR6)` forces `tr(H)->0`.

This is strictly weaker than decoding both products in `(STR1)`: source
fullness into the smaller target alone is impossible in finite dimensions.
It is also sharper than a support-only Toeplitz return, because `(OCR6)`
authenticates the full source Gram rather than merely naming nonzero source
and target supports.
