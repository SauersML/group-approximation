# Antipodal trace extraction

Status: exact and quantitative finite-matrix certificate; Lean formalized.

## Statement

Let `S,U in U(d)` and use normalized trace and normalized squared
Hilbert--Schmidt norm.  Then

```text
4 |tr_d(U)|^2 <= ||S U S* + U||_2^2.
```

Consequently, if

```text
S U S* = -U,
```

then `tr_d(U)=0` and

```text
||U-1||_2^2 = 2.
```

The quantitative form also applies to a sequence: if the antipodal defect
tends to zero in normalized Hilbert--Schmidt norm, then the normalized traces
of the `U` coordinates tend to zero.

## Proof

Cyclicity of finite-dimensional trace and `S* S=1` give

```text
tr_d(S U S*) = tr_d(U).
```

Therefore

```text
tr_d(S U S* + U) = 2 tr_d(U).
```

Normalized Cauchy--Schwarz says that the squared modulus of normalized trace
is at most normalized squared Hilbert--Schmidt norm.  Applying it to the
defect proves the inequality.  Exact antipodality makes the defect zero.  For
unitary `U`, the standard identity

```text
||U-1||_2^2 = 2 - 2 Re tr_d(U)
```

then gives the asserted separation.

## What this closes—and what it does not

This closes the *local trace-extraction step*.  Once an antipodal conjugacy is
obtained in matrix coordinates, its marked unitary is automatically visible
to the hyperlinear metric; no positive-rank or adjoint-density hypothesis is
needed.

It does **not** manufacture that conjugacy from the candidate group's present
relations.  The remaining global problem is now sharply separated from the
local analytic step: construct or recover, in compatible matrix coordinates,
a unitary `S` and a marked unitary `U` whose antipodal defect tends to zero.

Lean source:
[`GroupApproximation/Sofic/AntipodalTraceExtraction.lean`](../GroupApproximation/Sofic/AntipodalTraceExtraction.lean).

The ultraproduct/radical endpoint is also formalized in
[`GroupApproximation/Sofic/AntipodalRadicalCollision.lean`](../GroupApproximation/Sofic/AntipodalRadicalCollision.lean): an asymptotic
unitary representation with this profile detects its marked element, and a
sofic-residual marked element then yields a hyperlinear nonsofic range.
