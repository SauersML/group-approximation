# Exact harmonic dual systole at projective level 121

Date: 2026-08-11

## Theorem-level outcome

For the signed cellular complex of the `SL_3(Z)` projective action on
`P^2(Z/121Z)`, the rational second harmonic space has dimension seven and
its dual cycle-pairing lattice satisfies

```text
lambda_1(Q^#)=0.45320230767323166... .
```

The exact shortest squared norm is the rational number stored in
`experiments/projective-cellular-n121-systole-span.json`.  The shortest
vector is nonintegral, with exact class order equal to the common
denominator in that certificate.  Nevertheless the sharp chartwise
spherical bound is

```text
B_121^2=12,
```

and exact arithmetic certifies

```text
12 lambda_1(Q^#)^2>1.
```

Therefore every nonzero vector of `Q^#` lies above the spherical
localization threshold.  None of the seven new level-121 harmonic
directions contributes a dangerous denominator-collapse class.

## Why this is stronger than the earlier lift tests

The lower-level chart at level `11` has `H_2=0`, so all seven directions at
level `121` are genuinely new rather than ordinary pullbacks.  Modular
lifting of a chosen pair of cuspidal generators would only test those two
directions and would not control the remaining five.  The exact shortest
vector computation instead screens the entire rank-seven rational harmonic
space simultaneously.

The computation does not require a primitive basis for
`H intersect Z^1940`.  By `TRUE_QSHARP_SPAN_BASIS_REDUCTION.md`, any rational
basis matrix `R` for `H`, together with an integral cycle basis `C`, recovers
the physical dual lattice from the column lattice of `R C^T`.  This reduced
the decisive run to `5m16s` on one MSI core.

## Certificates

```text
experiments/projective-cellular-n121-harmonic-span.json
SHA-256 90fccdd4c83c3812cecae3dadf8076aadc6cfaa23159dede4853593ac8b0e3eb

experiments/projective-cellular-n121-systole-span.json
SHA-256 f9b5733277ba8c942710d6f24cf5407895478e13aa71d5014cbd28475a0c51b3
```

The first certificate records rank seven and zero exact residual.  The
second reconstructs `Q^#` from exact cycle pairings, checks the exported
harmonic lattice lies in `Q^#`, runs exact integer SVP, tests ambient
integrality, computes the class order, and performs the threshold comparison
over the rationals.

## Scope

This eliminates level `121`; it does not prove a uniform systole lower bound
over every projective prime-power chart.  The next theorem-shaped target is
to explain structurally why all presently tested charts except level `53`
are above threshold, or to control the paired integral decoder at the
exceptional level `53` without enumerating levels one by one.
