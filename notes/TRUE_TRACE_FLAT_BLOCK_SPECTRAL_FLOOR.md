# A trace-flat comb block has a positive well-conditioned spectral sector

Date: 2026-08-13

## Outcome

The failure of the scaled-isometry identity in
`TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md` does not leave both density and
condition number uncontrolled.  An elementary spectral truncation supplies
both with explicit constants.

Fix one raw character cut `F` and one transported cut `G`.  They satisfy

```text
tau(F)=tau(G)=1/8,             tau(FG)=1/64.
```

Put

```text
H=F G F.
```

Then `H` is a positive contraction supported on `F`, and

```text
tau(H)=1/64.                                           (SFF1)
```

Let `P` be the spectral projection of `H` for eigenvalues at least `1/16`,
and write `r=tau(P)`.  The low spectral part has trace at most

```text
(1/16)(tau(F)-r)=(1/16)(1/8-r),
```

while the high part has trace at most `r`.  Hence

```text
1/64 <= 1/16(1/8-r)+r,
```

which rearranges to

```text
r >= 1/120.                                           (SFF2)
```

On `P`, one has

```text
P H P >= (1/16)P.                                    (SFF3)
```

Equivalently, the corresponding `F`--`G` transition block has singular
values at least `1/4` on a subspace of normalized dimension at least `1/120`.
This is dimension-free.

The rational endpoint `(SFF2)` is kernel-checked in
`GroupApproximation/Sofic/DoublePauliCoefficient.lean` as
`one_div_120_le_of_trace_flat_spectral_split`.  The remaining application of
finite-dimensional spectral calculus uses the existing `spectralAbove`
infrastructure.

The density and conditioning conclusions do **not** imply a compressed
Leavitt obstruction without invariance.  The exact rank-one countermodel in
`FALSE_WEIGHTED_LEAVITT_CONTRACTION_GAP.md` has carrier trace `1/2`, singular
value `1`, and zero compressed product defects: one arrow simply exits the
carrier and its mate returns it.  Hence the third obligation below is
logically load-bearing, not an artifact of the proof organization.

## Consequence for the robust radical-quotient gate

The earlier formulation `(RPC128)` listed three obligations for a spectral
truncation:

1. a uniform lower singular-value bound;
2. positive normalized trace of the retained sector; and
3. approximate invariance under the four multiplication arrows.

Equations `(SFF2)--(SFF3)` discharge the first two for every one of the
sixteen comb coefficient blocks.  The only genuinely structural obligation
left is the third:

> prove that one selected spectral projection of `FGF` is asymptotically
> invariant under the recovered left/right coefficient multiplications (or
> that its orbit has a common positive-density invariant subprojection).

If this holds, polar decomposition on the retained sector has condition
number at most `4`, and the reduced Fourier/contraction argument becomes
dimension-free.  If it fails, the failure itself is a fixed leakage term and
must be compared with the one-cut balance obstruction.  Positive spectral
mass, even at density `1/2` and with perfect conditioning, cannot substitute
for this comparison.

This spectral route is a fallback to the shorter coefficient-algebra
alignment gate in `TRUE_DOUBLE_PAULI_COMB_ANTINORMALIZER_GAP.md`.  It matters
because it shows that nonuniform singular values are not, by themselves, a
fatal escape.
