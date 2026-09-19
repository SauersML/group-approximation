---
rg: 2
id: half-period-sector-sits-inside-two-level-exit
kind: claim
title: The half-period wrong sector is contained sharply in the two-level conductor exit
distinct_from:
  half-period-weyl-band-transport-is-defect-or-leakage: that produces a root-defect versus wrong-sign leakage inequality for a rectangular transporter; this identifies that leakage with a canonical dyadic spectral cut and places it inside the pre-existing two-level conductor exit.
  finite-dyadic-square-function-detects-deep-root-mass: that compares the union of all root orders above two with a sum over dyadic powers; this compares the top primitive layer and the top two layers by exact nested Fourier projections at one fixed depth.
  spectral-compressed-leakage-is-finite-word-moment-functional: that Fourier-expands arbitrary finite-order source and target cuts; this gives the arithmetic specialization, the exact nesting identity, and the sharp intermediate-conductor counterpacket.
---

Let `N>=2`, `d=2^N`, `m=d/2`, and let `T` be a unitary with `T^d=I` in a
finite tracial von Neumann algebra. Define

```text
F_<=N-1=(I+T^m)/2,
F_<=N-2=(1/4)sum_(j=0)^3 T^(j d/4).                    (HCE1)
```

These are spectral projections. The first is the sum of the characters of
order dividing `2^(N-1)`; the second is the sum of those of order dividing
`2^(N-2)`. In particular

```text
F_<=N-2 <= F_<=N-1,                                   (HCE2)
I-F_<=N-1 = F_=N,
F_<=N-1-F_<=N-2 = F_=N-1,                             (HCE3)
```

where `F_=k` denotes the exact-conductor-`k` spectral projection.

For every operator `X`, put

```text
ell_hp=||(I-F_<=N-1)X||_2^2,
ell_2 =||(I-F_<=N-2)X||_2^2.                           (HCE4)
```

Nested orthogonality gives the exact identity

```text
ell_2=ell_hp+||F_=N-1 X||_2^2,                         (HCE5)
```

and hence `ell_hp<=ell_2` with constant one.

Apply this with `X=W` from
`half-period-weyl-band-transport-is-defect-or-leakage`. Its wrong-sign term
is exactly `ell_hp`: the negative half-period sector is the primitive
depth-`N` sector. If the endpoint in the arithmetic first-exit ledger is the
canonical two-level descendant `F_<=N-2`, then the already-recorded exit
`||(I-F_<=N-2)W||_2^2` pays the Weyl wrong-sector leakage without loss.
Thus no additional analytic comparison is needed between the local Weyl
dichotomy and that conductor ledger.

The containment cannot be reversed. Take `T` to be a scalar of exact order
`2^(N-1)` and `X=I`. Then

```text
ell_hp=0,                 ell_2=1.                     (HCE6)
```

So the half-period test alone does not certify the full two-level descent;
the intermediate exact-conductor-`N-1` band is invisible to it. This is
harmless in the forward use `(HCE5)`, where the larger established
two-level exit pays the smaller Weyl leakage, but it forbids replacing the
two-level ledger by the binary half-period cut.

Finally, `(HCE1)--(HCE5)` do not construct the six `42`-atom chart PVMs.
Indeed tensor every clock, root word, and transition by the identity on
`K=(C^42)^(tensor 6)`, and choose the chart-`w` PVM to be the coordinate
PVM on the `w`-th tensor factor. All quantities in `(HCE1)--(HCE5)` are
unchanged, while different chart atoms have flat overlap `1/42^2` rather
than diagonal overlap. Hence the exact spectral identification closes the
first-exit bookkeeping only; separate root-chart covariance must still
construct each chart PVM before the finite-tree synchronization theorem can
be applied.
