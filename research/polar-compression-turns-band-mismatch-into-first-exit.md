---
rg: 2
id: polar-compression-turns-band-mismatch-into-first-exit
kind: claim
title: Polar compression turns conductor-band mismatch into literal first-exit mass
distinct_from:
  kazhdan-polar-rounding-produces-supported-gallery-edges: that rounds an almost intertwiner after genuine endpoint group actions have been decoded; this directly compresses a raw actor unitary between spectral-band projections and charges all failure to their geometric mismatch.
  partial-isometry-translate-cancel-charges-first-exit: that uses already-supplied partial transitions in translated triangles; this canonically supplies those partial transitions from projections and raw actor words.
  six-edge-holonomy-energy-ledger-is-scale-free: that charges a sixfold returned product after supported transitions are supplied; this bounds the distance between that supported product and the raw group-word product.
---

Let `(M,tau)` be a finite tracial von Neumann algebra, let `P,Q` be
projections with

```text
tau(P)=tau(Q)=mu,                                        (PCB1)
```

and let `U` be unitary.  Define the one-edge band leakage

```text
ell=||(1-Q)UP||_2^2                                     (PCB2)
```

and take the polar decomposition

```text
QUP=V|QUP|.                                              (PCB3)
```

Then `V` is a partial isometry with source `S=V^*V<=P` and range
`T=VV^*<=Q`, and

```text
tau(P-S)<=ell,
tau(Q-T)<=ell,
||QUP-V||_2^2<=ell,
||UP-V||_2^2<=2ell.                                     (PCB4)
```

Thus the same scalar which measures failure of the raw word to carry `P`
into `Q` controls both missing supports and polar-rounding displacement.
There is no dependence on matrix dimension, spectral alphabet size, or
conductor depth.

## Proof

Put `X=QUP`.  Since `0<=|X|<=P`,

```text
ell=tau(P)-||X||_2^2=tau(P-X^*X).                       (PCB5)
```

On the kernel of `|X|`, the positive contraction `P-X^*X` equals the
identity.  Hence `tau(P-S)<=ell`.  The nonzero singular values `s` of `X`
lie in `[0,1]`, and `(1-s)^2<=1-s^2`; integration against `tau` gives
`||X-V||_2^2<=ell`.  Because `tau(S)=tau(T)` and `(PCB1)` holds, the source
and range deficiencies agree.  Finally

```text
UP-V=(1-Q)UP+(QUP-V),                                   (PCB6)
```

and the two summands have orthogonal row supports, proving the last bound in
`(PCB4)`.

## Closed products

Let `P_0,...,P_k=P_0` have common trace, let `U_i` be raw transition
unitaries, and let `V_i` be the polar compression from `P_(i-1)` to `P_i`.
Write

```text
ell_i=||(1-P_i)U_iP_(i-1)||_2^2.                        (PCB7)
```

Because the range of `V_(i-1)...V_1` lies under `P_(i-1)`, word telescoping
using `(PCB4)` gives

```text
||V_k...V_1-U_k...U_1P_0||_2
 <=sum_i sqrt(2ell_i).                                  (PCB8)
```

If the raw group-word product has return defect

```text
||(U_k...U_1-I)P_0||_2<=epsilon_word,                   (PCB9)
```

then

```text
||V_k...V_1-P_0||_2
 <=epsilon_word+sum_i sqrt(2ell_i).                     (PCB10)
```

Every failure in `(PCB10)` is therefore either a fixed raw word defect or
an explicit conductor-band crossing `(PCB7)`.  Combined with
`partial-isometry-translate-cancel-charges-first-exit`, this completes the
operator-theoretic passage

```text
equal-trace conductor projections + raw actor words
  -> supported triangle/gallery transitions + first-exit ledger.          (PCB11)
```

What remains in the arithmetic decoder is not polar or intertwiner rounding.
It is the matrix-coordinate construction of equal-trace band projections
whose leakage can be assigned consistently to the next conductor layer.
