---
rg: 2
id: agent-free-compressor-contractive-toeplitz-no-go
kind: claim
title: Contractive finite Toeplitz models cannot retain a positive-density one-sided defect
distinct_from:
  hs-schur-toeplitz-root-defect-collapse: that concerns arbitrary normalized-HS unitary microstates of the Steinberg HNN group; this is a sharp no-go only for microstates decoded through contractive coefficient matrices.
  toeplitz-defect-roots-form-independent-heisenberg-cells: that studies abstract root representations which need not arise from coefficient operators.
---

Let `X,Y in M_d(C)` be contractions and use normalized Hilbert--Schmidt norm.
Put

```text
delta=||YX-I||_2.
```

Then

```text
||XY-I||_2 <= 2 sqrt(2 delta).                            (CTT1)
```

Consequently, for every sequence of finite-dimensional contractive
coefficient models satisfying `||Y_dX_d-I||_2->0`, the Toeplitz defect

```text
P_d=I-X_dY_d
```

converges to zero in normalized Hilbert--Schmidt norm. In particular neither
ordinary unilateral-shift truncations, cyclic closures, Følner compressions
by contractions, nor their direct-sum amplifications can falsify
`hs-schur-toeplitz-root-defect-collapse` while retaining the marked root on a
carrier whose trace is controlled by `P_d`.

For `delta>=1`, `(CTT1)` follows from the trivial bound
`||I-XY||_2<=2`. Assume henceforth that `delta<1`. Then
`||YX||_2>=1-delta` and contractivity of `Y` give

```text
||X||_2^2 >= (1-delta)^2.
```

Since `0<=I-X^*X<=I`,

```text
||I-X^*X||_2^2
 <= tr_d(I-X^*X)
 <= 2 delta.
```

The same estimate holds for `I-XX^*`, because `X^*X` and `XX^*` have the
same matrix moments. Also cyclicity of trace and contractivity give

```text
||Y-X^*||_2^2
 =||Y||_2^2+||X||_2^2-2 Re tr_d(XY)
 <=2-2 Re tr_d(YX)
 <=2 delta.
```

Therefore

```text
||I-XY||_2
 <=||I-XX^*||_2+||X(X^*-Y)||_2
 <=2 sqrt(2 delta),
```

which proves `(CTT1)`.

This is not a proof of the full root-collapse claim. An arbitrary unitary
microstate of `EL_5(R_f)*_alpha` need not decode to contractive matrices
`X,Y`; producing such a decoder is precisely the linear-sofic/root-kernel
wall. The result instead closes a broad falsification family and shows that
any countermodel must decouple root phase mass from the physical coefficient
defect.

## Attempts

- **Truncated unilateral shift.** Taking `Y=X^*` makes both one-sided defects
  rank one, hence normalized trace `1/d`; the marked carrier vanishes.
- **Cyclic closure.** Replacing the truncation by a cyclic shift makes
  `YX=XY=I`, so the defect vanishes identically.
- **Positive-density boundary.** Direct sums of bounded Toeplitz blocks retain
  positive defect density only by retaining the same positive density of the
  `YX=I` error. Inequality `(CTT1)` is the dimension-free version of this
  obstruction.
