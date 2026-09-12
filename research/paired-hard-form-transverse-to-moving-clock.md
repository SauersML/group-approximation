---
rg: 2
id: paired-hard-form-transverse-to-moving-clock
kind: claim
title: The Boolean rank-jump form is the covector transverse to the moving kernel clock
artifacts:
  - experiments/paired_frame_moving_kernel_orbit.py
distinct_from:
  paired-frame-moving-kernel-is-a-rank-one-veronese-clock: that identifies the moving relation line L_n; this identifies the forbidden alternating form and computes its nonzero pairing with every moved line.
  support-packet-paired-word-frame-exposes-forbidden-rank: that computes a rank-two form on the forbidden plus sector; this locates that form in wedge coordinates and couples it to the polynomial degree clock.
  free-root-first-detection-eigenvectors-localize-exactly: that turns a first-detection character into top-boundary mass; this supplies the explicit leading polynomial which the character must detect.
---

Use the wedge-coordinate order `(01,02,03,12,13,23)`.  The alternating form
of the paired frame on the forbidden plus sector

```text
(source,coefficient)=(101,011)
```

is the single covector

```text
h=e_02^*.                                                (HTK1)
```

The forced reverse minus sector `(011,101)` has the same form `h`, whereas
the stationary minus sector `(101,101)` has zero form.  Thus `h` is exactly
the one-Pauli Boolean rank jump.

For the moving relation line `L_n=R v_n` of `(MVK4)`,

```text
h(v_n)=c_n^2.                                            (HTK2)
```

It vanishes at `n=0`, because `v_0=e_13`, and for every `n>=1` it is nonzero
with

```text
deg h(v_n)=4n-2.                                         (HTK3)
```

Consequently the forbidden rank-one form is transverse to every transported
kernel after level zero, and its transverse coefficient is the unique leading
degree of the clock.  The nonlinear Boolean bit, the rank-one packet bit, and
the new polynomial degree are therefore the same relative coordinate rather
than three unrelated gadgets.
