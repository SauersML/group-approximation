---
rg: 2
id: stw07-singular-trace-normal-form-proof
kind: route
title: Kill bounded traces on the stable kernel and exclude a traceless kernel by Gabe's theorem
target: stw07-counterexample-has-singular-trace-normal-form
requires:
  - stw07-bk-reduces-to-stable-character-kernels
artifacts:
  - research/artifacts/stw07-status-and-stable-character-reduction-2026-08-30.md
---

Start from a counterexample `A` and use the stable-character reduction to
put

```text
I=A tensor K,             E=I~.                          (SN1)
```

Let `tau` be a bounded trace on the stable algebra `I`.  Choose isometries
`s_1,...,s_n in M(I)` with orthogonal ranges.  For any `a in I_+`, the
positive elements `s_i a s_i*` are orthogonal, have norm `||a||`, and all
have trace `tau(a)`.  If `C` bounds `tau` on the positive unit ball, then

```text
n tau(a)=tau(sum_i s_i a s_i*) <= C||a||.                (SN2)
```

Letting `n` grow proves `tau(a)=0`; thus `I` has no nonzero bounded trace.
Every tracial state on `E` restricts to zero on `I`, hence factors through
`E/I ~= C` and equals `chi`.  Essentiality and `I!=0` make `chi`
nonfaithful.

Suppose now that `I` were traceless in the sense that every
lower-semicontinuous tracial weight were `{0,infinity}`-valued.  The algebra
`I` is separable, nuclear (hence exact), and stably finite.  Gabe's traceless
AF-embedding theorem then makes `I` AF-embeddable, in particular
quasidiagonal.  Quasidiagonality passes to unitizations, so `E=I~` would be
quasidiagonal, a contradiction.  Hence `I` has a lower-semicontinuous
tracial weight with a finite nonzero value.  Equation `(SN2)` shows that no
such nonzero weight can be bounded, proving all four properties.
