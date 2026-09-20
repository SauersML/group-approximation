---
rg: 2
id: nonhyperlinear-via-leavitt-chromatic-commutator-code
kind: route
title: A bounded-area chromatic commutator code at the marked Leavitt root makes the Steinberg group non-hyperlinear
target: non-hyperlinear-group
requires:
  - binary-leavitt-bounded-area-chromatic-code
  - chromatic-codes-kill-marks-in-every-bi-invariant-approximation
---

This is a hardness-transfer bridge.  The leaf
`binary-leavitt-bounded-area-chromatic-code` was introduced as an
operator-norm (MF) tool, as distinct from the Hilbert--Schmidt Carmichael
route `nonhyperlinear-from-leavitt-steinberg-carmichael-area`.  But it
already yields an explicit non-hyperlinear group.

Take `Delta = St_20(L_(F_2)(1,2))` and `z = x_13(s_1 t_1)`.  Here `z != 1`,
as shown in `non-weakly-sofic-via-leavitt-chromatic-commutator-code`: the
Steinberg map sends `z` to `I + s_1t_1 E_13`, and `s_1t_1` is a nonzero
idempotent.

If the leaf holds, then (BI3)-(BI4) of
`chromatic-codes-kill-marks-in-every-bi-invariant-approximation` apply.  Every
homomorphism from `Delta` to a metric ultraproduct of
`(U(n), normalized HS)` kills `z`, so `Delta` is not hyperlinear.

The Hilbert--Schmidt conclusion needs no Carmichael (order-three)
structure.  The commutator table itself suffices.
