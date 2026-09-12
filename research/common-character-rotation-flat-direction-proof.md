---
rg: 2
id: common-character-rotation-flat-direction-proof
kind: route
title: Rotate two code characters together and pinch back to the old character blocks
target: common-character-rotation-is-flat-for-involution-jacobian
requires:
  - quadratic-overlay-has-uniform-linearized-synchronization-gap
---

Since `Q^0` is a direct sum of two characters, simultaneous conjugation by
`U_theta` preserves every exact word relation.  On a coordinate where the
characters agree, `Q_i^0` is scalar and does not move.  Where they differ,
it is a signed `Z`; rotation gives a signed

```text
 cos(2theta)Z+sin(2theta)X.
```

Pinching by the old `Z`-spectral projection removes the `X` term.  This
proves `(CCF2)--(CCF3)`.

The pinched tuple is diagonal.  Its exact character product on a dual row
is `I`, and every coordinate in `supp(z)` contributes one scalar factor
`c`, proving `(CCF4)`.  Bounded row width then gives

```text
 |1-c^(m_h)|<=m_h(1-c)<=w s^2,
```

so every squared face defect is `O_w(s^4)`.  Averaging does not change that
order, while `(CCF3)` gives boundary `rho s^2`.

Finally, for every scalar `lambda in [-1,1]`,

```text
 (1-|lambda|)^2<=(1-lambda^2)^2.
```

Integrating this pointwise inequality against the spectral measure of a
selfadjoint contraction proves `(CCF7)`.
