---
rg: 2
id: all-dual-operator-tail-contraction-proof
kind: route
title: Apply Minkowski on each unique dual row and count good witnesses
target: all-dual-unique-neighbors-contract-operator-tails
requires:
  - dellm-all-dual-presentation-has-many-unique-neighbors
  - adjoint-parity-cone-lifts-to-loewner-order
---

For a commuting parity row `h` and `s in h`, put
`V=prod_(i in h minus {s})Q_i`.  Then `V` is a reflection,

```text
||Q_s-V||_2=e_h,
||[Q_s,Q_j]||_2
 <= sum_(i in h minus {s})||[Q_i,Q_j]||_2+2e_h.           (AUP1)
```

Minkowski in the normalized `ell_2` sum over `j` gives

```text
q_s <= sum_(i in h minus {s})q_i+2e_h.                   (AUP2)
```

Fix `U_t`.  Every unique-neighbor row `h` has
`h intersect U_t={s}`.  If `h` is outside `B_rho`, `(AUP2)` gives

```text
q_s<(w-1)t+2rho.                                         (AUP3)
```

There are at least `gamma|U_t|-b_rho` good unique rows.  At most `D` of
them can name the same site `s`, so at least
`(gamma|U_t|-b_rho)/D` sites of `U_t` are absent from the higher tail.
This is `(AUT2)`.  The fixed-`W` version is identical without the outer
Minkowski step.

For `(AUT3)`, use the shortened-code separation from
`dellm-shortened-core-unique-neighbor-proof` to choose `h`.  The exact
parity Loewner inequality for that row is
`P_s<=sum_(i in h-{s})P_i`, and every other site of `h` lies outside `W`.
