---
rg: 2
id: leavitt-presentation-double-instability-proof
kind: route
title: Lift the corona images of the free generators; amalgam relations give convergence on the kernel, injectivity gives separation off it
target: leavitt-presentation-double-forces-restriction-instability
requires:
  - symmetric-double-weak-mf
  - binary-leavitt-elementary-group-is-simple
  - universal-leavitt-el4-nonsofic
---

`F` is free, hence residually finite, so `P = F *_K F` is weak MF by
`symmetric-double-weak-mf`: there is an injective `*`-homomorphism
`Phi : C^*(P) -> prod_n M_(d_n) / (+)_n M_(d_n)`.  Unitaries of the corona
lift to unitaries of `prod_n M_(d_n)`; lift the images of a free basis
`x_1..x_m` of the first vertex copy `i_0(F)` to unitaries `u_n(x_j)` and of
the second copy `i_1(F)` to `v_n(x_j)`.  Since `F` is free these define exact
homomorphisms `u_n, v_n : F -> U(d_n)`, and for every word `f`, the sequences
`(u_n(f))_n` and `(v_n(f))_n` lift `Phi(i_0(f))` and `Phi(i_1(f))`.

For `k in K` one has `i_0(k) = i_1(k)` in `P`, so the two lifts differ by an
element of `(+)_n M_(d_n)`: `||u_n(k) - v_n(k)||_op -> 0`.  For `f_0 notin K`
the word `w_0 = i_0(f_0) i_1(f_0)^(-1)` is reduced of length two in the
amalgam, hence `w_0 != 1`, and injectivity of `Phi` gives
`||Phi(w_0) - 1|| = limsup_n ||u_n(f_0) v_n(f_0)^* - 1||_op =: c > 0`, i.e.
`limsup ||u_n(f_0) - v_n(f_0)||_op = c`.  Statement (3) is the finite-window
form of (2).  The hypotheses on `Q` are used only to make the kernel `K`
proper (`Q != 1`) and to match the consumer's setting; the argument works for
any normal `K` in a residually finite `F`.
