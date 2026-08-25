---
rg: 2
id: hnn-stable-letter-rounding-proof
kind: route
title: Spectral sector functions of the Haar letter are exact centered order-m letters, and Voiculescu uniqueness identifies the amalgam
target: hnn-stable-letter-rounds-to-finite-order
requires:
  - hnn-hyperlinearity-is-amalgamated-free-haar-unitary
---

Assume `G = A *_C (C x Z)` hyperlinear.  By condition (2) of
`hnn-hyperlinearity-is-amalgamated-free-haar-unitary` there is a
trace-preserving embedding of `N = L(A)` into a tracial matrix
ultraproduct `M` and a Haar unitary `k in B' cap M`, `B = L(C)`, with
`E_B(k^n) = 0` for `n != 0` and `(N, W*(B,k))` free with amalgamation
over `B`.

**Rounding.**  Fix `m >= 2` and let `f_m : T -> T` be the sector
function `f_m(e^(i theta)) = omega^j` for
`theta in [2 pi j/m, 2 pi (j+1)/m)`, `omega = e^(2 pi i/m)`.  Put
`s = f_m(k)` (Borel functional calculus in the von Neumann algebra `M`).
Then:

- `s^m = 1` exactly, since `f_m^m = 1` pointwise; and `s` has EXACT order
  `m` with balanced spectrum: the spectral measure of the Haar unitary
  `k` is the Lebesgue measure, each sector has mass `1/m`, so
  `tau(s^r) = (1/m) sum_j omega^(jr) = 0` for `r != 0 mod m`.  For
  `m = 2`, `s` is a self-adjoint unitary of trace zero.
- `s in B' cap M`: `k` commutes with `B` exactly in `M`, hence so does
  every Borel function of `k`.
- `E_B(b s^r) = b tau(s^r)` for `b in B`: on `W*(B,k) = B (x) W*(k)`
  the trace-preserving conditional expectation onto `B` is `id (x) tau`,
  and `s^r in W*(k)`.  In particular `E_B(s^r) = 0` for `r != 0 mod m`,
  so the `B`-valued distribution of `W*(B,s)` is exactly that of
  `B (x) L(C_m)` with its canonical trace.
- `(N, W*(B,s))` is free with amalgamation over `B`: `W*(B,s) subseteq
  W*(B,k)`, and every alternating word of `E_B`-centered elements drawn
  from `N` and `W*(B,s)` is such a word for the pair `(N, W*(B,k))`, whose
  `E_B` vanishes by the assumed freeness.  (Freeness passes to
  intermediate subalgebras containing the core -- immediate from the
  definition.)

**Identification.**  By Voiculescu's uniqueness of the tracial
amalgamated free product (the same argument as the converse direction of
`hnn-amalgamated-free-haar-unitary-proof`, with `L(C_m)` in place of
`L(Z)`): the joint `B`-valued distribution of `(N, W*(B,s))` under
freeness is determined by the two marginal `B`-valued distributions,
which are those of `L(A) supseteq L(C)` and `B (x) L(C_m)`.  Hence

```text
W*(N, s)  ~=  N *_B (B (x) L(C_m))  =  L(A *_C (C x C_m))  =  L(G^(m)),
```

trace-preservingly, inside the matrix ultraproduct `M`.  A group von
Neumann algebra embeds trace-preservingly into a matrix ultraproduct iff
the group is hyperlinear (Radulescu, as used throughout the lane), so
`G^(m)` is hyperlinear.  No padding, no defect, no dimension change was
used at any step: `s` is a function of `k` on the same space.
