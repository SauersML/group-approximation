---
rg: 2
id: sln-z-thin-quasiregular-not-weakly-contained-in-fd
kind: claim
title: One element of C*(SL_n(Z)) has finite-dimensional norm below one but norm one on the thin quasi-regular representation
artifacts:
  - research/artifacts/sl4z-thin-corona-gap-reduction-2026-09-16.md
distinct_from:
  thin-hnn-regular-selected-module-is-profinite-discontinuous: that proves the selected HNN stable-letter module of the explicit SL_3(Z) pair is not weakly contained in the congruence-free finite-dimensional part; this gives, for every n >= 3, one fixed element x of the maximal C*-algebra of the lattice itself with a uniform finite-dimensional bound and norm one on l^2(Gamma/C).
  thin-leak-has-universal-fd-null-laplacian-witness: that builds a sequence y_N = (r-1)(1-Delta_C/L)^N with finite-dimensional norms tending to zero, which does not converge in C*(Gamma) because C is free; this element x = mu(1-p) is a single element, built from the Kazhdan projection of the ambient lattice.
  arithmetic-kazhdan-corner-is-fd-invisible: that uses the Kazhdan projection of the property (T) subgroup SL_3(Z) inside SL_3(Z[1/p]) and gets an element killed by every finite-dimensional representation; here the subgroup is a thin free group with no Kazhdan projection, and x has a uniform finite-dimensional gap rather than finite-dimensional norm zero.
  thin-profinite-selected-gap-lemma: that is a conditional transfer lemma about selected matrix-origin modules; this is an unconditional statement about the maximal group C*-algebra and one genuine representation.
---

Let `n >= 3`, `Gamma = SL_n(Z)`, and let `C = <g_1,...,g_4>` be the thin profinitely dense
free subgroup of `sln-z-thin-codense-tau-pair`, with symmetric generating list `F`
(`|F| = 8`).  Let `S` be a finite symmetric generating set of `Gamma` and `p` the central
Kazhdan projection of `C*(Gamma)`, the limit of `((1 + |S|^(-1) sum_s u_s)/2)^N`.  Put

```text
mu = (1/2)(1 + |F|^(-1) sum_(c in F) u_c),        x = mu (1 - p)  in C*(Gamma).
```

Then there is `epsilon > 0` such that:

1. `||rho(x)|| <= 1 - epsilon` for every finite-dimensional unitary representation `rho`
   of `Gamma`;
2. `||sigma_C(x)|| = 1` for the quasi-regular representation `sigma_C` on
   `l^2(Gamma/C)`, witnessed by the coset vector `delta_C`.

Consequences:
- No representation that weakly contains `sigma_C` is weakly contained in the
  finite-dimensional representations of `Gamma`.
- `C*(SL_n(Z))` is not residually finite-dimensional.  This is Bekka's theorem (Forum
  Math. 1999, not re-read here), reproved with an explicit witness.

The constant is `epsilon = kappa^2/32`, where `kappa^2 = h^2/8` and `h` is a uniform edge
expansion constant of the Cayley graphs `Cay(SL_n(Z/m), pi_m(F))` (Bourgain--Varju,
arXiv:1006.3365).

The element `x` is the test element for the corona crux
`sl4z-corona-reps-have-thin-relative-spectral-gap`.  There, the finite-dimensional bound
of item 1 is asked to survive in matrix corona representations of `SL_4(Z)`.
