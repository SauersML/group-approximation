---
rg: 2
id: finite-index-projective-core-proof
kind: route
title: Pass non-CE down finite index and cut the finite central character sector
target: finite-index-projective-core-yields-central-witness
requires:
  - finite-index-extensions-preserve-connes-embeddability
  - thom-central-corner-criterion
---

If `N` were Connes embeddable, finite-index invariance would make `M`
Connes embeddable.  Hence `N` is non-CE.

The multiplication and orthogonality assumptions in `(FPC1)` identify the
algebraic span of the `v_g` with the twisted group algebra
`C_omega[Gamma]`, preserving its canonical trace.  Completeness of the
basis identifies the von Neumann closure with `L_omega(Gamma)`, proving
`(FPC2)`.

Because `omega` is `mu_m`-valued, `(FPC3)` is a finite central extension.
The central character projection for the tautological character of `mu_m`
cuts `L(Gamma_tilde)` down to `L_omega(Gamma)`.  If `Gamma_tilde` were
hyperlinear, its group factor and every positive central corner would be
Connes embeddable, contradicting non-CE of `N`.

Finally, if `D` is finite-dimensional and `M` is an infinite-dimensional
finite factor, then `L2(M)` has infinite dimension as a right `D`-module.
Equivalently the Jones index `[M:D]` is infinite.  This applies to every
fixed finite context and packet algebra in the BCS source.  The only named
global alternative is the native BCS group of involutions, to which the
affine-support theorem applies.
