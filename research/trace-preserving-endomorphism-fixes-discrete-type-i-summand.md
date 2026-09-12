---
rg: 2
id: trace-preserving-endomorphism-fixes-discrete-type-i-summand
kind: claim
title: A trace-preserving endomorphism of a finite von Neumann algebra is an automorphism on its discrete type I summand
distinct_from:
  fd-isotypic-part-of-a-kazhdan-image-carries-no-wall: that locates walls away from the finite-dimensional isotypic part of the REPRESENTATION of the Kazhdan subgroup; this locates them away from the discrete type I part of the RELATIVE COMMUTANT, with no rigidity input.
  commutant-no-growth: that counts linear dimension of commutants of genuine finite-dimensional representations; this is the trace-weighted size-matching statement for arbitrary discrete type I algebras, including infinite direct sums.
artifacts:
  - research/artifacts/kt-wreath-double-re-unification-2026-09-11.md
---

**ESTABLISHED.**  Let `(R,tau)` be a finite von Neumann algebra with faithful
normal tracial state.  Let `z_d` be the central support of its minimal
projections, so `z_d R = direct_sum_i M_(k_i)` and `z_c R`, with
`z_c = 1 - z_d`, has no minimal projections.  Let `Phi: R -> R` be a unital
injective normal trace-preserving `*`-endomorphism.  Then

```text
Phi(z_d) = z_d,     Phi(z_d R) = z_d R,     Phi(z_c R) <= z_c R.
```

So if `Phi(R) != R`, the properness lives entirely in the diffuse summand
`z_c R`.

**Consequence for relative walls.**  For `sigma: G -> U(M)` (`M` finite with
faithful trace), `Lambda <= G` and `t Lambda t^(-1) <= Lambda`, the map
`Phi_t = Ad sigma(t)^*` is such an endomorphism of
`R = sigma(Lambda)' cap M`.  So `Phi_t` fixes the discrete type I part of `R`,
and a relative wall in the sense of `relative-wall-commutant-growth` must use
the diffuse part.  In particular, a relative commutant that is purely discrete
type I is normalized by every compressor.  This is the Hilbert--Schmidt form
of Kun--Thom's median size-matching wherever component sizes still exist.

DERIVATION
discrete-type-i-endomorphism-proof
