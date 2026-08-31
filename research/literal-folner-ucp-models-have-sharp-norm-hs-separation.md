---
rg: 2
id: literal-folner-ucp-models-have-sharp-norm-hs-separation
kind: claim
title: The literal Folner u.c.p. witnesses have an exact operator-versus-Hilbert--Schmidt boundary gap
distinct_from:
  literal-group-factorization-property: that establishes existence of u.c.p. Hilbert--Schmidt models for the canonical trace; this computes, on one fixed pair, the exact defect of the concrete models used in that proof.
  literal-canonical-trace-hyperlinear-not-quasidiagonal: that is the global nonexistence of arbitrary quasidiagonal models; this is a sharp formula for the particular Folner-compression models and does not claim that every amenability model has the same boundary.
artifacts:
  - GroupApproximation/Analysis/QuasiRegularCompression.lean
  - GroupApproximation/Analysis/LocallyRFByIntAmenableTrace.lean
  - GroupApproximation/Analysis/LocallyRFByIntAction.lean
  - research/artifacts/literal-factorization-folner-ucp-2026-08-30.md
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

**ESTABLISHED.**  Let `u` be the stable-letter unitary in `C*_(max)(E)`.
For the `N`-level window `F={0,...,N-1}`, let

```text
Phi_F : C*_(max)(E) -> M_(N|Q|)
```

be the quasi-regular compression map at a stage of
`literal-fp-via-folner-rf-core`, with `Q` its residual packet quotient.  Then

```text
||Phi_F(uu*)-Phi_F(u)Phi_F(u*)||       = 1,
||Phi_F(uu*)-Phi_F(u)Phi_F(u*)||_(2,tr)= N^(-1/2),
tr(Phi_F(uu*)-Phi_F(u)Phi_F(u*))       = N^(-1).
```

The same formulas hold with `u` and `u*` reversed.  Thus these explicit
factorization witnesses become multiplicative in normalized
Hilbert--Schmidt norm at the exact rate `N^(-1/2)`, while their
operator-norm defect on the fixed two-element test never decreases at all.

This calculation is independent of the finite quotient `Q` and the collected
normal-coordinate subgroup.  There is no Arveson extension in the formal
construction.  It gives a sharp,
dimension-free explanation of why the new factorization proof does not
accidentally produce quasidiagonality.
