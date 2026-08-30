---
rg: 2
id: stw93-residual-gns-central-support-proof
kind: route
title: Take the weak ideal support and average it onto the factor section
target: stw93-extra-trace-is-a-central-residual-layer-over-the-factor
requires:
  - stw93-residual-extension-splits-over-factor
  - stw93-residual-tracefree-iff-unique-trace
  - stw93-singular-trace-needs-finite-central-cuntz-capacity
artifacts:
  - research/artifacts/stw93-residual-factor-section-audit-2026-08-30.md
---

The weak closure of a two-sided ideal in a von Neumann algebra is a weakly
closed ideal.  Hence there is a central projection `z_sigma in M_sigma`
with `(6)`.

The trace `sigma` restricts along `s` to the unique normalized trace of the
II_1 factor `Q`.  The restriction of `pi_sigma` to `Q` is normal for its
tracial representation.  Indeed, for GNS vectors of the form
`xi=pi_sigma(e)Omega` and `eta=pi_sigma(f)Omega`, tracial Cauchy--Schwarz
bounds the coefficient of `x in Q` by a constant times
`sigma(s(x)*s(x))^(1/2)=||x||_(2,Q)`.  Such vectors are dense.  Thus the
representation is a normal amplification of the tracial representation of
`Q`, and its von Neumann closure `N_sigma` is again a II_1 factor.  The
finite inclusion `N_sigma subset M_sigma` has a unique trace-preserving
conditional expectation.

Since `z_sigma` is central in `M_sigma`, the functional

```text
x -> sigma_bar(z_sigma x),             x in N_sigma,
```

is a normal trace on the factor `N_sigma`.  It must equal
`sigma_bar(z_sigma)` times the normalized factor trace.  This identity is
equivalent to `(7)` by the defining property of the conditional
expectation.

If `z_sigma=0`, then `pi_sigma(R)=0`, so `sigma` vanishes on `R` and factors
through `E/R=Q`; factor trace uniqueness makes it canonical.  Conversely,
the canonical trace kills `R` and has `z_sigma=0`.  If `sigma|R` is nonzero,
then some `r in R_+` has positive value, so `pi_sigma(r)!=0` and
`z_sigma!=0`.  This proves `(8)`.

Finally, if `sigma(a)>0` for `a in R_+`, choose `epsilon>0` with
`sigma((a-epsilon)_+)>0`.  The dimension-function argument in
`stw93-singular-trace-needs-finite-central-cuntz-capacity` gives finite
capacity of that cut.  Since its image belongs to the weak closure of
`pi_sigma(R)`, its support projection is dominated by `z_sigma`.
