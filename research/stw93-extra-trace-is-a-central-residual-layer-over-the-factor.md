---
rg: 2
id: stw93-extra-trace-is-a-central-residual-layer-over-the-factor
kind: claim
title: An extra XCIII trace is a central residual GNS layer with scalar factor expectation
distinct_from:
  stw93-residual-tracefree-iff-unique-trace: that equivalence extends a bounded residual trace to the ambient algebra; this theorem describes the von Neumann support of the residual ideal inside the GNS representation of any resulting extra trace.
  stw93-singular-trace-needs-finite-central-cuntz-capacity: that theorem extracts a finite-capacity spectral cut; this theorem simultaneously identifies the factor-compatible central support which carries every such cut in the GNS closure.
  stw93-super-mcduff-tracial-central-quotient: that theorem identifies the canonical tracial quotient; this theorem concerns a hypothetical second trace on the norm residual extension and does not assert its existence.
artifacts:
  - research/artifacts/stw93-residual-factor-section-audit-2026-08-30.md
---

Use the split extension `E=R+s(Q)` from
`stw93-residual-extension-splits-over-factor`.  Let
`sigma` be a normalized ordinary trace on `E`, let

```text
M_sigma=pi_sigma(E)'',             N_sigma=pi_sigma(s(Q))'',
```

and let `z_sigma` be the central projection in `M_sigma` satisfying

```text
closure^weak(pi_sigma(R))=z_sigma M_sigma.              (6)
```

Then `N_sigma` is a II_1 factor with its canonical trace, and

```text
E_(N_sigma)(z_sigma)=sigma_bar(z_sigma) 1_(N_sigma),    (7)
```

where `sigma_bar` is the normal GNS trace and `E_(N_sigma)` is the
trace-preserving conditional expectation.

Moreover

```text
z_sigma!=0  iff  sigma|R!=0  iff  sigma is noncanonical. (8)
```

Thus any extra ordinary trace produces a nonzero central residual layer over
the same hyperfinite factor section, and that layer is invisible to the
factor except through the scalar density in `(7)`.  If `a in R_+` is charged
by `sigma`, a positive spectral cut of `a` has finite Cuntz capacity and its
GNS support lies under `z_sigma`.

This is a necessary structure theorem, not an existence theorem for
`z_sigma` and not a proof of quasitrace linearity.
