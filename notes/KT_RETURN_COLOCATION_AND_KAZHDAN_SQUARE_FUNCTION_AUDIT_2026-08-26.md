# Kun--Thom return co-location and Kazhdan square-function audit

Date: 2026-08-26

## Result

One vanished exterior return already forces a padding-stable carrier.  If

```text
y=(1-E_B)(T^*phi(gamma)T),
```

then `||y||_2^2>=1-(q+eta)^2`, `||y||_infinity<=2`, and the right support of
`y` has physical trace at least `[1-(q+eta)^2]/4`.  Thus `q,eta->0` gives a
quarter-trace support.  This directly excludes the vanishing-weight padding
escape in `vanishing-weight-block-carries-full-actor-edge-leakage` once the
reduced return condition is imposed.

## Kazhdan square-function audit

The tempting next move is to spread this return around the infinite Schreier
graph `Gamma/(t Gamma t^(-1))` and average the resulting actor residuals with
a fixed Kazhdan/heat-kernel weight.  Every fixed summable weighting of
uniformly bounded residuals which vanish pointwise also vanishes in total, by
dominated convergence, so a bound by that ledger would already exclude the
hypothetical microstates.

More importantly, the exact regular tracial model has exterior-return
expectation zero and zero actor defects while the same quasi-regular module
has a Kazhdan spectral gap.  Expansion propagates the return into that genuine
infinite module rather than charging a defect.  Thus a finite-dimensional
inequality is not ruled out, but it must use matrix-only no-growth,
integrality, or carrier authentication; it cannot follow from tracial
Kazhdan expansion alone.

The remaining useful targets are therefore narrower:

- make the quarter-trace support approximately reducing for a fixed actor
  packet;
- encode the moving family in one fixed group-algebra checksum; or
- prove a genuinely nonsummable/moving-radius estimate with a presentation
  mechanism that prevents its defect budget from escaping to infinity.

No local heavy computation was used.
