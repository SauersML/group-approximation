---
rg: 2
id: covariant-model-satisfies-cross-context-radical-relators
kind: claim
title: The covariant completeness model satisfies both cross-context radical relators
distinct_from:
  s3-radical-chart-returns-to-fresh-context: that demands the full return incidence with reset discipline and transport properties; this is one computation in one named representation after the return is quotiented by two explicit relators. It is also distinct from any equivariant-edge closure, which eliminates independent rotations structurally before any quotient.
  three-chart-affine-clifford-return-incidence: that is the target common-marginal statement for finite tuples; this is the single completeness-side obligation of the relator route into it.
  fresh-selector-renewal-after-symplectic-chart-reset: that installs the fresh selector tuple and privatizes the old center; this adds no new edge and only asks whether two comparison loops fix the two raw radical words in the covariant model.
---

Fix a Fanizza predicate `f`, its marked forbidden atoms `a`, the fixed
zero-one raw radical basis words `r_(a,0),r_(a,1)` of `(SER1)`, and the
affine Clifford return presentation assembled by the established reset
chain, with the three conjugate chart transports `u_1,u_2,u_3`
implementing the contextual branch choices.  Let `(alpha,beta)` and
`(beta,gamma)` be the two context pairs whose endpoint marginals must
agree in `(RNS1)`, with `beta` the crossed context.  Adjoin, for every
marked atom `a`, the two **cross-context radical relators**

```text
u_alpha r_(a,0) u_alpha^(-1) = J^(c_(a,0)) u_beta  r_(a,0) u_beta^(-1),
u_beta  r_(a,1) u_beta^(-1)  = J^(c_(a,1)) u_gamma r_(a,1) u_gamma^(-1),
                                                        (CCR1)
```

where the fixed central exponents `c_(a,j)` are the twist-functional
differences `(ell_i-ell_j)(r_(a,*))` prescribed by `(RTC2)`, so that both
sides transport the same physical raw-radical coordinate.  Equivalently,
writing `l_(alpha beta) = u_beta^(-1) u_alpha` for the comparison loop,
`(CCR1)` says each loop **centralizes its shared raw radical word up to
the fixed central character**:

```text
l_(alpha beta) r_(a,0) l_(alpha beta)^(-1) = J^(c_(a,0)) r_(a,0).  (CCR2)
```

The claim: the countably amplified exact HALT gauge-orbit covariant
representation satisfies every relator in `(CCR1)` **exactly**, and the
quotiented presentation still admits an exact representation separating
the marked base word.

This is the only completeness-side obligation of the relator route
`three-chart-return-from-cross-context-relators`.  Soundness needs
nothing here: in any finite tuple the relators are part of the energy
`E`, and violation of the common endpoint marginals is charged to `E`
directly.

## Attempts

- **Common fresh vertex instead of relators.**  Gluing the three reset
  cells to one fresh finite vertex identifies only irreducible type
  counts; the edge intertwiners `I tensor V_i` rotate the endpoint
  projections independently.  This is the recorded failed shortcut of
  `three-chart-affine-clifford-return-incidence` and is what `(CCR1)`
  is designed to bypass: the relators are not graph-of-groups data for
  any edge, so representation-ring integer flows do not see them, and
  the stationary-flow obstruction of
  `three-radical-twist-crossed-products-have-uniform-scale` does not
  apply.  They are exactly the "non-Bass--Serre return relation" that
  node asks for.
- **Full sharing is deliberately avoided.**  Imposing all six
  identifications (every context shares both coordinates) would force a
  joint classical value table for all three matchings and, through the
  old selector center, exactly the forbidden cross-context commutators
  recorded in `fresh-selector-renewal-after-symplectic-chart-reset`.
  `(CCR1)` imposes only the two agreements `(RNS1)` actually uses; the
  old selector characters stay private.
- **Satisfying sectors are the live risk.**  A relator is global.  On a
  satisfying sector the words `r_(a,j)` are not sector-central (the form
  `A_f(x)` is nondegenerate there), so `(CCR2)` demands that the honest
  comparison loop fix a *non-central* packet word.  Two mitigations are
  in place but not yet a proof: the radical basis is independent of the
  selector values (SER1), so no sector-dependent dephasing enters the
  word itself; and the relator family is `S_3`-equivariant by `(SER2)`,
  so the obligation reduces to one orbit representative per atom.  The
  deferred step is to compute the honest loop `l_(alpha beta)` in the
  gauge-orbit covariant model — it is a composition of one context
  uninstallation and one installation over the same fresh carrier — and
  check its action on the full packet, not only on the radical plane.
- **Marked-base separation after the quotient.**  By
  `kleene-completeness-needs-only-a-nontrivial-exact-representation`,
  it suffices that the covariant model itself survives: if it satisfies
  `(CCR1)` exactly it descends to the quotient and still separates the
  marked word.  So this claim is genuinely a single computation in one
  named representation, not a new stability question.
