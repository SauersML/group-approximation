---
rg: 2
id: covariant-model-satisfies-cross-context-radical-relators
kind: claim
title: The covariant completeness model satisfies both cross-context radical relators
artifacts:
  - experiments/cross_context_radical_relator_audit.py
  - research/artifacts/cross-context-radical-relator-audit-2026-08-23.md
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

This was proposed as the only completeness-side obligation of the relator
route `three-chart-return-from-cross-context-relators`.  The present claim is
still purely about completeness.  The route's separate soundness assertion
is not automatic from adjoining the relators and is now invalidated by
`two-raw-radicals-fail-common-symplectic-reset`.

## Why no edge can ever carry the bit

The obvious alternative — enlarge the reset subgroup so the label word is
edge-carried and the events become type-level — is impossible, not merely
unattempted.  On a forbidden sector the chart-`i` label word is the
`delta_i`-invariant raw radical direction, i.e. the unique solution of
`A_f(a) w = 0`, `ell_i(w) = 0`; by the block form `(CHR1)` this is exactly
the radical line of `B_i(a)`.  The nondegeneracy certificate `(CHR2)`
requires `phi_i` to be nonzero on every `B_i`-radical line, so
`phi_i(w) = 1` and `w` lies outside `W_i = ker(phi_i)` for every admissible
hyperplane.  The Morita merge is therefore structural: chart `i`'s own bit
can never live in chart `i`'s edge subgroup, the two labels always fuse over
`L_i`, and any constraint pinning the endpoint events must be imposed
transversally to the graph-of-groups data — which is what `(CCR1)` does.
This also confirms the relators are genuinely non-Bass--Serre: they are not
consequences of any legal edge enlargement.

## Proof plan

1. Express each context transport as the composite of the established
   cells: the `(CHR3)` chart restriction, the two-copy Weyl derivative
   reset `(WDR2)`, gauge doubling, and the affine Clifford packet edge.
2. Track the two shares of each radical bit through the doubling.  The
   logical (shared) coordinate is the orbit product `w^((0)) w^((1))` of
   `(WDR3)`-type, and gauge flips fix logical products by
   `gauge-doubling-gives-selector-flip-symmetries`, so the gauge-orbit
   covariantization preserves whatever alignment the finite cells give.
3. Use `fanizza-radical-tuples-have-stabilizer-shears` for the full finite
   packet audit.  With `alpha=ell_1`, `beta=ell_3`, and `gamma=ell_2`, the
   two opposite lifted `GL_2(F_2)` shears fix respectively every
   `r_(a,0)` and every `r_(a,1)`.  Equivariant reset hyperplanes therefore
   align the complete indexed outside-word tuples on every selector block,
   including satisfying blocks, with zero central correction.
4. Marked-base separation descends because the aligned model satisfies
   the relators exactly and already separates the marked word.

The former finite obstruction in step 3 is closed.  What remains before this
claim itself may be established is to write the three complete context
transport unitaries in the countably amplified HALT representation and check
that their two relative loops are the two stabilizer shears supplied by that
finite audit.  The regular-orbit reset construction is equivariant, but the
current canonical presentation has not yet recorded this simultaneous choice
of the three full installation/uninstallation composites.

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
- **Satisfying sectors audited.**  A relator is global.  On a
  satisfying sector the words `r_(a,j)` are not sector-central (the form
  `A_f(x)` is nondegenerate there), so `(CCR2)` demands that the honest
  comparison loop fix a *non-central* packet word.
  `fanizza-radical-tuples-have-stabilizer-shears` now checks exactly this:
  64 satisfying comparison blocks, together with all forbidden blocks and
  central-root corrections.  The deferred step is only to identify the
  honest full comparison loops with those two audited shears.
- **The consumer route has a separate soundness no-go.**  Exact outside-word
  conjugacy does not put both endpoint words in the reset multiplicity
  commutant.  `two-raw-radicals-fail-common-symplectic-reset` proves that a
  nondegenerate codimension-one reset has only one commuting radical line.
  It therefore invalidates the present `three-chart-return-from-cross-context-relators`
  route even if the completeness choice in this claim is eventually written
  down.
- **Marked-base separation after the quotient.**  By
  `kleene-completeness-needs-only-a-nontrivial-exact-representation`,
  it suffices that the covariant model itself survives: if it satisfies
  `(CCR1)` exactly it descends to the quotient and still separates the
  marked word.  So this claim is genuinely a single computation in one
  named representation, not a new stability question.
