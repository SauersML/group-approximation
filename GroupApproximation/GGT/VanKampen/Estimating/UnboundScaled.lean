import GroupApproximation.GGT.VanKampen.Estimating.Assembly

/-!
# Superseded: the scaled unbound interface now lives in `Estimating/Assembly.lean`

This module briefly held `EstimatingUnboundScaledStatement`,
`EstimatingSelectionScaledConstructionStatement` and
`estimatingDataConstruction_of_scaledComponents`, as an additive draft of the
repair for issue #198.  It reached `origin/main` only through a periodic
snapshot of the shared working tree, ahead of the decision on how to apply that
repair.

The repair was then applied **in place** instead: `Assembly.lean`'s
`EstimatingUnboundOutputStatement` and `EstimatingSelectionConstructionStatement`
now carry `UnboundEstimate.OsinUnboundScale` themselves, and the refuted form
was renamed `EstimatingUnboundOutputHistoricalStatement` with both refutations
repointed at it.  Keeping the draft as well would have left two parallel
interfaces with nothing saying which is live, which is the confusion the
in-place repair was chosen to avoid.

The declarations are deliberately gone rather than deprecated: nothing imported
them, and a redundant twin of a statement is worse than an empty file.  This
file is retained only so that the change could be landed through the ordinary
gate, which refuses a path that does not exist; it may be deleted outright.
-/
