---
rg: 2
id: fano-incidence-recurrence-needs-a-nonstationary-two-cell
kind: claim
title: Fano point-line incidence cannot return the ghost defect through finite packet flow or finite-depth divisibility
distinct_from:
  fano-point-line-intertwiner-has-a-2-adic-defect: that supplies the determinant and mod-two rank defect; this proves that the defect is not yet a normalized-Hilbert-Schmidt return.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that treats arbitrary finite graphs of finite groups; this applies the theorem to the honest-point and ghost-line Fano sectors and combines it with the finite-depth arithmetic escape.
  consecutive-dyadic-splitting-does-not-report-dimension: that constructs the bulk-padding escape for a binary splitter; this identifies the same escape for any fixed finite list of incidence-lattice divisibility checks.
---

**ESTABLISHED NO-GO.**

Consider a compiler whose only distinction between the honest singleton orbit
and the ghost Fano-line orbit is the integral point-line incidence map of
`fano-point-line-intertwiner-has-a-2-adic-defect`.  Suppose its return hardware
uses finitely many finite-group charts and restriction edges, possibly together
with a fixed finite list of divisibility or Smith-coordinate checks.  Then this
hardware cannot by itself give a dimension-independent normalized-HS lower
bound on the ghost sector.

For the finite-chart part,
`finite-packet-graph-atlases-have-a-regular-stationary-flow` supplies positive
integer multiples of the regular representation at every chart whose edge
restrictions match exactly.  The selector subgroup is regular on that flow,
so every marked character occurs with positive multiplicity, including all
seven ghost line characters.  The point-line determinant defect is absorbed
by complementary packet types; bare restriction multiplicities do not expose
it.

For a fixed arithmetic depth, put the largest common incidence-lattice block
on a subspace whose dimension satisfies every required finite divisibility
condition and leave a residual subspace of bounded rank.  Evaluate the exact
packet and return tables on the bulk and complete the remaining generators
arbitrarily on the residual.  Every fixed word defect is supported on that
residual, hence is `O(d^(-1/2))` in normalized Hilbert--Schmidt norm as the
ambient dimension `d` grows.  This is the same padding mechanism proved
explicitly for dyadic splitting in
`consecutive-dyadic-splitting-does-not-report-dimension`; replacing powers of
two by the finitely many Smith divisors of the Fano matrix changes only the
bounded residual rank.

Therefore neither the determinant `24`, the mod-two rank drop, nor any fixed
finite repetition of those constraints makes the line-sector defect
extensive.  A live Fano recurrence must add a genuinely nonstationary
two-cell acting on edge intertwiner multiplicity spaces, a proper-corner
return, or a source-specific contextual holonomy.  It must also defeat bulk
padding at all depths with one finite presentation.  This is the same
load-bearing interface as `multiplicity-return-transducer`, not a replacement
for it.
