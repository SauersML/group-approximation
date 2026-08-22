---
rg: 2
id: balanced-overlay-diffuse-square-function-newton
kind: claim
title: Correct the low-square-function balanced overlay by operator-row Newton iteration
distinct_from:
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that supplies an ordinary normalized-HS Jacobian gap at exact points; this must propagate the gap and control nonlinear remainders in the operator row-column square-function norm away from an already known exact base
  balanced-overlay-common-reducing-outlier-cut: that removes the high square-function spectral sector; this corrects the remaining diffuse block
---

OPEN.  On the complement of the common cut from
`balanced-overlay-common-reducing-outlier-cut`, use the operator bound on the
average residual square function to enter and run a dimension-independent
Newton or alternating-projection basin for the balanced occurrence
presentation.

## Attempts

The ordinary Jacobian gap at exact representations does not immediately
give this statement: the low block controls an **average row/column square
function** of residuals, not the operator norm of every residual and not the
operator distance to a previously identified exact representation.  The
promising route is to rewrite the character-block complete-graph inverse and
the equality-expander inverse as completely positive averages.  Such
averages are contractions in operator row/column norm, which would make the
quadratic remainder bounded by `O(sqrt(b))` times the current `2`-residual.
What is still unproved is an SOS/coercivity identity extending the exact
character-block Jacobian inverse to a tuple known only through this
square-function bound; assuming the exact character decomposition here
would be circular.
