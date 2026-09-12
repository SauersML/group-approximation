---
rg: 2
id: sl3-swap-fold-square-from-unbalanced-torus-alone
kind: route
title: Charge the swap fold square using only the unbalanced torus word
target: sl3-swap-extension-has-defect-only-fold-square-rigidity
requires:
  - two-torus-closures-detect-denominator-multiplicity
---

**INVALIDATED PROPOSAL.**  Expand the unbalanced torus closure into its six
displayed lattice coefficients, use that the swap commutes with those
coefficients, and attempt to bound

```text
||(HSH^*S)^2-I||_2
```

only by the torus-word defect, the displayed swap--coefficient commutator defects,
and the separate rank-one doubling/Weyl-word defects.

`unbalanced-torus-and-swap-commutation-do-not-control-fold-square` gives an
exact `M_2` countermodel: every proposed input defect vanishes, while the fold
square is `-I` and its Gram defect is `1/8`.  The route therefore cannot be
repaired by improving constants, by replacing trace estimates with operator
equalities, or by completing either rank-one branch separately.

This does not invalidate the full arithmetic terminal.  A continuation must
use further lattice relations which force the two coefficient packages to
arise coherently from one approximate `SL_3(Z)` actor.  In light of the
separate bounded-depth rank-one firewalls, joint rank-two coherence is the
first surviving candidate in the simultaneous-outlier sector.
