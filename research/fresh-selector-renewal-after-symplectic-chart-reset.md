---
rg: 2
id: fresh-selector-renewal-after-symplectic-chart-reset
kind: claim
title: Renew the selector tuple after the common symplectic chart reset
distinct_from:
  fanizza-radical-charts-admit-common-symplectic-reset-subgroups: that merges the two chart simples on one full-matrix subgroup but retains the old selector center; this must install independent selectors for the next context.
  hnn-selector-chart-transport-preserves-mark-and-types: that transports an already prepared elementary-abelian selector chart; this must first privatize the old selector characters without changing the reset packet type.
---

Starting from the common reset subgroup `L_i` in `(CHR3)`, construct a fixed
finite-presentation incidence with the following properties.

1. Its restriction carries both crossed-product chart simples to two copies
   of the unique `L_i` spin type, with `O(sqrt(E))` loss after finite-group
   exactification.
2. The old context selector center is transported to private junk characters
   rather than identified with the next BCS variables.
3. A fresh commuting selector tuple is installed on the same fixed spin
   multiplicity carrier, with only the affine identifications required by the
   linear part of the Fanizza transition.
4. The incidence embeds the marked base and has bounded relator overlap under
   iteration.

The new symplectic reset removes the former four-branch Morita problem.  The
remaining issue is now center renewal: an HNN isomorphism may transport a
finite center but cannot quotient away old selector characters, while adding
an independent commuting packet naively tensors the Hilbert scale.  A valid
cell must move the old characters into private center while reusing, rather
than duplicating, the nondegenerate spin packet.

## Attempts

- Direct HNN transport preserves the old center and therefore does not create
  fresh selector coordinates.
- Tensoring an independent selector packet creates the desired coordinates
  but changes the packet scale, losing the fixed-scale return needed for
  normalized-HS payment.

## Attempts

- Identifying the old selector center directly with the next selector tuple
  imposes forbidden cross-context commutators and only permits an affine map
  of characters.
- Adding a completely independent next packet preserves freshness but tensors
  its spin factor with the reset packet, so the fixed-scale multiplicity wire
  is lost.  The active attack is a stable symplectic congruence that reuses the
  reset hyperplane while sending old central coefficients to private padding.
