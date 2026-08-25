---
rg: 2
id: induce-actor-microstates-across-finite-packet-action
kind: route
title: Regularly induce a canonical actor microstate through every finite packet covariance row
target: finite-packet-actions-have-positive-fiber-microstates
requires:
  - sofic-halo-products-preserve-hyperlinearity
---

Use the left regular packet blocks and place on the block `p` the actor
microstate precomposed by `alpha_(p^(-1))`.  Packet permutation implements
the crossed covariance.  Defects and traces are finite averages of the
corresponding actor quantities.  The packet restriction is exactly regular,
so every nonzero packet projection retains positive trace.  Tensoring a fixed
positive BCS/BTB atom supplies the protected active fiber and contradicts any
positive compressed relator floor.
