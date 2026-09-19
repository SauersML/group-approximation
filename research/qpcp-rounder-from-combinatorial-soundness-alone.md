---
rg: 2
id: qpcp-rounder-from-combinatorial-soundness-alone
kind: route
title: Extract a rounder from combinatorial soundness and local energy accounting alone
target: amplified-hamiltonian-has-a-constant-cost-rounder
requires: [locality-preserving-constant-combinatorial-gap]
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

**Dead.**  Invalidated by `coherent-shear-is-combinatorially-invisible`.

The tempting argument.  Combinatorial soundness already says that exact
satisfaction off `S` forces `|S| >= beta m`.  A state of small energy
violates few constraints "on average", so round each violated constraint to a
fault, count the faults, and the count should be `O(energy)`.

Why it fails.  On the 2-local chain `h_t = (I - SWAP_(t,t+1))/2` with the
sheared product state `rho_D`, the total violation is `Theta(1/D)` while any
exactification preserving the endpoint marginals must declare at least one
fault, so the cost constant is at least `2D/theta^2`.  Exact fault count and
soft energy are decoupled by a factor growing with the depth.  The
deformation responsible is a coherent infinitesimal rotation of the frame:
there is no discrete violated constraint corresponding to it, and a
combinatorial assignment cannot perform it, so an argument whose only content
is a conversion of energy into a count of violated constraints cannot see it.

Note the family in the kill has combinatorial gap `0`, which is the point:
combinatorial soundness is a NO-side hypothesis about exactly-satisfying
states and is silent about arbitrary low-energy states.  Bridging that
silence is what `local-syndrome-port-domination-at-each-gadget` is for.
