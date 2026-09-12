---
rg: 2
id: fpbs-bernoulli-lower-bound-from-cycle-tails
kind: route
title: Use Bernoulli cycle compactness and the homological lower bound
target: fpbs-free-action-cost-at-least-bernoulli-cost
requires:
  - fpbs-bernoulli-cycle-tail-compactness
  - fpbs-graphing-cost-betti-cycle-dimension-identity
  - fpbs-short-cycle-edge-measure-vanishes-near-optimum
  - fpbs-amen2-betti-cost-input
artifacts:
  - research/artifacts/fpbs/docs/cost-cycle-structure.md
---

For the Bernoulli action put g=C(b)-1-beta_1 and
epsilon_n=c(Phi_n)-C(b). The dimension identity and short-cycle estimate give
g <= (L-1) epsilon_n + tau_L(Phi_n) for every fixed L>=3.
First let n tend to infinity, then L tend to infinity using the open
compactness premise. Thus g=0. The cost--Betti lower bound for any free
action alpha gives C(alpha)>=1+beta_1=C(b), as required. All costs and
the first Betti number are finite because Gamma is finitely generated.

This is a valid conditional implication, not a proof of its compactness
premise. It enters the existing sandwich route to universal Fixed Price,
which also retains the open countable-group passage.
