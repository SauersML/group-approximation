---
rg: 2
id: uniform-obstruction-from-corona-invisibility
kind: route
title: Compactness converts universal mark invisibility to one finite test
target: uniform-finite-mf-obstruction
requires: [literal-central-mark-corona-invisible]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralUniformObstruction.lean
---

## Why sufficient

If no finite set and positive threshold worked, choose successively better
finite-dimensional countermodels on an exhaustion of `E`.  Their coordinate
sequence defines a homomorphism to a norm matrix corona whose marked value
stays at operator-norm distance at least `1` from the identity.  This
contradicts the universal invisibility of the mark.  The conclusion is
dimension-independent but does not extract a numerical threshold.
