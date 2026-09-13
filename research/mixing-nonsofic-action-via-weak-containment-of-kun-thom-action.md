---
rg: 2
id: mixing-nonsofic-action-via-weak-containment-of-kun-thom-action
kind: route
title: Find a mixing action weakly containing a Kun-Thom nonsofic action and conclude it is nonsofic
target: mixing-free-nonsofic-action-of-sofic-group
requires: []
---

Take the Kun--Thom group `G` with its infranormal Kazhdan pair `Γ <= G`, and look for a free
mixing action `Y` of `G` that weakly contains the nonsofic generalized Bernoulli action
`({0,1},fair)^(G/Γ)`. Since actions weakly contained in sofic actions are sofic (folklore,
Alpeev arXiv:1706.01864, p. 2), `Y` would be nonsofic. Weak containment does not preserve
mixing, so the non-mixing seed is not an immediate obstruction.

Dead: invalidated by `weak-containment-is-blind-to-kazhdan-fixed-algebras`. `Γ` is infinite
and Kazhdan, so on a mixing `Y` it is ergodic, hence ergodic on every action weakly contained
in `Y`; the seed has nonconstant `Γ`-fixed functions.
