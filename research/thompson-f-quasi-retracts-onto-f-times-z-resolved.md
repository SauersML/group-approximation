---
rg: 2
id: thompson-f-quasi-retracts-onto-f-times-z-resolved
kind: claim
title: "Bridson's easier question resolved: decide whether F x Z is a quasi-retract of Thompson's group F"
---

Part (d) of `zaremsky-2-04-f-quasi-isometric-to-f-times-z`. Decide whether there
are coarsely Lipschitz maps `i: F × Z -> F` and `r: F -> F × Z` with `r ∘ i` at
bounded distance from the identity (Alonso's quasi-retraction).

This claim is the question. It is established only by a yes-route or a no-route
requiring the corresponding established answer claim; never by a
`requires: []` route. A yes-answer to part (a) gives a yes-answer here, and a
no-answer here gives a no-answer to part (a).

## Attempts

- **Splitting off the Z factor.** Take `i` to be the inclusion of
  `F_[0,1/2] × <z>` with `z` supported in `[1/2,1]` and `z'(1) = 2`. The slope
  homomorphism `g ↦ log_2 g'(1)` is a retraction onto the Z factor that vanishes
  on `F_[0,1/2]`. What remains is a coarsely Lipschitz `q: F -> F_[0,1/2]` with
  `q(h z^k)` uniformly close to `h`. Where it stands: no such `q` is known; the
  conjugation isomorphism `F ≅ F_[0,1/2]` by the scaling `x ↦ x/2` is not close to
  the identity on `F_[0,1/2]`.
- **Obstructions inherited by quasi-retracts.** Quasi-retracts inherit type F_n
  (Alonso 1994) and Dehn functions are bounded by those of the ambient space; all
  groups here are of type F_∞ with quadratic Dehn function. Dies: no obstruction.
  If `H^*(F; ZF) = 0` (Brown–Geoghegan, to be re-read), coarse cohomology gives no
  obstruction either.
