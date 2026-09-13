---
rg: 2
id: thompson-f-quasi-retracts-onto-f-times-f-resolved
kind: claim
title: "Bridson's easier question resolved: decide whether F x F is a quasi-retract of Thompson's group F"
---

Part (e) of `zaremsky-2-04-f-quasi-isometric-to-f-times-z`. Decide whether there
are coarsely Lipschitz maps `i: F × F -> F` and `r: F -> F × F` with `r ∘ i` at
bounded distance from the identity.

This claim is the question. It is established only by a yes-route or a no-route
requiring the corresponding established answer claim; never by a
`requires: []` route. A yes-answer to part (b) gives a yes-answer here.

## Attempts

- **Retraction onto the stabilizer of 1/2.** With `i` the inclusion of
  `Stab_F(1/2) = F_[0,1/2] × F_[1/2,1]`, a retraction is a coarsely Lipschitz map
  onto this subgroup that is close to the identity on it. No homomorphic
  retraction exists: every proper quotient of F is abelian (Cannon–Floyd–Parry),
  and F × F is not abelian. Retractions built from a section of the orbit map
  `g ↦ g^{-1}(1/2)` need conjugations by the section to be uniformly
  length-controlled on `Stab_F(p)`; natural sections fail (see
  `thompson-f-qi-to-f-times-f-resolved`). Where it stands: open.
- **Root-split tree-pair retraction.** Restricting a reduced tree-pair diagram to
  the left and right subtrees of the root caret, and padding with carets to match
  leaf counts, is not coarsely Lipschitz: right multiplication by `x_0` rotates
  the root and moves an arbitrarily large subtree across the split. Dies.
