---
rg: 2
id: thompson-f-qi-to-thompson-t-resolved
kind: claim
title: "Bridson's related question resolved: decide whether Thompson's group F is quasi-isometric to Thompson's group T"
---

Part (c) of `zaremsky-2-04-f-quasi-isometric-to-f-times-z`. Decide whether
Thompson's group F is quasi-isometric to Thompson's group T. Zaremsky writes
"Surely not, but why not?"

This claim is the question. It is established only by a yes-route or a no-route
requiring the corresponding established answer claim; never by a
`requires: []` route. A yes-answer also answers part (f) yes.

## Attempts

- **Amenability.** T is not amenable (`thompson-t-is-not-amenable`) and
  amenability is a quasi-isometry invariant
  (`amenability-is-a-quasi-isometry-invariant`), both established with complete
  proofs. So an amenable F is not quasi-isometric to T
  (`thompson-f-not-qi-to-t-if-f-is-amenable`), and a yes-answer here makes F
  non-amenable (`thompson-f-nonamenable-if-qi-to-thompson-t`). Where it stands: the
  no-answer is reduced to the open root `thompson-f-is-amenable`.
- **Torsion, free subgroups, simplicity.** T has torsion, contains free groups and
  is simple, while F is torsion-free, has no free subgroups and has abelianization
  `Z^2`. Dies: none of these is a quasi-isometry invariant.
- **Coarse-embedding-monotone invariants.** F embeds in T. Whether T coarsely
  embeds in F is not known here; free groups coarsely embed in some amenable
  groups (quasi-isometrically embedded trees in Diestel–Leader graphs), so
  non-amenability of T gives no obstruction to such an embedding. Where it stands:
  open; a proof that T does not coarsely embed in F would answer this part no.
- **Cohomology with group-ring coefficients.** F has `H^*(F; ZF) = 0` in all
  degrees (`thompson-f-has-vanishing-zg-cohomology`, Brown–Geoghegan 1984,
  Theorem 7.2). T is of type F_∞ (Brown 1987), so a nonzero `H^k(T; ZT)` would
  answer this part no, given Gersten's quasi-isometry invariance (not yet
  imported). T is simple, so the ascending-HNN argument of Brown–Geoghegan does
  not apply to T. But Brown–Geoghegan announce (p. 368), about the finitely
  presented simple group of Thompson that they show is of type FP_∞: "We will show
  elsewhere that the simple FP_∞ group mentioned above also has this property",
  namely `H^*(G; ZG) = 0`. If that group is T, this line dies. Where it stands: the
  announced result is not yet located.
