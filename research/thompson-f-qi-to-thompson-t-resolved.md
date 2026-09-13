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
  degrees (Brown–Geoghegan 1984, to be re-read). T is of type F_∞ (Brown 1987), so
  `H^*(T; ZT)` is a quasi-isometry invariant (Gersten). A nonzero `H^k(T; ZT)` for
  some `k` would answer this part no. T is simple, so the ascending-HNN argument
  that works for F does not apply to T. Where it stands: `H^*(T; ZT)` not computed
  here yet.
