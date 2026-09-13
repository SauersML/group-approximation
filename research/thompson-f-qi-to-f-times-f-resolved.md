---
rg: 2
id: thompson-f-qi-to-f-times-f-resolved
kind: claim
title: "Bridson's related question resolved: decide whether Thompson's group F is quasi-isometric to F x F"
---

Part (b) of `zaremsky-2-04-f-quasi-isometric-to-f-times-z`. Decide whether
Thompson's group F is quasi-isometric to F × F with the product word metric.

This claim is the question. It is established only by a yes-route or a no-route
requiring the corresponding established answer claim; never by a
`requires: []` route. A yes-answer also answers part (e) yes.

## Attempts

- **Coarse-embedding-monotone invariants.** F × F is the stabilizer of `1/2` in F
  (elements supported in `[0,1/2]` times elements supported in `[1/2,1]`), so F
  and F × F embed in one another as subgroups. Every invariant monotone under
  coarse embeddings or under regular maps takes the same value on both. Dies.
- **Cohomology with group-ring coefficients.** If `H^*(F; ZF) = 0` in every degree
  (Brown–Geoghegan 1984, to be re-read), then `H^*(F × F; Z[F × F]) = 0` by the
  Künneth formula. Dies if confirmed.
- **Coset-bundle retraction.** A quasi-retraction `F -> Stab_F(1/2)` of the form
  `g ↦ g·s(g^{-1}(1/2))^{-1}`, for a section `p ↦ s(p)` with `s(p)(p) = 1/2`, is
  coarsely Lipschitz exactly when conjugation by `s(p)` carries short elements of
  `Stab_F(p)` to short elements of `Stab_F(1/2)` uniformly in `p`. The natural
  sections (powers of `x_0` for `p = 2^{-k}`, balanced dyadic maps) add about
  `log k` or `k` carets to elements supported far from `p`. This form of retraction
  looks blocked; a proof that no section works is not written down. Where it
  stands: heuristic only.
