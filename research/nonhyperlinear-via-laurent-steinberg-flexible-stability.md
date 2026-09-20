---
rg: 2
id: nonhyperlinear-via-laurent-steinberg-flexible-stability
kind: route
title: Flexible HS stability of the non-residually-finite Kazhdan group St_n(F_q[t,t^-1]) makes it non-hyperlinear
target: non-hyperlinear-group
requires:
  - laurent-steinberg-group-is-flexibly-hs-stable
  - laurent-steinberg-groups-are-deligne-type
  - hyperlinear-flexibly-hs-stable-group-is-residually-finite
---

Let `(n, q)` be given by `laurent-steinberg-group-is-flexibly-hs-stable`, so that
`Γ = St_n(F_q[t,t^-1])` is flexibly HS stable, with `n >= 3` and `q >= 3`.

- By `laurent-steinberg-groups-are-deligne-type` (items 2 and 3), `Γ` is finitely generated and
  not residually finite. The central symbol `{t,a}_α ≠ 1` lies in every finite-index subgroup.
- By `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, a finitely generated group that
  is hyperlinear and flexibly HS stable is residually finite.
- So `Γ` is not hyperlinear. It is a finitely generated non-hyperlinear group. ∎

**Comparison with `nonhyperlinear-via-free-algebra-lattice-flexible-stability`.**
- The open prerequisite here is implied by the open prerequisite there
  (`laurent-steinberg-stability-from-free-algebra-stability`), so this route is at least as close to
  the goal.
- The witness is concrete: a central extension of the S-arithmetic lattice
  `SL_n(F_q[t,t^-1])` by `Z/(q-1)`, of Deligne-type for `q` odd.
- `Γ` is finitely presented for `n >= 5` (by `steinberg-groups-of-fp-rings-are-fp-in-rank-five`,
  since `F_q[t,t^-1]` is a finitely presented ring), so the witness would also be finitely
  presented.

**Independent failure points.**
- A proof that `Γ` is hyperlinear, for every `n >= 3` and every `q >= 3`, kills this route.
- The same proof, at the matching `(A, n)`, also kills the free-algebra claim.
- A proof that `Γ` is not flexibly HS stable, for every `(n, q)`, also kills this route.
