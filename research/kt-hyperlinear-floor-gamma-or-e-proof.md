---
rg: 2
id: kt-hyperlinear-floor-gamma-or-e-proof
kind: route
title: The root-invisible alternative is empty because root-polynomial overgroups of SL_r(A) are SL_r(A)
target: kt-hyperlinear-floor-is-gamma-or-normal-closure
requires:
  - kt-hyperlinear-floor-is-root-invisible-laurent-overgroup
  - kt-compressor-commutant-collapse-is-all-or-nothing
  - sl-r-polynomial-has-no-root-free-laurent-overgroup
---

Notation is as in the target. Write `A = R_+`. Two external facts are used.

* **Suslin (1977):** `SL_r(A) = E_r(A) = Gamma` for `r >= 3`.
* `E = EL_r(R) <= SL_r(R)`.

The general theorem is `sl-r-polynomial-has-no-root-free-laurent-overgroup`. Its
statement for `f = x_1⋯x_d` reads: "every subgroup `H` with `SL_r(A) <= H <= SL_r(R)` and
`H ∩ U_12(R) = U_12(A)` equals `SL_r(A)`." Call this (NRF).

## Part 1

By `kt-hyperlinear-floor-is-root-invisible-laurent-overgroup` (a), we have
`Gamma <= K_Gamma <= E`.

Suppose `E ⊄ K_Gamma`. Part (d) of that claim gives `K_Gamma ∩ U_12(R) = U_12(A)`; its
proof, Section 4, derives this from the wall alternative. So (NRF) applies to
`H = K_Gamma <= E <= SL_r(R)`, and gives `K_Gamma = SL_r(A) = Gamma`. Otherwise
`K_Gamma = E`.

## Part 2

Let `h in E \ Gamma` lie in `K_Gamma`. Then `K_Gamma != Gamma`, so `K_Gamma = E` by
Part 1.

## Part 3

For `Delta >= Gamma`, `W_Delta` is hyperlinear iff `K_Gamma <= Delta`. This is Section 0
of the proof route `kt-hyperlinear-floor-is-root-invisible-laurent-overgroup-proof`.

If `K_Gamma = Gamma`, every `W_Delta` with `Delta >= Gamma` is hyperlinear.

If `K_Gamma = E`, then every `Delta` with `E ⊄ Delta` fails `K_Gamma <= Delta`, so
`W_Delta` is non-hyperlinear, and in particular `W_Gamma` is.

With Part 1 this gives the four-way equivalence. The normal closure of `Gamma` in `G` is
`E`, since conjugating `e_ij(1)` by `SL_d(Z)` gives every `e_ij(x^n)`. So
`kt-pair-hyperlinear-floor-below-normal-closure` is the statement "some such `W_Delta`
is hyperlinear", and it is therefore equivalent to `W_Gamma` hyperlinear, that is, to
`hyperlinear-wreath-model` for the pair.

For the model statement we use the description in Section 0 of that route. `K_Gamma` is
the intersection, over canonical CE actor models `σ` and projections
`p in σ(Gamma)' ∩ M`, of the commutation stabilisers of `p`.

* If `K_Gamma = E`, condition 4 of `kt-compressor-commutant-collapse-is-all-or-nothing`
  holds in each such model. This is Section 5, case 1, of the trichotomy route.
* Conversely, suppose condition 4 holds in every such model. Then `σ(E)` commutes with
  every such `p`, so `E <= K_Gamma`.

## Part 4

`Gamma^sat` is a subgroup of `G` containing `Gamma`, by the Engine paragraph of
`kt-compressor-commutant-collapse-is-all-or-nothing`. Let `H = Gamma^sat ∩ E`. Then
`Gamma <= H <= E <= SL_r(R)`. By that theorem, exactly one of two cases holds for `π`.

* The equivalent conditions hold. Condition 4, `C_0 = C_U(π(E))`, says that `π(E)`
  commutes with `C_0`, so `H = E`.
* The wall alternative holds. It gives `Gamma^sat ∩ U_12(R) = U_12(A)`, hence
  `H ∩ U_12(R) = U_12(A)`. By (NRF), `H = SL_r(A) = Gamma`. ∎

Part 1 also follows from Part 4 applied to canonical models, but the route above is
the shortest.
