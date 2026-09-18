---
rg: 2
id: faithful-pair-finite-steinberg-actions-need-noncentral-k2
kind: claim
title: If K_2(N,R) is central in St_N(R) for a Q-algebra R with a Leavitt pair, then St_N(R) has infinite, infinitely generated centre and no faithful action with finitely many orbits of pairs
distinct_from:
  type-a-actors-have-no-infinite-virtually-central-subgroup: that is the general necessary condition on a faithful actor with finitely many pair orbits; this applies it to Steinberg groups of Leavitt-type Q-algebras, where the rational scalars supply the infinite centre once K_2 is central.
  leavitt-scalar-commutators-block-fp-central-quotients: that shows central quotients of Leavitt unit groups and of E_N(R) are not finitely presented; this concerns the Steinberg group itself as a permutation actor, and the faithful images of its actions.
  steinberg-leavitt-resolvent-groups-have-no-type-a-action: that is the flat verdict for St_N(R_L), which also needs centrality of K_2(N,R_L); this is the unconditional implication.
---

**ESTABLISHED** by `faithful-pair-finite-steinberg-actions-need-noncentral-k2-proof`
(lane proof, elementary, not independently reviewed; no novelty claimed).

## Statement

Let `R` be a unital ring containing `Q` as a unital subring. `Q` is then
central: the integers are central, and the inverse of a central unit is central.
Suppose `R` has a Leavitt pair `s_1, s_2, t_1, t_2`, with `t_i s_j = δ_ij` and
`s_1 t_1 + s_2 t_2 = 1`. Let `N >= 3`, let `Γ = St_N(R)`, let
`π : Γ -> E_N(R)` be the canonical map, and let `K = K_2(N,R) = ker π`.

**If `K` is central in `Γ`**, then:

1. `Z(Γ) = π^-1(Z(E_N(R)))`, and it contains `π^-1(Q^x · I_N)`.
2. `Z(Γ)` is infinite and not finitely generated.
3. Let `Γ` act on a set `S` with finitely many orbits of two-element subsets,
   and let `M` be the kernel. Then `M ∩ Z(Γ)` has finite index in `Z(Γ)`. In
   particular the action is not faithful, and `Γ` has no action of type (A),
   whatever its stabilizers are.
4. In item 3, if `M <= Z(Γ)`, then the faithful image `Γ/M` is not finitely
   presented.

**Unconditional form.** If `St_N(R)` acts faithfully with finitely many orbits
of two-element subsets, then `K_2(N,R)` is not central in `St_N(R)`.

## Instances

- `R_L` (`leavitt-resolvent-ring-is-fp-and-contains-q`). `St_N(R_L)` is
  finitely presented for `N >= 5` (`steinberg-groups-of-fp-rings-are-fp-in-rank-five`)
  and contains every `GL_n(Q)` (`one-steinberg-group-contains-every-gl-n-q`).
- Every ring `S` with `Q` and a Leavitt pair, as in
  `one-steinberg-group-contains-every-gl-n-q`.

## Scope

- This constrains `St_N(R)` only as the actor. It says nothing against
  embedding `St_N(R)` in a different type (A) actor. There, by corollary 2 of
  `type-a-actors-have-no-infinite-virtually-central-subgroup`, every central
  element of infinite order of `St_N(R)` must acquire infinitely many
  conjugates.
- The centrality hypothesis is open for `R_L`
  (`k2-central-in-steinberg-groups-of-leavitt-resolvent-ring`).
