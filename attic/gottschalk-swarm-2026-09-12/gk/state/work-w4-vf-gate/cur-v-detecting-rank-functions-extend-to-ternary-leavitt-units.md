---
rg: 2
id: v-detecting-rank-functions-extend-to-ternary-leavitt-units
kind: claim
title: A detecting rank function on the ternary group algebra of V yields one on the ternary Leavitt unit group moving minus one
distinct_from:
  thompson-v-ternary-rank-functions-are-augmentation: that is the V gate itself, that every rank function on F_3[V] is the augmentation; this is the transfer from V up to the unit group, which together with the V gate route would make the minus-one gate and the V gate equivalent.
  signed-thompson-z-moving-rank-functions-match-v-rank-functions: that transfers rank functions between V and the signed subgroup E ⋊ V, through a permutation embedding; this asks for the transfer to the whole unit group, where no permutation model exists.
  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one: that is link 1 of the ternary counterexample chain; this is the statement that link 1 costs exactly the V gate, no more.
artifacts:
  - research/artifacts/ternary-minus-one-gate-outside-signed-thompson-2026-09-12.md
  - research/artifacts/v-rank-extension-to-ternary-leavitt-units-2026-09-12.md
---

**OPEN.** Let `G_3 = L_(F_3)(1,2)^x`, `z = -1`. If `F_3[V]` carries a Sylvester matrix rank function detecting
every nontrivial element, then `F_3[G_3]` carries a Sylvester matrix rank function with `rk(1 - [z]) > 0`.

**What it would give.** The known direction is: a z-moving function on `F_3[G_3]` restricts to `E ⋊ V`, and then
to a detecting function on `V` (`signed-thompson-z-moving-rank-functions-match-v-rank-functions`). With this claim,
`sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one` and `thompson-v-ternary-rank-functions-are-augmentation`
become equivalent (route `v-augmentation-from-minus-one-gate-and-extension`). So link 1 of the ternary chain would
cost exactly the `V` gate: at least as hard as nonsoficity of `V`, and no harder.

**What it asks.** By `leavitt-prime-field-units-generated-by-v-and-one-transvection`, `G_3 = ⟨V, x⟩` with
`x = 1 + s_00 t_01`. So the claim asks whether a detecting rank function on `F_3[V]` can be extended, or replaced,
so that it also assigns consistent ranks to matrices involving `[x]`.

## Attempts

- 2026-09-12 `w5-c3-outside` (artifact Section 3).
  - **No embedding into V.** The signed Thompson transfer pulls a rank function back along an embedding
    `E ⋊ V -> V`. No such route exists for `G_3`. `G_3` has property (T) (`leavitt-gl-equals-el-and-perfect-unit-group`, every finite field).
    `PG_3` is infinite simple, as consumed in `ternary-leavitt-rank-models-move-z-proof`; not re-derived here. `V` has the Haagerup property
    (Farley; literature, not re-read locally). An infinite Kazhdan image cannot sit inside a Haagerup group, so
    the image of any homomorphism `G_3 -> V` is finite. That image is then trivial, because `G_3` is perfect and
    `PG_3` is infinite simple. So every homomorphism `G_3 -> V` is trivial, and pullback gives nothing.
  - **No permutation model for x.** `x` is unipotent of order `char F_3`. On any finite-subgroup algebra its rank
    data are Jordan types. A permutation module gives only the free and trivial profiles, and the natural
    evaluation profile is not V-invariant.
  - **Firewall.** Every sofic subgroup of `G_3` containing `z`, and every locally finite HNN datum, already carries
    an anti-central model (`anti-central-sofic-data-cannot-force-defect-submultiplicativity`). So a
    counterexample to this claim, meaning a detecting V-function that does not extend, must live on a nonsofic
    configuration involving `x` and depth-changing elements of `V`. The first such configurations are
    depth-mismatched transvection pairs.
  - **Where it stops.** No construction, and no obstruction to extension.
- 2026-09-12 `w6-v-extend` (`research/artifacts/v-rank-extension-to-ternary-leavitt-units-2026-09-12.md`).
  - **Reduction.** The claim is equivalent to "link 1 iff V gate". When `F_3[V]` has a detecting function, the claim
    fails iff link 1 holds (Corollary 5.1). No Hamming model of `V` extends, since `G_3` and `PG_3` are nonsofic.
    Averaging from `V` is unavailable, since `[G_3 : V]` is infinite and `G_3` has (T).
  - **Monomial lifts die.**
    - `X_ev = 1 + ([τ_00] − 1)[w]` fails `x^3 = 1` by at least `β/4`.
    - The Fock lift `X_F = 1 + [w] P_00^+ P_01^−` satisfies the sign, support and centralizer relations exactly. It
      fails the splitting `x = x_0 x_1` by at least `β/16` in every rank function on `F_3[E ⋊ V]`.
    - Both bounds come from Haar values on parity patterns.
  - **Classes.** `T(0,1)`, `x` and the three-cycle `c_3` are pairwise non-conjugate (via `ker n / im n` on `R_R`). On
    the code `{0,10,11}`, `T(0,10) T(10,11)` is conjugate to `c_3`, so an extension couples the profile of `x` to
    `rk_V`. Finite modules meet these constraints.
  - **Intertwiner.** `X_F` is the functorial Fock action at depth two, and `X_0 X_1` is that action at depth three.
    Splitting is a single-letter partial conjugation, so it kills lifts, not extensions
    (`level-unit-hnn-extensions-have-anti-central-rank-models`). For this candidate the gap is a commutant-valued
    cocycle `c(v, v')` on V's multiplication table.
  - **Where an obstruction must live.** At least two depth-changing letters, beyond disjoint commutation, generating
    a nonsofic subgroup with `z`. First candidates: `{T(0,1), T(1,0), T(1,00), T(00,1)}` and the Toeplitz commutator.
  - **Weakly finite version.** An extension injective on `V` gives either a nonzero weakly finite quotient of `S_−` or
    a weakly finite representation of `F_3[PG_3]` injective on `PG_3` (Proposition 5.2). Not decided.
  - **Where it stops.** No construction, and no obstructing relation identified.
