---
rg: 2
id: odometer-lift-central-extensions-of-v-subgroups-into-2v-tau
kind: claim
title: Odometer lift - a central Z-extension of a subgroup of V whose class dies on the action groupoid embeds in the F_infinity simple group 2V_tau, with the centre acting as the odometer
distinct_from:
  odometer-2v-is-fp-simple-and-contains-bs12: that constructs the host 2V_tau and puts BS(1,2), Q and 2V in it; this is a permanence statement that uses that host for central extensions, and gives Thompson's lifted group T-bar as an instance.
  tbar-embeds-in-laurent-leavitt-unit-group: that puts T-bar in the unit group of L tensor F_2[t^{+-1}]; this puts T-bar in a group of Cantor-set homeomorphisms, by making the deck translation an odometer.
  boone-higman-closed-under-finite-direct-products: that is closure under products; this is closure under one class of central extensions by Z, for inputs inside V.
---

**ESTABLISHED** (lane proof, elementary, not reviewed). No priority is claimed; the
instance `T̄` is already known to satisfy Boone–Higman (Belk–Hyde–Matucci, `T̄ ≤ VA`,
as recorded in `aff-q-embeds-in-fp-simple-group`). What is new here is the general
mechanism and a second host.

## Setting

- `C = {0,1}^N`. `V` acts on `C` by prefix replacements. `2V_τ` is the group of
  `odometer-2v-is-fp-simple-and-contains-bs12`: homeomorphisms of `C × C` that, on the
  rectangles `C(p_i) × C(w_i)` of a finite partition, have the form
  `(p_i x, w_i y) ↦ (p'_i τ^{n_i}(x), w'_i y)`, with `τ` the binary odometer
  (`x ↦ x + 1` on `Z_2 ≅ C`, digits least significant first). By that node `2V_τ` is
  of type `F_∞` and simple.
- For `Q ≤ V`, the **action groupoid** is `Q ⋉ C`. A function `k : Q × C → Z` is
  *locally constant* if each `k(q, ·)` is locally constant.

## Statement

Let `Q ≤ V` and let `1 → Z → Q̃ → Q → 1` be a central extension, written as
`Q̃ = Z ×_ε Q` with product `(m,q)(m',q') = (m + m' + ε(q,q'), qq')` for a normalized
2-cocycle `ε`. Suppose the class of `ε` **dies on the action groupoid**: there is a
locally constant `k : Q × C → Z` with `k(1, ·) = 0` and

    ε(q, q') = k(q', y) − k(qq', y) + k(q, q'y)     for all q, q' ∈ Q, y ∈ C.     (∗)

Then

    Φ(m, q)(x, y) = (τ^{m + k(q,y)}(x), q y)

is an injective homomorphism `Q̃ → 2V_τ`. The central generator `(1,1)` goes to
`s = τ × id`. In particular `Q̃` satisfies Boone–Higman.

Condition (∗) says exactly that the image of `[ε]` under
`H^2(Q; Z) → H^2(Q ⋉ C; Z)` vanishes, where the right side is continuous groupoid
cohomology with coefficients in the constant sheaf `Z`.

## Proof

1. **Homomorphism.** For `(m,q), (m',q')`:
   `Φ(m,q)Φ(m',q')(x,y) = (τ^{m' + k(q',y) + m + k(q,q'y)}x, qq'y)` and
   `Φ((m,q)(m',q'))(x,y) = (τ^{m + m' + ε(q,q') + k(qq',y)}x, qq'y)`. These agree by (∗).
   Each `Φ(m,q)` is a bijection with inverse `Φ((m,q)^{-1})`, and is continuous because
   `k(q,·)` is locally constant. So `Φ` is a homomorphism into `Homeo(C × C)`.
2. **Injective.** If `Φ(m,q) = id`, then `qy = y` for all `y`, so `q = 1` since `V` acts
   faithfully. Then `τ^m = id` because `k(1,·) = 0`, so `m = 0`, since `τ` has infinite
   order.
3. **Lands in `2V_τ`.** Fix `q`. There are complete prefix codes `(w_i)`, `(w'_i)` with
   `q(w_i z) = w'_i z`. Since `k(q,·)` is locally constant and `C` is compact, refine to
   a finite cylinder partition `C = ⊔_j C(v_j)` with each `v_j` extending some `w_i`,
   say `v_j = w_i u_j`, and `k(q,·) ≡ n_j` on `C(v_j)`. Put `v'_j = w'_i u_j`. Then on
   the rectangle `C × C(v_j)`,
   `Φ(m,q)(x, v_j z) = (τ^{m + n_j} x, v'_j z)`.
   This is the defining form of `2V_τ`, with `p_i = p'_i` the empty word. ∎

## Instance: Thompson's lifted group `T̄`

Let `T̄` be the group of homeomorphisms `f` of `R` with `f(t+1) = f(t) + 1` that descend
to elements of Thompson's `T` on `R/Z`. It is the central extension of `T` by the
integer translations. Cantorize `R` at the dyadic rationals as `Z × C`, where `C` is
`[0,1)` Cantorized. `T ≤ V` acts on `C`, and each `f` acts on `Z × C` by
`f(n, w z) = (n + k_f(w), w' z)` on finitely many cylinders. Here the integer jump
`k_f` depends only on the cylinder and not on `n`, by periodicity. So
`k(f, y) := k_f(y)` is locally constant and satisfies (∗), which is just associativity
of composition on `Z × C`. The dense equivariant inclusion `Z ⊂ Z_2` extends the action
to `Z_2 × C`. Hence **`T̄ ≤ 2V_τ`**, with the deck translation becoming the odometer
`s = τ × id`.

Consequences:
- `2V_τ ⊇ T̄ ⊇ Q`, by Belk–Hyde–Matucci's copy of `Q` in `T̄` built from lifts of
  rotations. This gives a second, independent copy of `Q` in `2V_τ`, alongside
  `rationals-embed-in-brin-thompson-group-2v` and the root tower of item 5 of the host
  node. In the `T̄` copy the odometer `s` is the image of translation by `1`, so `s` is
  divisible inside `T̄` itself.
- `\widetilde{PSL_2(Z)} ≤ T̄ ≤ 2V_τ`, since `PSL_2(Z)` acts on `RP^1` by
  projective elements of `T` (piecewise-`PSL_2(Z)` model of `T`). This is the rank-one
  shadow of the Deligne test case (see Limits).

## Limits (where the lift stops)

- **Inputs must lie in `V`.** The lift needs the quotient `Q` to act on `C` by prefix
  replacements and needs a locally constant trivialization `k` on `Q ⋉ C`. For the
  Deligne lattice `Γ̃ → Sp_{2n}(Z)` (`deligne-lattice-satisfies-boone-higman`), `n ≥ 2`,
  `Sp_{2n}(Z)` has property (T) and `V` has the Haagerup property (Farley), so
  `Sp_{2n}(Z) ⊄ V`. The lift would need a host of `Sp_{2n}(Z)` that is a full group of
  prefix-type homeomorphisms, with an extra odometer colour that keeps finite
  presentation and simplicity. The natural candidate is a piecewise-`Sp_{2n}(Z)` group of
  the Lagrangian Grassmannian, lifted to its universal `Z`-cover as `T̄` lifts `T`.
  Its finite presentation is the same kind of open question as survey Remark 5.5
  (Thurston's PIP groups).
- **Classes that do not die.** (∗) fails whenever `[ε]` survives on `Q ⋉ C`. The lemma
  says nothing then; for example it does not decide which central extensions of
  Thompson's `F` (`H^2(F; Z) ≅ Z^2`) embed in `2V_τ`.
- **One odometer.** Iterated central extensions would need several odometer colours.
  Finite presentation and simplicity of such multi-odometer full groups is not
  established here.
