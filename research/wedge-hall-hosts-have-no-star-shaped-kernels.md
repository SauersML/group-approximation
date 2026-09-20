---
rg: 2
id: wedge-hall-hosts-have-no-star-shaped-kernels
kind: claim
title: In a wedge-designed Hall host for a one-sided free HNN extension, no kernel element has all of its valleys pinching directly
distinct_from:
  domain-exact-hnn-hosts-have-multivalley-kernels: that shows each kernel element has at least two peaks per period, for any domain-exact host; this shows that for the wedge design every kernel element also needs a cascading pinch, and it gives an exact decision procedure for two-peak kernels.
  bh-embeddability-survives-decidable-edge-hnn: that is the open permanence statement; this narrows what a kernel of the Hall-host map must look like in its one-sided free sub-case.
---

**ESTABLISHED** (lane proof, bh-last1-w21, elementary, not reviewed). No priority claimed.
Computation: `experiments/hall-host-kernels-2026-09-17/hall_kernel_census.py`.

## Setting

- **The input.** `G = F*_{φ : A -> B}`, with `F = <x, y>` free, `[F : A] = k < ∞` and
  `[F : B] = ∞`. This is the case `χ(G) = (k-1)(rk F - 1) >= 0`, which the `χ < 0`
  obstruction in the target's Attempts does not reach.
- **The host.** `H = Y*_{Φ : C_1 -> C_2}`, with `Y = F * <b>` and `[Y : C_i] = m`, where:
  - `C_1 ∩ F = A`, so the host is domain-exact;
  - `C_2 ∩ F = B̄ = B * L_0`, of finite index `n` in `F`;
  - `Φ|_A = φ`.

  `H` has free vertex group and finite-index edges, so it satisfies Boone–Higman
  (BLIW §12.5, as used in the target's Attempts).
- **The pullback.** `Q := Φ^{-1}(B̄) = A * S`, with `S := Φ^{-1}(L_0)`.
- **Wedge design.** Put `u_0 = q_0 · b` in the Schreier graph `Σ_1 = C_1\Y`, where `q_0` is the
  base vertex. Let `Σ_out` be the `F`-component of `u_0`, and take
  `S = b π' b^{-1}` with `π' <= Stab_F(u_0)`. Then the core graph `Γ_Q` of `Q` is the wedge
  `Δ ∨ Γ_S`. Here `Δ` is the core of `A` (the finite `F`-component of `q_0`), and `Γ_S` hangs
  off `q_0` through a single `b`-edge.
  Put `M := <F, S> = F * S`, so that `Q <= M`.

Conventions: `t a t^-1 = φ(a)` in `G`, and `s c s^-1 = Φ(c)` in `H`. The map `θ : G -> H` sends
`F` into `Y` by inclusion and `t` to `s`.

## Statement

Let `1 ≠ w ∈ ker θ`, written as a cyclically Britton-reduced word of `G`. Reduce `θ(w) = 1`
in `H` by Britton pinches. The pinches match the stable letters of `w` by a non-crossing
matching on the circle. Its dual tree has the complementary regions as vertices and the chords
as edges. Each chord has a **lower side**, read as `s^-1 X s` with `X ∈ C_2`, and an
**upper side**, read as `s X' s^-1` with `X' ∈ C_1`.

**Claim.** In a wedge Hall host, some chord of the reduction of `w` has a lower side that is
not a leaf region. So some valley pinch `s^-1 X s` has content `X ∉ F`: `X` contains
values that other stable letters have already pinched. We call this a **cascading pinch**.

Equivalently, no kernel element has a reduction in which every valley pinches directly, that
is, with content an `F`-word. In particular:
- no kernel element of shape `(t f t^-1 g)^p` has all of its valleys pinching directly, for
  any `p`;
- there is no two-peak kernel `t f_1 t^-1 f_2 t f_3 t^-1 f_4`.

## Proof

1. **`M` is a free product.** Take `p_i ∈ π' \ 1` and `f_i ∈ F`, nontrivial at interior
   positions. Then `f_0 (b p_1 b^-1) f_1 (b p_2 b^-1) ... ` is reduced in `Y = F * <b>`. So
   `<F, S> = F * S`, and `<A, S> = A * S`. Since `Φ` is an isomorphism,
   `Q = Φ^-1(B * L_0) = A * S`. Also `Q ∩ F ⊆ C_1 ∩ F = A`, so every element of `Q \ A`
   lies outside `F`.
2. **Claim A.** Let `r >= 1`, `z_i ∈ Q \ A` and `g_i ∈ F \ A`. Then
   `g_1 z_1 g_2 z_2 ... g_r z_r ≠ 1`.
   - Write each `z_i` in `A * S` normal form. It has at least one `S`-syllable, and it
     begins and ends with (possibly trivial) `A`-syllables `a_i` and `a_i'`.
   - In the cyclic product, each `g_i` merges with its two neighbouring `A`-syllables into
     `a'_{i-1} g_i a_i`, which lies in `F \ A` and so is nontrivial.
   - The result is a cyclically reduced word of `F * S` with at least `r` nontrivial
     `S`-syllables, so it is not `1`.
3. **Leaves.** A leaf region is bounded by one chord, so its content is an `F`-word.
   - A leaf on the upper side of its chord reads `t g t^-1` in `w`, with `g ∈ F`. It could
     pinch only if `g ∈ C_1 ∩ F = A`, which cyclic reducedness excludes. So there are no peak
     leaves.
   - A leaf on the lower side reads `t^-1 g t`, with `g ∈ (C_2 ∩ F) \ B = B̄ \ B`. It pinches
     to `z = Φ^-1(g) ∈ Q \ A`, since `Φ^-1(g) ∈ A` iff `g ∈ B`.
4. **The star case.** Suppose that every chord's lower side is a leaf.
   - A non-leaf region is then on the upper side of all its chords, so two non-leaf regions
     are never adjacent.
   - The tree has at least one chord, since `θ` is injective on `F`. A single chord would
     make its upper side a peak leaf, which step 3 excludes.
   - So the tree is a star. Its centre `R` is higher than all of its leaves.
5. **The contradiction.** Read the centre `R` around the circle.
   - It consists of `F`-arcs `g_i`, each read in `w` as a peak `t g_i t^-1`, so
     `g_i ∈ F \ A`.
   - Between consecutive arcs sit valley leaves, which pinch to `z_i ∈ Q \ A`.
   - After all the pinches, `θ(w)` is conjugate to `g_1 z_1 ... g_r z_r` in `Y`, and this
     must be `1`. That contradicts Claim A.

   So some chord's lower side is a non-leaf region: a cascading pinch. The shape
   `t f_1 t^-1 f_2 t f_3 t^-1 f_4` has two chords. A non-star tree for it would need a peak
   leaf, so this shape is excluded outright. ∎

Only the free-product structure `M = F * S` is used. The wedge design is one way to obtain it.

## The design of α matters: an exact two-peak test

For any Hall host (wedge or not), steps 3–5 show that a two-peak kernel exists iff there are
`z ∈ Q \ A` and `f_1, f_3 ∈ F \ A` with `f_1 z f_3 ∈ Q`. The witness is
`t f_1 t^-1 Φ(z) t f_3 t^-1 Φ(f_1 z f_3)^-1`.

The condition depends only on the cosets `A f_1` and `f_3 A`. For each of the `(k-1)^2`
choices it asks whether some path of the product graph `Γ_Q × Γ_Q`, between the two relevant
vertex pairs, has a label outside `A`. This is decidable from finite graphs, because the
labels form a coset of a finitely generated subgroup. The script checks whether every loop
generator and every tree label lies in `A`.

**Computation.** `experiments/hall-host-kernels-2026-09-17/hall_kernel_census.py`, standard
library only. Each run builds random Hall hosts with `F = F_2`. Run with arguments `20 0 2`
and `20 0 3`:

| design | `k = [F:A]` | hosts | hosts with a two-peak kernel | witnesses Britton-verified |
|---|---|---|---|---|
| naive (random `L_0`, random `α`) | 2 | 20 | 6 | 6 |
| naive | 3 | 20 | 6 | 6 |
| wedge | 2 | 20 | 0 | 0 |
| wedge | 3 | 20 | 0 | 0 |

In each case the explicit witness was reduced to `1` in `H` by an independent Britton reducer,
and it is cyclically reduced in `G`.

Run with arguments `4 2`, a brute-force census on `(+-+-)`, `(++--+-)` and `(+-+-+-)` words
with `F`-syllables of length at most 2 (sampled above 150000 per pattern), gives:
- naive hosts: 25 kernel words;
- wedge hosts: 0 kernel words out of 381936, 600000 and 600000 tested.

So "choose the complement map `α` arbitrarily" is false. Random Hall hosts do have kernels. At
the two-peak level, the wedge design is exactly what removes them.

## What remains, and why it does not close in one step

- **The gap.** A kernel element of a wedge host must contain a cascading pinch
  `s^-1 X s`, where `X ∈ C_2` involves values `Φ(y)` of peak regions or `Φ^-1(x)` of deeper
  valleys. These values lie in the `Φ(C_1 ∩ M) \ B̄` part of `C_2`, which the wedge design
  does not control. Controlling it needs a design for the next level, `Φ^-1` of the
  complement of `L_0`, and so on.
- **The tower is forced (finite-orbit obstruction).**
  - For any infinite `S <= C_1` with `<F, S> = F * S`, the subgroup `P = F * S` meets `C_2`
    in more than `B̄`. For `τ` in the base component of `Σ_2`, the finite `S`-orbit of `τ`
    has a nontrivial stabilizer in `S`, and conjugating it by the path `p_τ` gives elements
    of `(P ∩ C_2) \ B̄`.
  - Likewise `P ∩ C_1 ⊋ A * S` when `k >= 2`.
  - So a one-step HNN-subgroup criterion (`P ∩ C_1 = Q`, `P ∩ C_2 = B̄`) never holds for a
    Hall host. This agrees with the endless folds recorded in the target's bh-last1 Attempt.
  - By Tietze, `G ≅ M *_{Q -> B̄}`, and `ker θ` is the kernel of `M *_{Q -> B̄} -> H`. The
    obstruction to injectivity is exactly `(M ∩ C_1) \ Q` and `(M ∩ C_2) \ B̄`.
- **An explicit level-2 element.** `θ(G) ∩ Y` contains `Φ^-2(l)` for every `l` in the
  finite-index subgroup `Φ(S ∩ C_2)` of `L_0`, realised as `θ(t^-2 l t^2)`.
