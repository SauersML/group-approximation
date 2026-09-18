---
rg: 2
id: thompson-t-identities-hold-in-circle-orbit-wreath-overgroups
kind: claim
title: For every group B and every T-orbit X of the circle, every overgroup of T inside the unrestricted wreath product B^X ⋊ T satisfies all mixed identities of T; in particular T × B does, and every mixed identity of T becomes trivial when its constants are deleted
requires:
  - thompson-t-identities-hold-on-linearized-blow-ups
distinct_from:
  thompson-t-identities-hold-on-linearized-blow-ups: that treats groups of homeomorphisms of a derivative blow-up; this realizes wreath products with a free lamp group inside such a blow-up and transfers to arbitrary lamp groups, which need not act on anything.
  thompson-t-identities-one-word-basis-over-cantor-overgroups: that is about overgroups acting on the Cantor set or circle extending the standard T; the overgroups here are abstract, since B is arbitrary, for instance finite or torsion.
  bffhz-q32-forces-finitely-based-mixed-identities: that makes a finite basis over overgroups necessary for Question 3.2; this removes products T × B and circle-orbit wreath products as witnesses against such a basis at T.
---

**ESTABLISHED** by the proof below. Lane proof by bh-ffwz-q59, 2026-09-18. It is elementary and
not reviewed, and no priority is claimed.

## Statement

Let `X ⊂ S^1` be a single `T`-orbit, rational or irrational, with `T` acting as on the circle. Let
`B` be any group, and let `W = B^X ⋊ T` be the unrestricted permutational wreath product, where
`(t·f)(ξ) = f(t^{−1}ξ)`.
1. Every `M` with `T ≤ M ≤ W` has `J_k(M; T) = J_k(T)` for every `k ≥ 1`.
2. In particular, `T × B` has this property, embedded as `{(const_b, t)}`.
3. **Deletion.** For every `w ∈ J_k(T)`, the word `ŵ ∈ F_k` obtained by deleting all constants
   is trivial.

Finite unions of orbits follow by the product closure (E) of
`circle-overgroups-of-thompson-t-satisfy-all-its-mixed-identities`.

## Proof

**Step 1: lamps in a blow-up, for a free lamp group.** Let `C_X` be the derivative blow-up of
`S^1` along `X`, with `T` acting as in `thompson-t-identities-hold-on-linearized-blow-ups`. Fix
`p_0 ∈ X`, and let `Z_0 ≤ Homeo+(I_(p_0))` be a group of homeomorphisms that commute with the
action of the stabilizer `T_(p_0)` on `I_(p_0)`.
- **Irrational orbit.** `T_(p_0)` acts trivially on `I_(p_0)`, so any `Z_0` works.
- **Rational orbit.** `T_(p_0)` acts by one-sided dyadic scalings `s ↦ 2^a s` for `s < 0` and
  `s ↦ 2^b s` for `s > 0`. The homeomorphisms that fix `0` and commute with `s ↦ 2s` on each half
  form, after `log_2`, two copies of the lift group `Homeo~+(S^1)`.
- **A free lamp group exists in both cases.** `Homeo~+(S^1)` contains a free group of countable
  rank, because a free subgroup of `Homeo+(S^1)` lifts: a central extension of a free group by
  `Z` splits. So take `Z_0 ≅ F_∞`.
- **Transporting the lamps.** For `p = t p_0` put `Z_p = t Z_0 t^{−1}` on `I_p`. This is well
  defined because `T_(p_0)` centralizes `Z_0`.
- **The embedding.** For `f ∈ F_∞^X`, let `Λ_f` act on each gap `I_p` by `f(p) ∈ Z_p`, and as
  the identity off the gaps. It is a monotone bijection, hence in `Homeo+(C_X)`, and
  `t Λ_f t^{−1} = Λ_(t·f)`. So `F_∞^X ⋊ T` embeds in `Homeo+(C_X)` with `T` acting by
  derivatives.
- **Conclusion for free lamps.** By `thompson-t-identities-hold-on-linearized-blow-ups`, every
  overgroup of `T` in `F_∞^X ⋊ T` satisfies all of `J_k(T)`.

**Step 2: arbitrary lamp groups.** Let `w ∈ J_k(T)` and `y_i = (f_i, t_i) ∈ W`.
- **Evaluating.** `w(y) = (λ, w(t)) = (λ, 1)`. For each `ξ ∈ X`, the lamp `λ(ξ)` is obtained by
  following the finite trajectory of `ξ` through the letters of `w`. It is `ω_ξ(z)`, for a word
  `ω_ξ` in finitely many symbols `z_(i,η)` standing for the values `f_i(η)`.
- **Testing with free lamps.** Replace these values by distinct free generators of `F_∞`, and
  put `1` elsewhere. By Step 1, the resulting tuple in `F_∞^X ⋊ T`, which has the same
  `T`-parts, kills `w`. So `ω_ξ` is the trivial word.
- **Conclusion.** Hence `λ(ξ) = 1` for every `B`, and `W` satisfies `w`. Subgroups containing `T`
  inherit this. That proves items 1 and 2.

**Step 3: deletion.** In `T × B`, `w(t, b) = (w(t), ŵ(b)) = (1, ŵ(b))`. Take `B = F_k` and
`b` its basis. Item 2 gives `ŵ = 1` in `F_k`. ∎

## What survives as a witness against the one-word basis `E`, or any finite basis at T

Direct products and wreath products along circle orbits are dead, for every lamp group, including
finite and torsion groups that act on no line. Still alive:
- split extensions `L ⋊ T` by modules that are not permutation modules on circle orbits, for
  example `Z[T/H]` with `H` not a point stabilizer;
- amalgams and HNN extensions over subgroups that contain every constant of `E`;
- blow-ups whose gap actions are not germ actions.

A remark on logic:
- A counterexample to `E` alone would not refute a finite basis, since a larger finite `W` could
  still work.
- A finite basis would not answer Question 3.2 either. It is only the necessary condition of
  `bffhz-q32-forces-finitely-based-mixed-identities`.

## Lesson for general BH

- **Mixed identities of a circle-type host are blind to lamps attached along its orbits.** Any
  lamp group whatsoever can be tested through a free one. A free lamp group sits in a blow-up
  gap, commuting with the stabilizer germs.
- **Which overgroups can separate identities.** Only overgroups whose new elements interact with
  the host through something other than orbit points can do it. That leaves modules induced from
  non-point stabilizers, and amalgams.
- **The general tool.** A property of `J(G)` that holds on free-lamp wreath products along orbits
  holds on all of them, via the substitution "distinct values ↦ free generators".
