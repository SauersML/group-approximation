---
rg: 2
id: v-element-invariant-measures-live-on-the-periodic-part
kind: claim
title: Every atomless invariant measure of an element of V lives where the element is periodic, so V-elements normalize amenable actions only through automorphisms that are periodic on an invariant closed set, and never dilate a divisible group without fixed points
distinct_from:
  infinite-order-elements-of-v-have-hyperbolic-periodic-points: that says an infinite-order element of V has a hyperbolic periodic point; this says every atomless invariant measure avoids the non-periodic part, and applies it to normalizers of arbitrary amenable actions.
  no-free-q-odd-action-by-v-has-a-doubling-intertwiner: that is the degree-2 case (the intertwiner is a tail map Psi_f(g), and the action has free Z/p for infinitely many p); this is the degree-1 case (the intertwiner is a homeomorphism in V), for any amenable group and any automorphism, with no freeness hypothesis for divisible groups.
  rational-rotations-and-doubling-have-no-common-tree-coding: that restricts which rotations and coverings can be almost-automorphic in one coding; this places no hypothesis on the maps being normalized, only on the normalizing element.
  bs-conjugators-of-wandering-maps-have-invariant-compacta: that finds compact invariant sets for conjugators of wandering maps; this finds an invariant closed set on which the conjugator is periodic, for conjugators lying in V.
---

**ESTABLISHED** by `v-element-invariant-measures-live-on-the-periodic-part-proof` (lane bh-free-16,
09-18; elementary and self-contained; not reviewed; no priority claimed, although no statement of
this form was found on main).

**Setting.** `C = A^N` with `A = {0, …, d−1}` (`d >= 2`), and `V_d` is the group of homeomorphisms of
`C` given by finitely many prefix replacements. For `ψ ∈ V_d` put
`T(ψ) = ⋃_(n>=1) int Fix(ψ^n)`, the open, `ψ`-invariant set where `ψ` is locally periodic.

**Theorem.**
1. **Measure rigidity.** Let `ψ ∈ V_d` and let `μ` be an atomless `ψ`-invariant Borel probability
   measure. Then `supp μ ⊆ T(ψ)`, and `ψ^J` is the identity on a neighbourhood of `supp μ` for some
   `J >= 1`.
2. **Normalizers.** Let `L` be an amenable group, `ρ : L → Homeo(C)` any action, `α ∈ Aut(L)`, and
   `ψ ∈ V_d` with `ψ ρ(a) ψ^-1 = ρ(α(a))` for all `a`. Then there are a nonempty closed set `S ⊆ C`
   invariant under `ψ` and `ρ(L)`, and `J >= 1`, with `ψ^J|_S = id`. Hence `ρ(α^J(a) a^-1)` fixes `S`
   pointwise for every `a ∈ L`. If `ρ(L)` acts freely on `C`, then `α^J = id`.
3. **Divisible groups are never dilated.** If in 2 the group `L` is abelian and divisible (for
   example `Q`, `Q/Z[1/2]`, `Z(p^∞)`), and `α` is multiplication by an integer `m` with `|m| >= 2`,
   then `ρ(L)` fixes `S` pointwise. In particular `ρ(L)` has a global fixed point.

**Consequences.**
- **Q ⋊ ⟨2⟩ in V-coordinates.** Suppose `Q ⋊ ⟨2⟩` acts on a product `C × Y`. Suppose the dilation `δ`
  and all of `Q` act as skew products over `C`: `δ` with a base map that is a homeomorphism `ψ ∈ V_d`,
  and `q` with base maps `ρ(q) ∈ Homeo(C)` (arbitrary).
  Then `ρ(Q)` fixes a nonempty closed `ψ`-invariant set pointwise. This applies to `nV`, to every
  twisted Brin–Thompson group `SV_G` (a skew product over coordinate `k` whose base is a homeomorphism
  is locally a prefix replacement there), and to the free colour of `2V_τ`. So in a copy of
  `Q ⋊ ⟨2⟩` whose `Q` acts on some coordinate without a global fixed point, the dilation cannot act on
  that coordinate through a homeomorphic base map. With `no-free-q-odd-action-by-v-has-a-doubling-intertwiner`
  (the base is a 2:1 tail map), both one-coordinate shapes of the dilation are dead.
- **Baumslag–Solitar conjugators in V.** If `ψ ∈ V_d`, `a ∈ Homeo(C)` and `ψ a ψ^-1 = a^m`
  (`|m| >= 2`), apply 2 to `L = ⋃_k ψ^-k ⟨a⟩ ψ^k`. Then `a^(m^J − 1)` fixes pointwise a nonempty
  closed set on which `ψ` is periodic.
- **Calibration.** 1 fails for the odometer, which preserves Bernoulli measure and has infinite order.
  It also fails for the baker map of `2V`. So the only germs that can carry these configurations are
  odometer (Röver–Nekrashevych, Katsura–Exel–Pardo) germs, or hyperbolic germs that mix at least two
  coordinates. `2V_τ` has both kinds.

**Scope.** The normalizing element must lie in `V_d` (or `V_{d,r}`; the proof is the same). The
normalized maps `ρ(a)` are arbitrary homeomorphisms. The theorem says nothing about dilations that
mix coordinates at the base level.

## Lesson for general BH
Prefix-replacement germs are **measure-rigid**. The height cocycle `λ = |β| − |α|` of an element of
`V` (how many letters it writes minus how many it reads) forces every orbit to either repeat a cone
(periodic), contract a cone (a mass leak), or expand from a deep cone to a shallow one (a mass
leak). So invariant atomless mass sits only on the periodic part. Amenable groups that are normalized
with a twist always have a common invariant measure (Markov–Kakutani). So any infinite-order twist of
an amenable subgroup acting without finite orbits must be realised by non-V germs. That rules out
single-coordinate Thompson dynamics for divisible and dilated inputs (`Q ⋊ ⟨2⟩`, `Aff(Q)`,
`GL_n(Q)`). A host for them needs, in its germ groupoid, infinite-order bisections preserving an
atomless measure off their periodic part: odometer-type or multi-coordinate hyperbolic germs. This is
a one-line test for any proposed host.
