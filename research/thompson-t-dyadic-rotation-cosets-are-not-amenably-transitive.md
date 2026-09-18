---
rg: 2
id: thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive
kind: claim
title: The action of Thompson's T on the cosets of its dyadic rotation group is not locally amenably transitive; equivalently some finite set of elements of F cannot be twisted by dyadic rotations into an amenable subgroup of T
distinct_from:
  jz-question-5-for-thompson-t-implies-f-nonamenable: that proves the action is LAT if F is amenable (so this claim implies F is nonamenable); this asks whether it fails to be LAT outright.
  liouville-action-criteria-cannot-decide-thompson-f-amenability: that notes that for the regular F-set the set {e, x_0, x_1} forces H = F, so non-LAT is the root itself; here the extra dyadic twists in T may make non-LAT strictly stronger than the root.
  thompson-f-is-not-amenable: that is the target; this claim implies it through thompson-f-not-amenable-via-rotation-cosets-of-thompson-t and may be strictly stronger.
---

**OPEN.** Notation is as in `jz-question-5-for-thompson-t-implies-f-nonamenable`: `X = T/R_D`, and
`F → X`, `f ↦ fR_D` is a bijection.

**Statement.** There are `f_2, …, f_n ∈ F` such that no amenable subgroup `H ≤ T` has the points
`R_D, f_2R_D, …, f_nR_D` in one orbit.

**Reformulation (proved here).** `T ↷ X` is LAT iff for all `f_2, …, f_n ∈ F` there are dyadic
`θ_2, …, θ_n` with `⟨f_2ρ_{θ_2}, …, f_nρ_{θ_n}⟩` amenable. So the claim says: some finite `S ⊆ F` has
every rotation twist `{fρ_{θ_f} : f ∈ S}` generating a nonamenable subgroup of `T`.
- *Proof.* Translating a finite set by `g ∈ T` conjugates the subgroups that put it into one orbit, and
  conjugates of amenable groups are amenable. So it suffices to treat finite sets containing the base point
  `R_D`, and every point is `fR_D` for a unique `f ∈ F`. If `R_D` and `f_iR_D` lie in one `H`-orbit then `H`
  contains some `h_i` with `h_iR_D = f_iR_D`, i.e. `h_i = f_iρ_{θ_i}`, and `⟨h_i⟩ ≤ H` is amenable.
  Conversely `⟨f_iρ_{θ_i}⟩` itself maps `R_D` to each `f_iR_D`. ∎
- With all `θ_i = 0` and `S = {x_0, x_1}` the twisted group is `F`. So if `F` is amenable the claim is false
  (as the established node says), and if `F` is not, the claim asks whether twisting can always escape
  into amenable subgroups.

**Why it is a genuine prerequisite and not the root renamed.** It implies `thompson-f-is-not-amenable`. It can
fail while `F` is nonamenable: that happens iff for every finite `S ⊆ F` some rotation twist of `S` lands in an
amenable subgroup of `T`, and then `T ↷ X` is an unconditional finitely presented counterexample to
Juschenko–Zheng's Question 5 (Theorem A of `amenably-coupled-actions-admit-symmetric-liouville-measures`).
So either answer is new: "true" settles the root negatively; "false" answers Question 5 negatively for finitely
generated groups without deciding the root.

**Structure of the candidates (proved here).** Every amenable `H ≤ T` preserves a probability measure `ν` on
`S¹`. If `ν` has atoms, the atoms of maximal mass form a finite invariant set and its pointwise stabilizer
`H_0` has finite index. If `ν` has no atoms, the rotation number is a homomorphism on `H` and its kernel `H_0`
fixes `supp ν` pointwise (it preserves every fiber of the semi-conjugacy `x ↦ ν[0, x)` to the identity). Either
way `H` has a normal subgroup `H_0` fixing a point of `S¹`, with `H/H_0` finite or abelian. So a twist of `S`
escapes only if it generates a group that is, up to a finite or abelian quotient, inside a point stabilizer of
`T`, which for dyadic points is a conjugate of `F`.

## Attempts

- **2026-09-18 (swarm-0917-w8-w8-f-last1, census-computation).** Twist search for `S = {x_0, x_1}`, the smallest
  case, with `A = x_0ρ_a`, `B = x_1ρ_b` and `a, b ∈ 2^{−K}Z/Z`
  (`experiments/t-mod-dyadic-rotations-2026-09-17/twist_search.py`, exact rational PL arithmetic).
  - `K = 4` (`twist_K4.json`). Torsion twists exist: `x_0ρ_a` has finite order for `a ∈ {5/16, 7/16, 1/2,
    11/16, 3/4}` (orders 26, 19, 3, 17, 5), and `x_1ρ_b` for eight values of `b`. No pair `(A, B)` commutes, and
    no pair of torsion twists generates a group with at most 5000 elements. So no twist with denominator 16
    lands in an abelian or finite group; the solvable and point-fixing cases were not tested.
  - `K = 5` (`twist_K5.json`, 1024 pairs). 7 torsion twists of `x_0` and 14 of `x_1` (orders up to 60, bound 64).
    Again no commuting pair and no finite pair. So small twists do not escape through the abelian or finite
    branch of the structure lemma. The only possible escape left for `{x_0, x_1}` goes through point-fixing
    subgroups, whose amenability is `F`-level. This is evidence, not proof.
