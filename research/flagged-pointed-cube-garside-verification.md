---
rg: 2
id: flagged-pointed-cube-garside-verification
kind: route
title: Full Garside verification for the flagged pointed-cube category, via Dehornoy's mcm criterion, with the normal form written out (Niblo-Reeves cubes with maximal compatible labels) and the norm computed as the height of the hyperplane poset
target: flagged-pointed-cube-category-resynchronizes-cubulated-actions
requires:
  - pointed-cube-categories-are-li-garside-categories
  - pointed-cube-bisection-locus-is-the-regular-boundary
---

**Lane proof, written for referees (requested in re-review d6778b5f5f); not independently
reviewed.** This replaces the "heads" paragraph of §1 of `flagged-pointed-cube-category-proof`
with a complete argument.

## 0. Conventions and facts used

Fix a target representative `(w,σ)`. By freeness, morphisms with this target are the pairs
`(u,τ)` with:
- `H(w,u) ∩ σ = ∅`;
- `π(σ;w,u) ⊆ τ ⊆ adj(u)`, where `π(σ;w,u) = (σ ∪ H(w,u)) ∩ adj(u)`.

Composition is concatenation, by Lemma C of `flagged-pointed-cube-category-proof`. Units are
trivial.

**Left divisibility.** `(y,λ) ≼ (u,τ)` iff `(y,λ;u,τ)` is a morphism, that is, iff
`H(y,u) ∩ λ = ∅` and `π(λ;y,u) ⊆ τ`. Then `y ∈ I(w,u)` by Lemma C(1).

Standard cube complex facts, not re-derived:
- **(F1)** Pairwise crossing walls adjacent to `w` span a cube at `w`, whose far corner `j`
  has `H(w,j)` equal to those walls.
- **(F3) Niblo–Reeves.** For `u ≠ w`, the normal cube path `w = y_0, …, y_h = u` has
  cubes `c_k` whose walls are the walls of `H(y_{k−1},u)` adjacent to `y_{k−1}`. Its length
  `h` is the height of `(H(w,u), <)`. This is used in `pointed-cube-categories-li-garside-proof`.
- **(F4) Intervals.** If `y' ∈ I(a,b)` and `b ∈ I(a,c)`, then `b ∈ I(y',c)`.

Facts proved elsewhere or here:
- **(F2)** Two disjoint walls adjacent to `w` have disjoint far halfspaces. Proof:
  `w ∈ A^- ∩ B^-`, the `A`-edge at `w` lies in `A^+ ∩ B^-`, and the `B`-edge lies in
  `A^- ∩ B^+`. So the empty quadrant is `A^+ ∩ B^+`.
- **(F5)** The leaving and persistence lemmas of `pointed-cube-bisection-locus-proof` §2.

**Transitivity of propagation.** If `w → y → u` is geodesic, then
`π(π(σ;w,y); y,u) = π(σ;w,u)`. The inclusion `⊇` is Lemma C(2), and `⊆` holds because
`π(σ;w,y) ⊆ σ ∪ H(w,y)`.

## 1. The criterion

`C⁺` is right Noetherian and admits lcms (§1 of the proof node). Li (arXiv:2110.04505v2,
`s:CatBisGar`, citing Dehornoy, Chapter IV, Proposition 2.25) states: for such a category,
`𝔖` is a Garside family iff (a) `𝔖 ∪ 𝔠*` generates, and (b) `𝔖^♯` is closed under mcms and
under right divisors.

Take `𝔖⁺` to be the non-identity pairs `(u,τ)` with `H(w,u) ⊆ adj(w)`. By (F1) and (F2),
these are exactly the far corners of cubes at `w` whose walls avoid `σ`. The case `u = w`
(a flag) is included.

**(a) Generation.**
- If `u = w`, then `(u,τ)` is a flag, which lies in `𝔖⁺`.
- If `u ≠ w`, factor along the normal cube path of (F3) with natural labels
  `π(σ;w,y_k)`, and put `τ` on the last factor. The last factor is a morphism by
  transitivity of propagation.

**(b1) Right divisors.** Let `s = (u,τ) ∈ 𝔖⁺` with `s = (y,λ)·b`. Then `y ∈ I(w,u)` is a
vertex of the cube, and `H(y,u)` consists of walls of that cube, all adjacent to `y`. So
`b ∈ 𝔖⁺^♯`.

**(b2) Mcms.** Let `s_i = (u_i,τ_i) ∈ 𝔖⁺` have a common multiple. Their lcm is `(j,τ_j)`
with `H(w,j) = H(w,u_1) ∪ H(w,u_2) ⊆ adj(w)`. By (F2) no two of these walls are disjoint,
since `j` lies beyond both. By (F1), `j` is the far corner of a cube, so the lcm lies in
`𝔖⁺`.

So `𝔖⁺` is a Garside family. It is locally finite, since there are finitely many cubes and
labels at `w`. It is `=*`-transverse, and `𝔖⁺ ∩ 𝔠* = ∅`.

## 2. The normal form, explicitly

Let `a = (u,τ)` be a non-unit, and let `h` be the height in (F3).
- **Pure flags.** If `h = 0`, then `a` is a flag and `‖a‖ = 1`.
- **Maximal labels.** For `h ≥ 1` and `0 < k < h`, put
  `M_k = π(σ;w,y_k) ∪ {J ∈ adj(y_k) ∖ H(w,y_k) : J ∉ H(y_k,u), and J ∈ adj(u) ⇒ J ∈ τ}`.
  Also put `M_0 = σ` and `M_h = τ`.
- **`(y_k, M_k)` is the largest left divisor of `a` at `y_k`.** It divides `a`: `H(y_k,u)`
  avoids `M_k`, and `π(M_k;y_k,u) = π(σ;w,u) ∪ {extras adjacent to u} ⊆ τ`. Every
  `(y_k,λ) ≼ a` has `λ ⊆ M_k`, by the same two conditions.
- **The factors.** Let `s_k = (y_{k−1}, M_{k−1}; y_k, M_k)`.
  - It is a morphism. `H(y_{k−1},y_k)` avoids `M_{k−1}`. An extra wall of `M_{k−1}` that
    is adjacent to `y_k` meets the conditions defining `M_k`, because
    `H(y_{k−1},y_k) ⊆ H(y_{k−1},u)`.
  - It is one step, along the cube `c_k`.
  - `s_1 ⋯ s_h = a`.

**Normality.** Let `1 ≤ k ≤ h−1`, and let `r = (y',λ') ∈ 𝔖⁺` from `(y_{k−1},M_{k−1})` with
`r ≼ s_k s_{k+1}`.
- **Position.** The walls of `r`'s cube are adjacent to `y_{k−1}` and lie in
  `H(y_{k−1},y_{k+1}) ⊆ H(y_{k−1},u)`. So by (F3) they lie in `hyp(c_k)`, and `y'` is a
  vertex of `c_k`.
- **Avoidance.** By (F4), `y_k ∈ I(y', y_{k+1})`, so `H(y',y_k) ⊆ H(y',y_{k+1})` avoids
  `λ'`.
- **Label.** We check `π(λ';y',y_k) ⊆ M_k`. Crossed walls adjacent to `y_k` lie in
  `π(σ;w,y_k)`. Take `J ∈ λ'` adjacent to `y_k` with `J ∉ H(w,y_k)`.
  - If `J` is adjacent to `y_{k+1}`, then `J ∈ π(λ';y',y_{k+1}) ⊆ M_{k+1}`. So
    `J ∉ H(y_{k+1},u)`, and `J ∈ τ` if `J` is adjacent to `u`. Hence `J ∈ M_k`.
  - If not, the geodesic `y' → y_{k+1} → u` has left `J`'s carrier without crossing `J`.
    By (F5) it never crosses `J`, and `u` is not adjacent to `J`. Hence `J ∈ M_k`.
- So `r ≼ s_k`, and `(s_1, …, s_h)` is normal.

By uniqueness of normal forms (trivial units; Dehornoy, Chapter III, Corollary 1.27 as
quoted by Li), `‖a‖ = h`.

## 3. Left-divisor closure of `(𝔖⁺^{≤L})^♯`

The norm is `‖(u,τ)‖ = max(h(w,u), 1)` for non-units. Suppose `b = (y,λ) ≼ a`. Then
`y ∈ I(w,u)`, so `H(w,y)` is an order ideal of `(H(w,u), <)` and `h(w,y) ≤ h(w,u)`.
- If `b` is a flag, then `‖b‖ = 1 ≤ ‖a‖`.
- Otherwise `‖b‖ = h(w,y) ≤ ‖a‖`.

Hence `(𝔖⁺^{≤L})^♯ = {‖·‖ ≤ L}` is closed under left divisors, for every `L`. ∎

## Lesson for general BH

With lcms and right Noetherianity, Dehornoy's mcm criterion reduces "Garside family" to two
closure checks on one-step moves. For wall-based codings both checks are the same fact:
walls adjacent to a vertex, with a common far side, pairwise cross (F2).

The one delicate point is normality in the presence of promises. It rests on choosing
labels maximal, which is possible because every compatible promise is either still visible
at the next vertex or permanently unreachable, by the leaving lemma.
