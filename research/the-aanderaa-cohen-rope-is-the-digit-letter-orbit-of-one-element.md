---
rg: 2
id: the-aanderaa-cohen-rope-is-the-digit-letter-orbit-of-one-element
kind: claim
title: The infinite-rank rope of the Aanderaa-Cohen tower is the free-monoid orbit of t under the digit letters a_i, its relations follow from two finite families, and relative seeds pass through it exactly when its two edge groups carry relative seeds on H_1; reordering the tower (digit letters before p) removes the infinite rank modulo two Britton checks
requires:
  - higman-clapham-towers-leave-the-seed-form-at-three-steps
  - relative-seeds-glue-graphs-of-groups-into-class-c
distinct_from:
  higman-clapham-towers-leave-the-seed-form-at-three-steps: that lists the rope as one of three off-form steps; this analyses the rope itself, shows it is finite-state and has easy membership, and gives the reordering that should make it finitely generated.
  relative-seeds-glue-graphs-of-groups-into-class-c: that is the gluing theorem; this notes that its proof never uses finite generation of edge groups, so the rope is covered once relative seeds exist for its edge groups.
---

**Mixed status** (lane bh-invent-14, 2026-09-18; not reviewed).
- §§1–3 are **ESTABLISHED** (lane proof; elementary; the notation and the facts quoted are from
  D. E. Cohen, *Combinatorial Group Theory: a topological approach*, CUP 1989, §9.6 pp. 279–281,
  read at source).
- §4 is **OPEN** (two precise Britton checks).
- §5 is analysis.

**Setting (Cohen §9.6).**
- `H_1 = K_M * (C × ⟨b_1, …, b_n⟩) * ⟨d⟩`, with `t_α = t(α,0) = x^{-α} t x^{α}`.
- `I` is the set of `α` whose `m`-ary digits lie in `{1, …, 2n}`, and `w_α` is the corresponding
  word.
- The rope is `H_2 = ⟨H_1, p | p^{-1} t_α p = t_α w_α(b) d, α ∈ I⟩`. Its associated subgroups are
  `C_+ = ⟨t_α : α ∈ I⟩` and `C_- = ⟨t_α w_α(b) d : α ∈ I⟩`, both free on the displayed infinite
  bases (p. 280).
- `H_3` adds the digit letters `a_i` (`1 ≤ i ≤ 2n`): `a_i^{-1}` takes `t, x, d, b_j, p` to
  `t_i, x^m, b_i d, b_j, p`. It also adds `k`.

## 1. The rope is one orbit

For a digit word `W = a_{i_1} ⋯ a_{i_r}`, put `α(W) = (⋯(i_1 m + i_2)m + ⋯)m + i_r`, the numeral
with digits `i_1, …, i_r`.

**Claim.** In any group where the `a_i` act as in `H_3`, `W^{-1} t W = t_{α(W)}` and
`W^{-1} d W = w_{α(W)}(b) d`.

*Proof.*
- One letter: `a_i^{-1} x^{-α} t x^{α} a_i = x^{-mα} t_i x^{mα} = t_{mα + i}`.
- `a_i^{-1} (w(b) d) a_i = w(b) b_i d`, and `w_{αm+i} = w_α b_i` (p. 279).
- Induct on `r`. ∎

So `{t_α : α ∈ I} = {W^{-1} t W : W ∈ {a_1, …, a_{2n}}^*}`. The regular index set `I` **is** the
free monoid on the digit letters, acting on the single element `t`.

**Corollary (the relations are finitely generated).** The two finite families
- `p^{-1} t p = t d`, and
- `[p, a_i] = 1`, together with the `a_i`-relations on `t` and `d`,

imply every rope relation: conjugating the first family by `W` gives
`p^{-1} t_{α(W)} p = t_{α(W)} w_{α(W)}(b) d`. This is Cohen's own derivation on p. 281, read as a
recursion on digit words.

## 2. Membership in the rope is finite-state

`g ∈ C_+` iff `g ∈ T = ⟨⟨t⟩⟩_K` (decidable in `K`) and every letter `t(r,s)` of `g` in the free
basis of `T` has `s = 0` and `r ∈ I`. Membership in `I` is decided by a finite automaton on base-`m`
digits. `C_-` is handled the same way, through the basis `t_α w_α(b) d`.
- So by item 3 of `relative-seeds-glue-graphs-of-groups-into-class-c` (membership is consumed),
  a relative seed for the rope only has to compute a **regular** membership problem.
- **The rope is not a CAP obstacle.** Its infinite rank carries no complexity.

## 3. Relative seeds pass through infinitely generated edge groups

In `relative-seeds-glue-graphs-of-groups-proof`, the edge groups `C_ε` enter only through their
relative seeds `(Y_ε, π_ε)` and the exclusivity rule (X). Finite generation is used only for the
**vertex** groups: rule (T) transports types along generators of `V_u`, and rule (Y) reads `Y_τ` on
cosets of `V_u`.
- So the gluing theorem holds verbatim for a finite graph of finitely generated vertex groups with
  **arbitrary** edge groups.
- The rope HNN `H_2` has one finitely generated vertex group `H_1` and one loop. Hence:
  - `(H_2, C) ∈ 𝓡` whenever `(H_1, C) ∈ 𝓡`, provided `(H_1, C_+) ∈ 𝓡` and `(H_1, C_-) ∈ 𝓡`;
  - `H_2 ∈ 𝒞` under the same proviso together with `H_1 ∈ 𝒞`.
- `H_1 ∈ 𝒞` needs `C × F_n ∈ 𝒞`, the input's own seed. This is ingredient 1 of the parent node.

## 4. Reordering removes the infinite rank (OPEN at two checks)

Build `H_3` in the order `H_1 → B_1 → B_2 → B_3`, with the same finite presentation (I) of Cohen
p. 281, so `B_3 ≅ H_3`:

- **`B_1 = ⟨H_1, a_i | a_i^{-1} u a_i = φ_i(u), u ∈ A°⟩`.** Here `A° = ⟨t, x, d, b_j⟩` and
  `φ_i : t, x, d, b_j ↦ t_i, x^m, b_i d, b_j`. This is an HNN extension (**proved**).
  - `A° = F(t,x) * F(b) * ⟨d⟩` is free on `{t, x, b_j, d}`. The factors lie in the three free
    factors of `H_1`, and `⟨x, t⟩ ≤ K` is free.
  - `A_i° = ⟨t_i, x^m⟩ * F(b) * ⟨d⟩` is free on `{t_i, x^m, b_j, b_i d}` for the same reason.
  - So `φ_i` is a bijection of free bases.
- **`B_2 = ⟨B_1, p | p^{-1} t p = t d, [p, a_i] = 1⟩`.**
  - **(R1)** This is an HNN extension iff `t ↦ td`, `a_i ↦ a_i` is an isomorphism
    `⟨t, a_i⟩ → ⟨td, a_i⟩` of subgroups of `B_1`.
  - On the positive orbit (§1) both sides are Cohen's bases `t_α` and `t_α w_α(b) d`. What remains
    is the words with negative digit letters.
- **`B_3 = ⟨B_2, k | k^{-1} u k = u (u ∈ U ∪ {d, p}), k^{-1} b_j k = b_j c_j⟩`.**
  - **(R2)** Cohen proves that `A_+ → A_-` is an isomorphism in `H_2` (p. 280). The same must be
    checked in `B_2`.

If (R1) and (R2) hold, every step of the Aanderaa–Cohen tower has finitely generated associated
subgroups, and the rope disappears as a separate step.

## 5. What remains for relative seeds

After reordering, the new relative seeds needed are:
- `(H_1, A°)` and `(H_1, A_i°)`. These subgroups are free products of subgroups of the three free
  factors, so they need a **Kurosh gluing** for relative seeds: the forced point marks the
  `C`-minimal subtree as its core instead of a single exit.
- `(B_1, ⟨t, a_i⟩)` and `(B_1, ⟨td, a_i⟩)`. Their membership is regular, by §2.
- `(B_2, A_±)`. This is **CAP**, because `A_+ ∩ K` encodes `H_0(M)`.

Without reordering, the needed seeds are `(H_1, C_±)` by §3. Along the `x`-ray, the forced point
must read an `m`-automatic sequence (the indicator of `I`).
- A `Z`-direction alone cannot force that.
- `K_M` contains the dilations `r_i^{-1} x^m r_i = x^{m^2}`, and `B_1` contains `a_i`. Those are
  the natural carriers.

## Lesson for general BH

**Infinite rank is an artifact of order.** The rope's infinitely many relations are one relation
transported by the free monoid on the machine's digit letters. Its membership is finite-state,
so it costs no complexity.
- **For seeds**, infinitely generated edge groups are harmless (§3). The rope needs relative seeds
  only for regular subgroups. Built in the other order, it needs only finitely generated ones,
  modulo (R1) and (R2).
- **So the seed tower's real work is concentrated in two places:**
  - a Kurosh-type gluing for subgroups that span several free factors, which is input-free;
  - the halting HNN along `A_±`, which is CAP.
- **General principle:** a regular family of relations should be generated by transport along a
  finite automaton inside the group, and then seeds see it as finite-state.
