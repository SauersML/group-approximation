---
rg: 2
id: train-track-split-cones-least-common-descendants-proof
kind: route
title: Proof that split descendants of a complete train track have least common descendants
target: train-track-split-cones-have-least-common-descendants
---

Lane bh-major-mcg, 2026-09-18. Lane proof, not independently reviewed. Notation is that
of the target node.

## Standard facts used (recalled from Penner–Harer, not re-read)

- **F1.** For a complete track `τ`, the carrying map `W(τ) → ML(S)` is a linear
  isomorphism onto `P(τ)`. This lets cones and linear functionals be compared inside
  `ML(S)`.
- **F2.** Let `σ = τ_b^ε`. Branches of `τ` other than `b` correspond to branches of `σ`,
  and in the identification `W(σ) ↪ W(τ)` their weights are unchanged. The image is
  `W(τ) ∩ {ε·ℓ_b ≥ 0}`. Here `ℓ_b = μ(a) − μ(d)`, where `a` and `d` are the small
  half-branches at the two ends of `b` on one diagonal; the opposite diagonal gives
  `−ℓ_b`.
- **F3.** Splits along distinct large branches commute (Penner–Harer). Agol uses this
  in `pAtriangulation3.tex`, §3: "any sequence of splits of a measured train track may
  be arranged by a sequence of commuting splits to be in maximal order".

## Part 1: wall locality

- **Distinct large branches share no switch.** A trivalent switch has exactly one large
  half-branch, and a large branch has a large half-branch at each end. So two distinct
  large branches `b, b'` have four distinct end switches, and neither is adjacent to the
  other.
- **The split at `b` leaves `b'` alone.** It changes only a small neighbourhood of `b` and
  its two end switches. So `b'`, its end switches and the small half-branches at them are
  unchanged. A small branch `e` joining an end of `b` to an end of `b'` is reattached only
  at its `b`-end. Hence `b'` is still large in `σ_b^ε`.
- **The wall of `b'` is unchanged.** Its small neighbours are the same branches, and by
  F2 they keep their weights. So `ℓ_{b'}` is the same functional on `P(σ_b^ε) ⊂ P(σ)`.
- **Commutation.** The two splits are supported in disjoint neighbourhoods, so they
  commute as isotopy classes (F3).
- **Cones of splits.** `P(σ_b^ε) = P(σ) ∩ {ε·ℓ_b ≥ 0}` is F2 read in `ML(S)` via F1.
- **Nonempty interior forces completeness.** Suppose a track `σ` obtained by splits has a
  cone with nonempty interior. Then `W(σ)` is full-dimensional in the solution space of
  the switch equations. No coordinate vanishes identically on that space, so an interior
  point has every coordinate positive, and `σ` is recurrent. Maximality and transverse
  recurrence pass to splits (recalled). So `σ` is complete.

## Part 2, one-step lemma

**Lemma.** Let `σ ∈ D(τ)`, let `(b, ε)` be a split of `τ` with `τ' = τ_b^ε`, and suppose
`int P(σ) ∩ int P(τ') ≠ ∅`. Then there is `σ' ∈ D(σ) ∩ D(τ')` with
`P(σ') = P(σ) ∩ P(τ')`.

**Proof.** Induct on the length `n` of a split sequence from `τ` to `σ`.

- **`n = 0`.** Then `σ = τ`; take `σ' = τ'`.
- **`n ≥ 1`.** Let the first step be `(c, δ)`, so `σ ∈ D(τ_c^δ)` by a sequence of length
  `n − 1`.
- **Case `c = b`.**
  - If `δ ≠ ε`, then `P(σ) ⊂ {δ·ℓ_b ≥ 0}` and `P(τ') ⊂ {ε·ℓ_b ≥ 0}` are on opposite
    sides of one hyperplane, contradicting the interior hypothesis.
  - So `δ = ε` and `σ ∈ D(τ')`; take `σ' = σ`, which works because `P(σ) ⊂ P(τ')`.
- **Case `c ≠ b`.**
  - By Part 1, `b` is large in `τ_c^δ` with the same functional `ℓ_b`.
  - The track `κ = (τ_c^δ)_b^ε = (τ_b^ε)_c^δ` has cone `P(τ_c^δ) ∩ {ε·ℓ_b ≥ 0}`. This cone
    contains `int P(σ) ∩ int P(τ')`, so it has nonempty interior, and `κ ∈ D(τ') ∩ D(τ_c^δ)`.
  - Apply the induction hypothesis over the base `τ_c^δ` to `σ` and the split `(b, ε)` of
    `τ_c^δ`. The interiors meet, since `P((τ_c^δ)_b^ε) ⊇ P(σ) ∩ P(τ')`.
  - This gives `σ' ∈ D(σ) ∩ D(κ) ⊂ D(σ) ∩ D(τ')` with
    `P(σ') = P(σ) ∩ P(κ) = P(σ) ∩ P(τ_c^δ) ∩ {ε·ℓ_b ≥ 0} = P(σ) ∩ P(τ')`.
  - The last equality uses `P(σ) ⊂ P(τ_c^δ)` and `P(τ') = P(τ) ∩ {ε·ℓ_b ≥ 0}`. ∎

## Part 2, the theorem

Let `τ = τ_0 → τ_1 → ⋯ → τ_n = σ_2` be a split sequence, and suppose the interiors of
`P(σ_1)` and `P(σ_2)` meet. Put `ρ_0 = σ_1`.

- **Inductive step.** Suppose `ρ_{k−1} ∈ D(σ_1) ∩ D(τ_{k−1})` with
  `P(ρ_{k−1}) = P(σ_1) ∩ P(τ_{k−1})`. The interiors of `P(ρ_{k−1})` and `P(τ_k)` meet,
  because both contain `int P(σ_1) ∩ int P(σ_2)`. The lemma over the base `τ_{k−1}` gives
  `ρ_k ∈ D(ρ_{k−1}) ∩ D(τ_k)` with `P(ρ_k) = P(σ_1) ∩ P(τ_k)`.
- **Conclusion.** `ρ = ρ_n` works. Leastness at the level of cylinders is immediate,
  since any common descendant has its cone inside `P(σ_1) ∩ P(σ_2) = P(ρ)`.

Tracks with equal cones need not be equal: a "forced" split, whose other side has empty
interior, keeps the cone. So the least object is canonical as a cylinder, not as a
track. For the boundary groupoid only the cylinder matters.

## Parts 3 and 4

- **Part 3.** This is Agol, arXiv:1008.1606, Corollary `spliteq` (TeX §3), which I read.
  Its proof reduces to Penner–Harer Theorem 2.3.1, quoted there verbatim, and to Agol's
  Lemma `edgesplit` for minimal `λ`.
- **Part 4.** `Mod(S)` has finitely many orbits of complete tracks (standard, recalled). A
  complete track on `S_g` has a bounded number of branches, and the number of large
  branches is at most half the number of cusps.

## Lesson for general BH

The proof uses only two properties of the move system:
- the wall deciding a move is unchanged by moves elsewhere;
- moves with disjoint supports commute.

Any group-equivariant system of binary moves with these two properties has least
common descendants by this exact induction, which is Levi's lemma for traces. So
checking these two local properties is the first test for any proposed Garside-type
coding of a Boone–Higman input.
