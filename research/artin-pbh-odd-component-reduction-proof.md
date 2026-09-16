---
rg: 2
id: artin-pbh-odd-component-reduction-proof
kind: route
title: Kill generators across even boundaries to get retractions, split A_Γ over the Artin group of the odd components adjacent to one component, and induct on the number of odd components
target: artin-pbh-reduces-to-odd-component-cliques
requires:
  - pbh-class-closed-under-common-retract-amalgams
  - boone-higman-type-a-class-closed-under-finite-extensions
  - type-a-action-gives-boone-higman-for-subgroups
---

Notation as in the target. `Π(u, v; m)` is the alternating word `u v u ⋯` of length
`m`, and `A_Γ = < V | Π(u, v; m_uv) = Π(v, u; m_uv) for every edge uv >`. A set
`S ⊆ V` is **odd-saturated** when it is a union of odd components, that is, when no
odd edge joins `S` to `V \ S`. Details are in §5 of
`research/artifacts/bh-common-retract-amalgams-even-artin-2026-09-16.md`.

## Lemma 1. Even-boundary retractions

Let every edge joining `Λ` to `V \ Λ` be even. Then `π_Λ` (`u -> u` for `u ∈ Λ`,
`u -> 1` otherwise) is a homomorphism `A_Γ -> A_Λ`, and `π_Λ ∘ ι = id` for the
natural map `ι: A_Λ -> A_Γ`. So `ι` is injective and `A_Λ` is a retract.

*Proof.* Check the relators.
- **Both ends in `Λ`.** A relator of `A_Λ`.
- **Both ends outside `Λ`.** It becomes `1 = 1`.
- **One end `u ∈ Λ`, the other outside, with `m = 2k`.** `(uv)^k = (vu)^k` becomes
  `u^k = u^k`.

`π_Λ ∘ ι` fixes every generator. Every odd-saturated `Λ` qualifies. ∎

## Lemma 2. Even-boundary splittings

Let `V = V_1 ∪ V_2` and `Λ = V_1 ∩ V_2`. Suppose no edge joins `V_1 \ Λ` to
`V_2 \ Λ`, and every edge from `Λ` to `V \ Λ` is even. Then
`A_Γ = A_(V_1) *_(A_Λ) A_(V_2)`, `A_Λ` is a retract of both factors, and
`A_Γ ∈ B_A` iff `A_(V_1), A_(V_2) ∈ B_A`.

*Proof.*
- **Presentation.** Every edge of `Γ` lies in `Γ[V_1]` or `Γ[V_2]`. So the pushout
  presentation of `A_(V_1) <- A_Λ -> A_(V_2)` is that of `A_Γ`.
- **Retractions.** Lemma 1 inside `Γ[V_i]` makes `A_Λ -> A_(V_i)` injective with a
  retraction. So the pushout is an amalgamated product over a common retract.
- **"If"** is Part 1 of `pbh-class-closed-under-common-retract-amalgams`.
- **"Only if".** `A_(V_i)` embeds in the amalgam, and `B_A` is closed under subgroups
  (`boone-higman-type-a-class-closed-under-finite-extensions`). ∎

## Lemma 3. Inheritance

For odd-saturated `S`, the odd components of `Γ[S]` are the odd components of `Γ`
contained in `S`, and `Q(Γ[S])` is the induced subgraph of `Q` on them.
- The odd edges of `Γ[S]` are the odd edges of `Γ` inside `S`, and every odd
  component inside `S` keeps all of its odd edges.
- An edge between two components inside `S` lies in `Γ[S]`.

## Proof of the statement

- **Only if.** Every union of odd components is odd-saturated, so its Artin group
  embeds in `A_Γ` (Lemma 1). Closure under subgroups gives membership.
- **If.** Induct on the number `k` of odd components.
  - **`Q` complete (including `k ≤ 1`).** `V` itself is a union over a clique, so
    `A_Γ ∈ B_A` by hypothesis.
  - **Otherwise.** Take odd components `O ≠ O'` that are not adjacent in `Q`. Let `Λ`
    be the union of the odd components adjacent to `O`, and put `V_1 = V \ O` and
    `V_2 = O ∪ Λ`.
    - `V_1 ∩ V_2 = Λ`, since `O ∩ Λ = ∅`.
    - An edge leaving `O` ends in a component adjacent to `O`, that is in `Λ`. So no
      edge joins `V_2 \ Λ = O` to `V_1 \ Λ`.
    - `Λ` is odd-saturated, so its boundary edges are even. Lemma 2 applies.
    - `V_1` and `V_2` are odd-saturated. Each has fewer than `k` odd components,
      because `O ⊄ V_1` and `O' ⊄ V_2`.
    - By Lemma 3 every clique of `Q(Γ[V_i])` is a clique of `Q`, so the hypothesis
      holds for `Γ[V_i]`.
    - By induction `A_(V_1), A_(V_2) ∈ B_A`, and Lemma 2 gives `A_Γ ∈ B_A`.
  - When `Λ = ∅` the splitting is a free product over the trivial retract.
- **Even labels.** Each odd component is a single vertex, and `Q` is the underlying
  graph of `Γ`. Every subset is odd-saturated, so by Lemma 1 the Artin group of a clique
  is a retract of that of any maximal clique containing it. Maximal cliques therefore
  suffice.
- **Solvable word problem and simple envelope.** A group in `B_A` is a subgroup of a
  group with a type (A) action. So it embeds in a finitely presented simple group and,
  being finitely generated here, has solvable word problem
  (`type-a-action-gives-boone-higman-for-subgroups`). ∎
