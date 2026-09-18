---
rg: 2
id: class-transposition-presentation-has-central-kernel
kind: claim
title: The transposition presentation of CT_P(Z) (squares, regular conjugation, splitting) is a perfect central extension of CT_P(Z); every finite box-permutation group embeds in it, and CT_P(Z) is perfect
distinct_from:
  ct-p-z-is-a-one-vertex-k-graph-full-group: that identifies CT_P(Z) with a k-graph full group and gets simplicity and F_infinity from Matui, Li and Farsi-Kumjian-Pask-Sims; this is an elementary statement about an explicit infinite presentation by class transpositions, with no cited theorem.
  class-transposition-relations-present-ct-p-z: that is the OPEN claim that the kernel here is trivial; this proves the kernel is central and the extension perfect.
artifacts:
  - research/artifacts/gq-bh-pal-kourovka61-presentation.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no cited theorem; no priority claimed).
For P = ∅ the presentation below is the multi-colour form of the Bleak–Quick presentation of V
by cone transpositions; this node does not use their theorem.

## Setting

- `P` is a finite set of odd primes, `P' = P ∪ {2}`, and `N_{P'}` is the monoid of positive
  integers all of whose prime factors lie in `P'`.
- A **box** is a residue class `r(m) = r + mZ` with `m ∈ N_{P'}`, `0 ≤ r < m`, `m ≥ 2`.
  A **box partition** is a finite set of pairwise disjoint boxes covering `Z`.
- **Intersections.** `r1(m1) ∩ r2(m2)` is empty or a residue class mod `lcm(m1, m2)` (CRT), so two
  box partitions have a common refinement by boxes, and the complement of a finite union of boxes
  is a finite disjoint union of boxes.
- **Canonical maps.** For boxes `A = r_A(m_A)`, `B = r_B(m_B)`, `κ_{B←A}(r_A + t m_A) = r_B + t m_B`.
  These compose (`κ_{C←B} κ_{B←A} = κ_{C←A}`), send sub-boxes to sub-boxes, and restrict
  canonically: `κ_{B←A}|_E = κ_{κ(E)←E}` for a box `E ⊆ A`.
- **Children.** For `p ∈ P'` the `p`-children of `A` are `A_a = (r_A + a m_A)(p m_A)`, `0 ≤ a < p`.
  They partition `A`, and `κ_{B←A}(A_a) = B_a`.
- **Uniform refinement.** For `k ∈ N_{P'}`, `U_k(A)` is the partition of `A` into the `k` residue
  classes mod `k m_A` it contains; `κ_{B←A}` maps `U_k(A)` onto `U_k(B)`.
- For disjoint boxes `A, B`, the **class transposition** `τ_{A,B}` swaps `A` and `B` by
  `κ_{B←A}` and `κ_{A←B}` and fixes the rest. `CT_P(Z)` is the group they generate.
- A box `E` is **regular** for `τ_{C,D}` if `E ⊆ C`, `E ⊆ D` or `E ∩ (C ∪ D) = ∅`. Then
  `τ_{C,D}(E)` is a box and `τ_{C,D}|_E` is canonical.

## The presented group Γ_P

Generators `t(A,B)`, one for each unordered pair `{A, B}` of disjoint boxes. Relations:
- **(R1)** `t(A,B)^2 = 1`.
- **(R2)** `t(C,D) t(A,B) t(C,D) = t(τ_{C,D}A, τ_{C,D}B)` whenever `A` and `B` are regular for
  `τ_{C,D}`.
- **(R3)** `t(A,B) = ∏_{a<p} t(A_a, B_a)` for every `p ∈ P'`.

All three hold for class transpositions in `Sym(Z)`, so `ε: t(A,B) ↦ τ_{A,B}` is a surjective
homomorphism `Γ_P → CT_P(Z)`.

## Statement

1. **Finite box permutations.** For a box partition `R = {E_1, …, E_n}`, `(i j) ↦ t(E_i, E_j)`
   defines an injective homomorphism `Sym(n) → Γ_P`. Its image `Γ_R` maps isomorphically onto the
   group of permutations of `Z` that permute the cells of `R` canonically.
2. **Central kernel.** `ker ε` is contained in the centre of `Γ_P`.
3. **Perfect.** `Γ_P` is perfect: every generator is a commutator. Hence `CT_P(Z)` is perfect.
4. **Consequence.** `ε` is an isomorphism, i.e. (R1)–(R3) present `CT_P(Z)`, if and only if
   `ker ε = 1`. This holds, for instance, whenever `H_2(CT_P(Z); Z) = 0`: a perfect central
   extension of a perfect group with trivial Schur multiplier is an isomorphism.

## Proof

**Lemma 1 (item 1).** The transpositions `(i j)` with relations `(i j)^2 = 1`,
`(i j)(k l) = (k l)(i j)` for disjoint pairs and `(i j)(j k)(i j) = (i k)` present `Sym(n)`.
In `Γ_P` these hold by (R1) and by (R2) with `C, D = E_i, E_j` (the other cells are disjoint
from `C ∪ D`; `E_j ⊆ D` goes to `E_i`). So `Sym(n) → Γ_P` is a homomorphism. Composing with
`ε` gives the canonical permutation action on the cells, which is faithful; so the map is
injective and `ε|_{Γ_R}` is an isomorphism onto its image.

**Lemma 2 (uniform splitting).** For disjoint boxes `A, B` and `k ∈ N_{P'}`,
`t(A,B) = ∏_{E ∈ U_k(A)} t(E, κ_{B←A} E)` in `Γ_P`, the factors commuting pairwise.
Induction on the number of prime factors of `k`. For `k p`, apply (R3) with colour `p` to each
factor: the `p`-children of `E` and of `κE` correspond under `κ`, and the union of the
`p`-children of the cells of `U_k(A)` is `U_{kp}(A)`. Factors have pairwise disjoint supports,
so they commute by (R2) (both boxes disjoint from `C ∪ D`).

**Lemma 3 (transport).** For a word `w = t_1 ⋯ t_k` with `t_i = t(C_i, D_i)`, call a box `E`
*regular along* `w` if `E_k := E` is regular for `τ_k`, and inductively `E_{i-1} := τ_i(E_i)`
is regular for `τ_{i-1}`. Put `w·E := E_0`, which equals `ε(w)(E)` as a set. If `A` and `B`
are regular along `w`, then `w t(A,B) w^{-1} = t(w·A, w·B)` in `Γ_P`: apply (R2) and (R1) once
for each `i`, from `i = k` down to `1`.

**Lemma 4 (fine partitions).** For every word `w` and box partition `R` there is a refinement
`S` of `R` whose cells are all regular along `w`.
- For `t(C,D)` let `π(C,D)` be `{C, D}` together with a box partition of `Z ∖ (C ∪ D)`. Every
  refinement of `π(C,D)` has cells regular for `τ_{C,D}`.
- Put `S_k := R ∧ π(C_k, D_k)`. Having `S_i`, whose cells are regular for `τ_i`, the image
  `τ_i(S_i)` is a box partition. Put `S'_{i-1} := τ_i(S_i) ∧ π(C_{i-1}, D_{i-1})`.
- Pull `S'_{i-1}` back to level `k` through `τ_i, …, τ_k`. A sub-box of a cell `τ_j(E)` pulls
  back under the canonical map `τ_j|_E` to a sub-box of `E`, so each pull-back is a box partition
  refining the previous one, and refinements keep all earlier regularity.
- After `k` steps the resulting partition `S` refines `R` and is regular along `w`.

**Item 2.** Let `w ∈ ker ε` be a word and `t(A,B)` a generator.
- Choose `R` with `A, B ∈ R` and take `S` from Lemma 4.
- Choose `k ∈ N_{P'}` so that `U_k(A)` refines `S|_A` and `U_k(B) = κ_{B←A}(U_k(A))` refines
  `S|_B` (take `k` divisible by every ratio `m_E / m_A` for cells `E ⊆ A`, and likewise for `B`).
- The partition `S'` obtained from `S` by replacing its cells in `A ∪ B` with `U_k(A) ∪ U_k(B)`
  refines `S`, so it is regular along `w`.
- By Lemma 2, `t(A,B) = ∏_{E ∈ U_k(A)} t(E, κE)`. By Lemma 3, `w t(E, κE) w^{-1} = t(w·E, w·κE)`,
  and `w·E = ε(w)(E) = E`, `w·κE = κE`. So `w` commutes with every factor, hence with `t(A,B)`.
- The generators generate `Γ_P`, so `w` is central.

**Item 3.** Let `x = t(A_0, B_0)` with `A_0, A_1, B_0, B_1` the `2`-children, and
`c = t(A_0, A_1) t(B_0, B_1)` (commuting involutions, so `c = c^{-1}`). By (R2) twice,
`c x c = t(A_1, B_1)`. By (R3) with `p = 2`, `t(A,B) = x · c x c^{-1} = [x, c]` since
`x^{-1} = x`. So `Γ_P = [Γ_P, Γ_P]`, and its image `CT_P(Z)` is perfect.

**Item 4.** If `G` is perfect and `H_2(G; Z) = 0`, the universal central extension of `G` is
`id_G`. Every perfect central extension `E → G` is a quotient of it, hence an isomorphism.
Apply this with `E = Γ_P` and `G = CT_P(Z)`, using items 2 and 3. ∎

## Scope

- Nothing here computes `H_2(CT_P(Z))` or shows `ker ε = 1`; that is
  `class-transposition-relations-present-ct-p-z` (OPEN).
- The presentation is infinite. A finite truncation is
  `ct-p-z-has-a-finite-class-transposition-presentation` (OPEN).
- Item 3 reproves perfectness of `CT_P(Z)` without Matui or Li (simplicity is Kohl's theorem and
  also follows from `ct-p-z-is-a-one-vertex-k-graph-full-group`).
