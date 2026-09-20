---
rg: 2
id: fixers-of-attractor-and-repeller-sets-force-disjoint-supports
kind: claim
title: In a subgroup of V, neighborhood fixers of an element's repeller set and of its identity region plus attractor set force two disjoint supports
distinct_from:
  locally-fixed-torsion-free-subgroups-of-v-have-disjoint-supports: that is (COMP), still open; this is a sufficient criterion for its conclusion that uses no local-fixedness hypothesis, and turns the open dynamical case into a condition on pointwise stabilizers of finite sets.
  one-ended-hyperbolic-subgroups-of-v-are-locally-fixed: its item 2 (a north–south element forces disjoint supports) is the special case A, R singletons and P empty; this allows several attractors and repellers and a nonempty identity region.
  block-permuting-local-fixers-force-disjoint-supports: that needs fixers permuting a common partition; this has no permuting hypothesis.
---

**ESTABLISHED** by `fixers-of-attractor-and-repeller-sets-disjoint-supports-proof` (lane proof, bh-q47-comp, 09-19, not
reviewed). It uses one recalled input about the dynamics of single elements of `V`, marked (N) below.

## Setup

For `g ∈ V` write `O_g = int Fix(g)` (clopen) and `supp g = C ∖ O_g`. For `Γ ≤ V` and a finite `X ⊆ C`, write `Γ_X` for
the pointwise stabilizer of `X` and `Γ⁰_X` for the elements fixing a neighborhood of `X`.

**(N) Normal form (recalled, not read at source; the same input as the (COMP) node's "Where a proof must work").** For
`γ ∈ V` of infinite order, some power `γ' = γ^m` has: `C = P ⊔ F` with `P, F` clopen, `γ'|_P = id`, `γ'(F) = F`;
`Fix(γ') ∩ F = A ⊔ R` is finite; and for every compact `K ⊆ F ∖ R` and every neighborhood `N` of `A`, `γ'^n(K) ⊆ N`
for all large `n`. The same holds for `γ'^{-1}` with `A` and `R` swapped. Sources to check: Brin's revealing pairs,
Salazar-Díaz, and Bleak–Bowman–Gordon–Graham–Hughes–Matucci–Sapir on centralizers in `V`.

## Statements

**Lemma S (germ commutators).** For every `Γ ≤ V` and finite `X ⊆ C`, `[Γ_X, Γ_X] ⊆ Γ⁰_X`. So if `Γ_X` is non-abelian,
some nontrivial element of `Γ` fixes a neighborhood of `X`. Moreover, if `γ'|_P = id` and `b(P) = P`, then `[γ', b]` is
the identity on `P`.

**Proposition C (criterion).** Let `Γ ≤ V`, and let `γ ∈ Γ` have normal form `(γ', P, F, A, R)`. Suppose `h, f ∈ Γ ∖ {1}`,
where `h` fixes a neighborhood of `R` and `f` fixes `P` pointwise and a neighborhood of `A`. Then `f` and
`γ'^n h γ'^{-n}` (for all large `n`) are nontrivial elements with disjoint supports.
- The same holds with `A` and `R` swapped (use `γ'^{-1}`).
- The same holds with `P` moved to `h`'s side: `h` fixes `P` pointwise and a neighborhood of `R`, and `f` fixes a
  neighborhood of `A`.
- No torsion-freeness and no local fixedness is assumed.

**Corollary (stabilizer form).** Let `Γ ≤ V` be torsion-free with cyclic centralizers (the centralizer of every nontrivial element is cyclic; torsion-free
hyperbolic groups qualify), and let `γ ∈ Γ` be nontrivial with normal form `(γ', P, F, A, R)`. Then
- `Γ_R` is cyclic, or
- `Γ_A ∩ Stab_Γ(P)` is contained in the centralizer of `γ'`,

and the same with `A` and `R` swapped. When `P = ∅`, the second condition reads "`Γ_A` is cyclic".

## What this gives for (COMP) and Q4.7

**Q4.7 reduces to a stabilizer condition.** Let `Γ ≤ V` be torsion-free, one-ended and hyperbolic. It has cyclic
centralizers. The argument of `one-ended-hyperbolic-subgroups-of-v-are-locally-fixed` (refereed; Lemma L with HSZ Theorem A) shows every one-point stabilizer
`Γ_x` is non-cyclic. So the Corollary constrains every nontrivial `γ ∈ Γ`:
- If `|R_γ| = 1`, then `Γ_{A_γ} ∩ Stab(P_γ) ⊆ C(γ')`, which is cyclic. Symmetrically, if `|A_γ| = 1`, then
  `Γ_{R_γ} ∩ Stab(P_γ) ⊆ C(γ')`.
- If `P_γ = ∅` and `|A_γ| = |R_γ| = 1`, this contradicts Lemma L, which recovers the known north–south case.
- If `P_γ = ∅` and `|R_γ| = 1`, then `Γ_{A_γ}` is cyclic, even when `A_γ` has several points.

So a negative answer to Q4.7 for torsion-free one-ended hyperbolic groups now follows from:

**(STAB).** Some nontrivial `γ ∈ Γ` has `Γ_{R_γ}` non-cyclic and `Γ_{A_γ} ∩ Stab_Γ(P_γ) ⊄ C(γ')`, or the version with `A`
and `R` swapped.

This is OPEN. Lemma L gives the one-point case; what is missing is non-cyclicity of pointwise stabilizers of finite
fixed sets, together with the identity region.

## Calibration

- **`S_3 × Z`** (torsion, pairwise meeting supports). For `z` with `ζ` fixing no open set, `A` and `R` have one point in
  each cone. Every element fixing all three repellers is a power of `z`, so no nontrivial element fixes a neighborhood
  of `R`. Proposition C does not apply, as it must not.
- **Schottky free subgroups.** For a north–south `γ`, the stabilizer of its repeller is the maximal cyclic subgroup
  containing `γ`, so the Corollary's hypotheses fail, consistent with free groups having meeting supports.
- **`Z²`, `F_n × F_m`, `F`, `T`, `V`.** They have disjoint supports anyway, so there is no conflict.
