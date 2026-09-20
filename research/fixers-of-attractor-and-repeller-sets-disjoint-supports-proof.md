---
rg: 2
id: fixers-of-attractor-and-repeller-sets-disjoint-supports-proof
kind: route
title: Proof that neighborhood fixers of an element's repeller set and of its identity region plus attractor set force disjoint supports in V
target: fixers-of-attractor-and-repeller-sets-force-disjoint-supports
requires: []
---

Lane proof (bh-q47-comp, 09-19), not reviewed. Notation and the recalled normal form (N) are as in the target node.
Supports are conjugation-equivariant: `supp(δgδ⁻¹) = δ(supp g)`.

## Lemma S

**Germs at a fixed point commute.** Let `x ∈ C` and let `g ∈ V` fix `x`. Near `x`, `g` replaces a prefix `u` of `x` by
a prefix `v`, with `x = uy` and `vy = x`.
- If `|u| = |v|`, then `u = v`, and `g` is the identity near `x`.
- Otherwise `x` is eventually periodic, and the germ of `g` at `x` is a power of the shift germ along the period.

So the germs at `x` of elements fixing `x` form a subgroup of `Z`. This is fact (F2), refereed in 6a216bf0dc.

**Proof of the first claim.** Let `a, b ∈ Γ_X` and `x ∈ X`. The germ of `[a,b]` at `x` is the commutator of the germs
of `a` and `b` at `x`, which is trivial because germs at `x` commute. So `[a,b]` is the identity on a neighborhood of
each `x ∈ X`, hence on a neighborhood of `X`, since `X` is finite. If `a` and `b` don't commute, `[a,b] ≠ 1`.

**Proof of the second claim.** Let `y ∈ P`. Since `b(P) = P`, `b⁻¹y ∈ P`, so `γ'⁻¹` fixes it. Then `b` returns it to `y`,
and `γ'` fixes `y`. So `[γ', b] = γ' b γ'⁻¹ b⁻¹` fixes `y`.

## Proposition C

- Let `M` be a clopen neighborhood of `R` fixed pointwise by `h`. Then `supp h ⊆ C ∖ M = P ⊔ (F ∖ M)`.
- Let `N ⊆ F` be a clopen neighborhood of `A` with `P ∪ N ⊆ O_f`. It exists because `f` fixes `P` and a neighborhood of
  `A`, and `A ⊆ F` is finite.
- `K = F ∖ M` is compact and misses `R`. By (N), `γ'^n(K) ⊆ N` for all large `n`.
- Also `γ'^n(P) = P`.
- Put `u = γ'^n h γ'^{-n}`. It is nontrivial, since it is conjugate to `h ≠ 1`, and
  `supp u = γ'^n(supp h) ⊆ P ∪ γ'^n(K) ⊆ P ∪ N ⊆ O_f = C ∖ supp f`.

So `u` and `f` are nontrivial with disjoint supports.

**Swapped version.** Apply the argument to `γ'⁻¹`. Its normal form has `A` and `R` swapped, by (N).

**`P` on `h`'s side.** If `h` also fixes `P`, then `supp h ⊆ F ∖ M = K` and `supp u ⊆ N`. So it is enough that `f`
fixes a neighborhood of `A`.

## Corollary

Suppose `Γ_R` is non-cyclic and some `b_A ∈ Γ_A ∩ Stab(P)` doesn't commute with `γ'`.

**Finding `h`.** Since `C(γ')` is cyclic and `Γ_R` is not,
there is `b_R ∈ Γ_R` not commuting with `γ'`. Since `γ' ∈ Γ_R`, Lemma S makes `h = [γ', b_R]` a nontrivial element
fixing a neighborhood of `R`.

**Finding `f`.** `f = [γ', b_A]` is nontrivial.
- It fixes a neighborhood of `A`, by Lemma S, since `γ', b_A ∈ Γ_A`.
- It is the identity on `P`, by the second part of Lemma S.

**Conclusion.** Proposition C gives two nontrivial elements with disjoint supports. In a torsion-free group with cyclic
centralizers that is impossible: such elements commute, so they are nonzero powers of one `z`, and `z^{ab}` would be
supported in `∅`. This is step (D) of `block-permuting-local-fixers-disjoint-supports-proof`.

So one of the two hypotheses fails. The swapped statement follows the same way.
