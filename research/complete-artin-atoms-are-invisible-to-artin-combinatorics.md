---
rg: 2
id: complete-artin-atoms-are-invisible-to-artin-combinatorics
kind: claim
title: A complete Artin group can be moved by folding separations, parabolic embeddings, LCM-homomorphisms or diagram-automorphism folds only into complete parabolic subgroups, so these tools cannot reduce the atoms T4 and P
distinct_from:
  artin-pbh-reduces-to-free-of-infinity-artin-groups: that reduces every Artin group to complete ones; this explains why the same combinatorics cannot go further, so the complete cases need hosts of a different kind.
  artin-hub-cones-reduce-pbh-to-coned-cliques: that records "cliques are atoms" for one device; this proves it for the whole family of Artin-combinatorial maps.
  coprime-four-cycle-artin-pbh-reduces-to-one-tetrahedral-group: that reduces one graph to the complete atom P; this says which further moves cannot help with P.
---

**ESTABLISHED** (lane proof, elementary, in the body; not independently reviewed). A negative, method-level statement; no priority is claimed.

## Statement

Call an Artin group **complete** when its defining graph has every label finite (free of infinity). Let `A_Δ` be complete.

1. **Folding separations.** For every graph `Γ' ⊇ Δ` (induced) and every separation `V(Γ') = V_1 ∪ V_2` with no edge between `V_1 \ Λ` and `V_2 \ Λ`, the vertex set `V(Δ)` lies in `V_1` or in `V_2`. So `A_Δ` lies in one factor of every folding-separation amalgam (`artin-pbh-reduces-along-folding-separators`), at every stage of every iteration.
2. **LCM-homomorphisms** (Crisp: `s ↦ Δ_(X_s)`, the Garside elements of pairwise disjoint spherical subsets `X_s` of a graph `Σ`, with `X_s ∪ X_t` spherical and `Π(Δ_(X_s), Δ_(X_t); m_st) = Δ_(X_s ∪ X_t)` whenever `m_st < ∞`). If `Δ` is complete, then `Σ[∪ X_s]` is complete, and the image lies in the complete standard parabolic subgroup `A_(∪ X_s)`.
3. **Diagram-automorphism folds.** If a group `G` of automorphisms of a graph `Σ` has orbits spanning spherical subgraphs, and the folded graph `Σ_G` (orbits, with the folded labels) is complete, then `Σ` is complete.

Hence for the atoms left by `coprime-four-cycle-artin-pbh-reduces-to-one-tetrahedral-group` and `artin-hub-cones-reduce-pbh-to-coned-cliques`, namely `T4` (`K_4` with all labels 3) and `P` (`K_4` with five labels 3 and one label 2), no chain of these moves reaches a non-complete host. A proof that `T4` or `P` lies in `B_A` needs a host outside this combinatorics: a linear representation, an action on a tree or a CAT(0) complex, a Garside-odometer or germ construction (compare `artin-groups-embed-in-decorated-garside-odometer-groups`, which is for finite type), or an explicit type (A) action.

## Proof

1. The vertices of `Δ` are pairwise adjacent in `Γ'`. If `x ∈ V(Δ) ∩ (V_1 \ Λ)` and `y ∈ V(Δ) ∩ (V_2 \ Λ)`, the edge `xy` would join `V_1 \ Λ` to `V_2 \ Λ`. So `V(Δ) \ Λ` lies on one side, and `V(Δ) ⊆ V_1` or `⊆ V_2`. Each folding-separation step replaces a graph by the two sides, so this persists through iterations.
2. A spherical subset has every pairwise label finite (its Coxeter group is finite, so every pair generates a finite dihedral group). Every pair `s ≠ t` of `Δ` has `m_st < ∞`, so `X_s ∪ X_t` is spherical, and every pair of vertices `x ∈ X_s`, `y ∈ X_t` has a finite label. Within one `X_s` labels are finite because `X_s` is spherical. So `Σ[∪ X_s]` is complete, and each `Δ_(X_s)` lies in `A_(X_s) ≤ A_(∪ X_s)`.
3. In the folding of a Coxeter graph by an admissible group of automorphisms (Mühlherr; Crisp, *Symmetrical subgroups of Artin groups*; the convention is recalled here and was not re-read at source), the folded label between orbits `O ≠ O'` is finite exactly when `O ∪ O'` is spherical, and is `∞` otherwise. If `Σ_G` is complete, every `O ∪ O'` is spherical, and every orbit is spherical by hypothesis, so every pair of vertices of `Σ` has a finite label.

∎
