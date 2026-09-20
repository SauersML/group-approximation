---
rg: 2
id: attractor-repeller-fixers-review
kind: claim
title: Referee review of 9d789abc60 (attractor/repeller fixers force disjoint supports) — Proposition C is correct and uses no local fixedness or torsion-freeness, only the recalled normal form (N); Lemma S and the Corollary are correct; the reduction of Q4.7 to (STAB) is correct, the non-cyclicity of every one-point stabilizer coming from HSZ Theorem A with Lemma L; (N) remains the one input not checked at source
distinct_from:
  fixers-of-attractor-and-repeller-sets-force-disjoint-supports: that is the lane claim under review; this checks Proposition C, Lemma S, the Corollary and the Q4.7 reduction.
  one-ended-hyperbolic-v-locally-fixed-review: that review passed Lemma L, which the reduction uses at every point.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of the lane proof 9d789abc60 by bh-q47-comp).**

## Verdicts

| item | verdict |
|---|---|
| (1) Proposition C, and its two variants | **PASS**: no local fixedness, no torsion-freeness |
| (2) Lemma S (germ commutators; `[γ′, b]` trivial on `P`) | **PASS** |
| Corollary (stabilizer form) | **PASS** |
| (3) the reduction of Q4.7 to (STAB) | **PASS**; (STAB) correctly **open** |
| (N), the normal form of infinite-order elements of `V` | **recalled, not checked at source**, and correctly labeled so |

## (1) Proposition C

**Supports.** `supp g = C ∖ int Fix(g)` is the *closed* support. It is clopen by (F1), and it is
conjugation-equivariant. Disjoint closed supports imply disjoint moved sets, so the elements commute.

**The proof, step by step.**
- **`h`'s support.** `M` is a clopen neighbourhood of `R` fixed pointwise by `h`, so `M ⊆ int Fix(h)` and
  `supp h ⊆ C ∖ M ⊆ P ⊔ (F ∖ M)`. This holds even if `M` meets `P`.
- **`f`'s fixed set.** `f` fixes the open set `P` pointwise, so `P ⊆ int Fix(f)`. A clopen `N ⊆ F` with
  `A ⊆ N ⊆ int Fix(f)` exists, because `A` is finite and `C` is zero-dimensional.
- **Contraction.** `K = F ∖ M` is compact and misses `R`. So by (N), `γ′^n(K) ⊆ N` for large `n`, while
  `γ′^n(P) = P`.
- **Disjointness.** `supp(γ′^n h γ′^(−n)) = γ′^n(supp h) ⊆ P ∪ N ⊆ int Fix(f)`, which is disjoint from `supp f`.
  Both elements are nontrivial.

**The variants.**
- *`γ′⁻¹`.* This swaps `A` and `R`, by (N).
- *`P` on `h`'s side.* Then `supp h ⊆ K`, so `f` need only fix a neighbourhood of `A`.

**What is and is not used.** Only (N), and the existence of `h` and `f`. No local fixedness and no
torsion-freeness enter. **PASS.**

## (2) Lemma S

- **Germs.** By (F2) (refereed, 6a216bf0dc), germs at `x` of elements fixing `x` form a subgroup of `Z`, so they are
  abelian. The germ map is a homomorphism, so `[a, b]` has trivial germ at every `x ∈ X`. It is therefore the
  identity near `X`, which is finite. Non-commuting `a, b` give a nontrivial such element.
- **The identity region.** For `y ∈ P`: `b⁻¹y ∈ P`, which `γ′⁻¹` fixes; `b` returns it to `y`; and `γ′` fixes `y`.
  So `[γ′, b]` is trivial on `P`. **PASS.**

## Corollary

- **`γ′` is a legal input.** `γ ≠ 1` has infinite order, by torsion-freeness, so (N) applies. `γ′` lies in `Γ_R`
  and in `Γ_A`, since it fixes both sets pointwise.
- **The element `h`.** If `Γ_R` is not cyclic, it is not contained in the cyclic group `C(γ′)`. So some
  `b_R ∈ Γ_R` does not commute with `γ′`, and `h = [γ′, b_R] ∈ [Γ_R, Γ_R]` fixes a neighbourhood of `R`
  (Lemma S).
- **The element `f`.** Given `b_A ∈ Γ_A ∩ Stab(P)` not commuting with `γ′`, the element `f = [γ′, b_A]` fixes a
  neighbourhood of `A` and is trivial on `P`.
- **Conclusion.** Proposition C gives two nontrivial elements with disjoint supports, which step (D) of Lemma B
  excludes (reviewed, 7ff5a6abf0). **PASS.**

## (3) Reduction of Q4.7 to (STAB)

**The key input: every one-point stabilizer `Γ_x` is non-cyclic.** This holds for every `x ∈ C`, not only for
`x ∈ K`.
- HSZ Theorem A makes `Γ/Γ_x` a quasi-tree for every `x`.
- `Γ_x = 1` would make `Γ` virtually free, by item 1 of the refereed partial.
- `Γ_x = ⟨c⟩` with `c` of infinite order contradicts Lemma L (refereed, 020fc76108).
- In a torsion-free group these are the only cyclic cases.
- *Wording.* The node phrases this as "the argument of" the locally-fixed node. That is right, but it should cite
  HSZ Theorem A at `x` together with Lemma L explicitly.

**The bullets.**
- `|R| = 1` makes `Γ_R` non-cyclic, so the Corollary forces `Γ_A ∩ Stab(P) ⊆ C(γ′)`.
- If also `P = ∅` and `|A| = 1`, this contradicts non-cyclicity of `Γ_A`. That recovers the north–south case.

**(STAB) suffices.** For a hypothetical torsion-free one-ended hyperbolic `Γ ≤ V`, (STAB) contradicts the
Corollary, so it gives a negative answer to Q4.7. (STAB) is correctly marked **open**.

**The one unverified input.** (N) is the standard revealing-pair and flow-graph picture of infinite-order elements
of `V`: after a power, the element is the identity on a clopen region, and elsewhere it has finitely many attracting
and repelling fixed points with uniform convergence on compacta. The node marks it as recalled and names the
sources to check: Brin; Salazar-Díaz; Bleak–Bowman–Gordon–Graham–Hughes–Matucci–Sapir. Everything above is
conditional on it.

## Lesson for general BH

**Local fixedness was a red herring for disjoint supports.** In `V`, disjoint supports come from any element whose
attractor and repeller sets both have nontrivial neighbourhood fixers. Germ commutators manufacture those fixers
from non-abelian pointwise stabilizers. So Q4.7 has become a question about how large pointwise stabilizers of
finite fixed sets can be, in a subgroup of `V` whose Schreier graphs are all quasi-trees.
