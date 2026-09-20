---
rg: 2
id: ct-z-21-74a-base-reduction-review
kind: claim
title: Referee review of b0a142ef7b (Kourovka 21.74(a) reduces to the base's clopen structure; Conway's amusical permutation decided NO) — PASS; the Haar-measure holonomy step is correct (a trivial-holonomy component would be a translation of R_j by an integer, contradicting indecomposability), the bounds and truncation carry over, and the Corollary holds, including item 2 of the Conway full-shift node, which is checked here
distinct_from:
  ct-z-kourovka-21-74a-reduces-to-base-coarse-structure: that is the lane node under review; this checks it step by step.
  conway-amusical-permutation-is-the-full-three-shift: that is an unreviewed lane node whose item 2 the Corollary uses; this checks that item.
  ct-p-z-neutral-primes-21-74a-review: that reviewed the positive-ray proof whose Lemmas 1–3 are reused here; this checks that the reuse is legitimate.
---

**ESTABLISHED (referee bh-ref-e, 2026-09-19; review of the lane node by bh-2174-rank2, landed in
b0a142ef7b).** No priority claimed.
- **Read at source on origin/main:** the new node; item 2 of `conway-amusical-permutation-is-the-full-three-shift`;
  the neutral-prime node as reviewed at 41b91ef912.
- **No code was run.**

## 1. Theorem R

**Lemmas B.1 and B.3 under Σ: correct.**
- B.1 uses only that `ĝ^K C = C`, with `K = |𝒫|!`. So the base of `C` is `g^K`-invariant, and indecomposability
  (with `t = K`) gives base `⊇ R_j`.
- B.3 is the skew-product identity.
- A box containing a nonempty open `R_j` has bounded radii, so there are finitely many base candidates.

**(1) The Haar-measure holonomy: correct.**
- If every holonomy over `R_j` is trivial, then all the `β^(M)_x`, `x ∈ R_j`, are one affine map `F`. The base
  action is `g^M(x) = β^(M)_x(x) = F(x)`, so `g^M = F` on `R_j`, and `F` maps `R_j` onto itself.
- **Haar scaling.** For an `S`-unit `λ` the product formula gives `∏_(p∈S) |λ|_p = λ^(−1)`. So `F` scales Haar
  measure on `Z_S` by `λ^(−1)`. `R_j` has positive measure, so `λ = 1`.
- A slope-one canonical map `r + mk ↦ s + mk` is translation by `s − r ∈ Z`.
- **`t = 0` is impossible.** `g^M` would be the identity on `R_j`, and a nonempty clopen subset of the Cantor set
  `Z_S` has proper nonempty clopen subsets.
- **`t ≠ 0` is impossible.** `(g^M)^m` is translation by `mt ∈ mZ_S` on `R_j`, so it preserves
  `R_j ∩ (a + mZ_S)`, which is proper and nonempty for a suitable `S`-smooth `m`.
- So a nontrivial holonomy exists, and enumerating `N` and the formulas of `g^N` on `R_j` finds one.

**(2) Bounds: correct, with one clarity repair.**
- **Translation holonomy `+τ`.** A ball `c + ℓ^e Z_ℓ` is invariant under it iff `v_ℓ(τ) ≥ e`, which is positive
  for finitely many `ℓ`.
- **Hyperbolic holonomy.** Replacing the attractor formula by `ψ_i` in Lemma 1.2 is legitimate. ⇐ is unchanged,
  and for ⇒ a degenerate center is fixed by every holonomy, in particular by the hyperbolic `ψ_i`, so it is its
  unique fixed point. The fibre slopes are `S`-units, hence `ℓ`-units, so the estimate and D1–D3 hold.
- **Repair.** Say explicitly what happens when some component of a `σ`-cycle yields a translation holonomy. Then
  the whole cycle is nondegenerate, since degeneracy is a cycle property (Lemma 1.1) and a nonzero translation fixes
  no point. So `q_i` is needed only for cycles all of whose found holonomies are hyperbolic. Also say that the
  translation bounds enter `E_ℓ` in Step 3.

**(3) Truncation and search: correct.**
- Lemmas 2–3 use only conditions 1–3, B.1, B.3 and coordinatewise unit-slope rational affine fibre maps. My review
  41b91ef912 checked this, and all of it holds under Σ.
- The ⇐ direction uses `ĝ^N = id` on `U × Φ`, which is Σ's first bullet.

## 2. The Corollary (Conway's `α`): correct

- **`α ∈ CT_{3}(Z)`.** `α` maps `0(2), 1(4), 3(4)` canonically onto `0(3), 1(3), 2(3)`, via `2t ↦ 3t`,
  `1 + 4t ↦ 1 + 3t` and `3 + 4t ↦ 2 + 3t`.
- **Item 2 of the Conway node (unreviewed there, checked here): correct.**
  - Which piece contains `α^n(x)` is read from the 2-adic coordinate. `α` acts on that coordinate by the piece's
    formula.
  - On `Z_2`, each branch is a homeomorphism of its piece onto `Z_2`. For example, `1 + 4t ↦ 1 + 3t` is onto
    because `3` is a 2-adic unit. The branches are expanding, since `|3/2|_2 = 2` and `|3/4|_2 = 4`.
  - So the forward coding `x_2 ↦ Φ(x)_(≥0)` is a homeomorphism onto `{0,1,2}^N`.
  - Symmetrically, `α^(−1)` has three full branches `i(3) → Z_3`, expanding in `Z_3`, and they are read from `x_3`.
    So `x_3 ↦ Φ(x)_(<0)` is a homeomorphism.
  - So `Φ` is a homeomorphism of `Z_2 × Z_3` onto `{0,1,2}^Z` with `Φ ∘ α = σ ∘ Φ`.
- **Indecomposable.** Powers of the full shift are mixing, so no power fixes a proper nonempty clopen set. So Σ is
  `(∅, X)`, and every part has base `X`.
- **The holonomy.** `F_2^(−1)(z) = (4z + 1)/3`, so `F_2^(−1) F_1(y) = y + 2/3`.
  - `2/3` is a unit at every `ℓ ≥ 5`, so every fibre ball is `Z_ℓ`, and every part is `Ẑ`.
  - So `α` permutes no nontrivial residue-class partition.
- **Sanity check.** Invariance mod 5 fails at `n = 5`, since `α(5) = 4`.

## 3. Scope of the interpretation

- **"Saddles are not the obstruction"** is justified by the Corollary, as stated there: a mixing component always
  carries a nontrivial holonomy.
- **"The block is Σ"** is accurate as a reduction. Theorem R needs Σ as input. Whether Σ exists and is computable
  for rank-two and mixed-sign elements is open, and the node says so, with the two failure modes correctly
  described.

## Verdict

**PASS.**
- Theorem R holds: given Σ, 21.74(a) is decidable for every `g ∈ CT(Z)`.
- The Haar-measure holonomy step is correct.
- The Corollary holds: Conway's amusical permutation permutes no nontrivial residue-class partition. Its input,
  item 2 of the Conway full-shift node, is checked here.
- Repairs are clarity only: the translation-holonomy case in the cycle test, and translation bounds in `E_ℓ`.
