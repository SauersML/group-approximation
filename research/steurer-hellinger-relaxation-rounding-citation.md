---
rg: 2
id: steurer-hellinger-relaxation-rounding-citation
kind: route
title: Import the definition (2.6)-(2.8) of sdp+, Theorem 3 and Theorem 8 of Steurer, Improved Rounding for Parallel Repeated Unique Games (APPROX-RANDOM 2010)
target: steurer-hellinger-relaxation-rounding
requires: []
---

This is a literature import, and credit is the authors' in full. The
quotations come from text that `pypdf` extracted on 2026-09-19 from
`dsteurer.org/paper/roundpar2.pdf`, the same file that
`steurer-parallel-repeated-unique-games-rounding-citation` quotes. Line breaks
and hyphenation have been undone, and symbols have been transcribed
(`𝓁` as `ℓ`, the extracted `⁄=` as `≠`).

## Quotations

* **Section 1.1, statement.** "The key result in [2] is a lower bound on
  sdp+(G) in terms of the semidefinite value of G. We prove the following
  improved bound (which is optimal up to the constants hidden in the
  O(·)-notation). Theorem 3. For every unique G with alphabet size k and
  sdp(G)≥1−ε, sdp+(G)≥1−O(ε log k)."
* **Section 1.1, role.** "The approach of [2] for proving lower bounds on the
  value of repeated games Gℓ involves an intermediate relaxation, denoted here
  sdp+(G), which is “sandwiched” between opt(G) and sdp(G)."
* **Section 2.2, definition.** "The Hellinger value of G is defined as
  sdp+(G) := max E_{(u,v,π)∼G} Σ_{i∈Σ} ⟨f_{u,i}, f_{v,π(i)}⟩, (2.6) where we
  maximize over all collections {f_{u,i}}_{u∈V,i∈Σ} of nonnegative functions on
  Ω such that Σ_{i∈Σ} ‖f_{u,i}‖² = 1 (u∈V), (2.7)
  supp(f_{u,i}) ∩ supp(f_{u,j}) = ∅ (u∈V, i≠j∈Σ). (2.8) Here, (Ω,µ) is some
  probability space and the norms and inner products for functions
  f,g : Ω→ℝ are defined as ⟨f,g⟩ := ∫_Ω fg dµ and ‖f‖ := ⟨f,f⟩^{1/2}. Without
  loss of generality, we could assume Ω = [0, 1] and that µ is the usual
  Lebesgue measure."
* **Section 2.2, Theorem 8.** "Our result relies on the following theorem of
  [2]. Theorem 8 ([2]). If G is a unique game with sdp+(G)≥1−ε, then
  opt(G)≥1−2√(2ε)."
* **Section 2.2, Lemma 9 and its proof idea.** "Furthermore, we can lower bound
  sdp+(Gℓ) in terms of sdp+(G) as expected. This lemma follows from the fact
  that we can construct a solution for sdp+(Gℓ) by taking appropriate tensor
  products of the functions f_{u,i} that form an optimal solution for
  sdp+(G). Lemma 9. For every unique game G, we have sdp+(Gℓ)≥sdp+(G)ℓ."
* **Section 3.** "Theorem (Restatement of Theorem 3). For every unique G with
  alphabet size k and sdp(G)≥1−ε, sdp+(G)≥1−O(ε log k)."

## Reading

1. **Constant and logarithm.** The logarithm is read as the natural one, and
   `O(ε log k)` as `C_3 ε ln k` for one absolute constant `C_3`. Enlarging a
   constant keeps the statement true, so `C_3 >= 1` may be assumed. Theorem 3
   is stated "for every unique G with alphabet size k", with no condition on
   `ε` or `k`. It is used here only for `k >= 2`, where `ln k > 0`.
2. **"max" read as supremum, over every probability space.** The definition
   lets "(Ω,µ)" be "some probability space", and the WLOG remark says the value
   does not change if it is fixed to `[0,1]`. In (H0) the value is read as the
   supremum over all probability spaces and feasible collections. This is the
   reading under which Lemma 9's tensor-product solutions, which live on
   `Ω^ℓ`, are feasible. Theorem 8's hypothesis `sdp+(G) >= 1 − ε` is then a
   statement about this supremum, and so is (H2). No attainment is used
   downstream: every use exhibits feasible solutions and takes a supremum.
3. **No extra hypotheses.** Theorem 8 is stated for every unique game, with no
   condition on alphabet, bipartiteness or weights. Steurer's constraint
   distribution `(u,v,π)∼G` covers bipartite games with rational edge weights,
   which are the games of `sqrt-scale-unique-games-hardness`.
4. **What is not imported.** Lemma 9 is quoted for context only. The
   downstream claim `correlated-products-cannot-substitute-rounds-for-alphabet`
   reproves its tensor step in a more general form, and does not rely on the
   quotation.
