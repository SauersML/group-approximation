---
rg: 2
id: infinite-shift-similar-groups-need-not-be-strongly-shift-similar
kind: claim
title: There is an infinite (not finitely generated) shift-similar group that is not strongly shift-similar, answering Mallery-Zaremsky Question 3.18 as stated
requires:
  - houghton-like-groups-are-strongly-shift-similar
distinct_from:
  fg-infinite-shift-similar-groups-are-strongly-shift-similar: that asks the same for finitely generated groups (OPEN), which is the version that matters for Observation 5.12 and Question 5.13 of the source; this answers the question as printed, with an example that is not finitely generated.
  strongly-shift-similar-type-f-m-passes-to-houghton-like-groups: that proves the finiteness transfer for strongly shift-similar groups; this shows that the class of infinite shift-similar groups is strictly larger.
---

**ESTABLISHED** (lane proof, elementary, below; not independently reviewed; no priority claimed). A bounded
priority search found no later paper on the question. It covered the Semantic Scholar citations of the source,
which include the planted positive arXiv:2405.18354, plus arXiv metadata and web searches, 2026-09-18.

**The question.** Mallery--Zaremsky, arXiv:2202.00822v2, Question 3.18 (label `quest:not_strong`), verbatim:
"Does there exist an infinite shift-similar group that is not strongly shift-similar?" The source adds, before
Definition 3.17, that the germ shifting map is always injective, and: "We see no reason why it should always be the
case, but we do not know of an example where it is not."

**Setting (the source's conventions).** `N = {1, 2, ...}`.
- `psi_j(g) = s_(g(j))^-1 ∘ g|_(N\{j}) ∘ s_j` (Definition 3.1).
- `G` is shift-similar if `psi_j(G) ⊆ G` for all `j`.
- An infinite shift-similar `G` contains `FSym(N)` (Theorem 3.12). The map `psi_infinity : G/FSym -> G/FSym` is
  induced by any `psi_j`. `G` is strongly shift-similar if `psi_infinity` is onto (Definition 3.17).

**The example.** For `k >= 0` let

    rho_k = ∏_(i >= k+2) (2^i - k, 2^i - k + 1),

a product of disjoint transpositions, since `2^(i+1) - k > 2^i - k + 1`. Put
`G = < FSym(N), rho_0, rho_1, rho_2, ... > <= Sym(N)`.

**Statement.** `G` is infinite and shift-similar, and `psi_infinity` is not onto. So `G` is not strongly
shift-similar. `G` is not finitely generated.

**Proof.** Write `ḡ` for the class of `g` modulo `FSym(N)`, and `Γ = G/FSym(N) = < rho̅_k : k >= 0 >`.
1. **`psi_j` is conjugation by the shift at infinity.** For large `i`, `s_j(i) = i+1`, and `g(i+1) > g(j)`, so
   `psi_j(g)(i) = g(i+1) - 1`. With `σ(i) = i+1`, this says `psi_j(g)` agrees with `σ^-1 g σ` off a finite set. Put
   `c(ḡ) = (σ^-1 g σ)‾`. This is conjugation by the shift in the near symmetric group, hence a homomorphism, and
   `(psi_j(g))‾ = c(ḡ)`.
2. **`c(rho̅_k) = rho̅_(k+1)`.** For `i = 2^m - (k+1)` we get `rho_k(i+1) - 1 = 2^m - k`. For `i = 2^m - k` we get
   `rho_k(i+1) - 1 = 2^m - k - 1`. Every other large `i` is fixed. So `σ^-1 rho_k σ` agrees at infinity with the
   product of the transpositions `(2^m - (k+1), 2^m - (k+1) + 1)`, i.e. with `rho_(k+1)`.
3. **Shift-similar.** `G` is the full preimage of `Γ` in `Sym(N)`, because `FSym(N) <= G`. For `g ∈ G`,
   `(psi_j(g))‾ = c(ḡ) ∈ c(Γ) = < rho̅_k : k >= 1 > ⊆ Γ`, so `psi_j(g) ∈ G`. `G` is infinite since it contains
   `FSym(N)`.
4. **`rho̅_0` is not in the image `c(Γ) = < rho̅_k : k >= 1 >`.** An element of the image is the class of a word `w`
   in `rho_1, ..., rho_K` for some `K`.
   - For `m >= K+2` put `W_m = [2^m - K, 2^m]`. These windows are pairwise disjoint.
   - For `1 <= k <= K`, the factor of `rho_k` at `i = m` is `(2^m - k, 2^m - k + 1)`, which lies in `W_m`. The factors
     with `i < K+2` move boundedly many points.
   - So `w` fixes `2^m + 1` for every large `m`, because `2^m + 1` lies in no window: `2^(m+1) - K > 2^m + 1`.
   - But `rho_0` moves every `2^m + 1` with `m >= 2`. So `w` and `rho_0` differ at infinitely many points, and
     `w̄ ≠ rho̅_0`.
5. **Not finitely generated.** The same argument, with the windows `[2^m - K, 2^m + 1]`, shows that
   `rho̅_(K+1) ∉ < rho̅_0, ..., rho̅_K >`, since `rho_(K+1)` moves `2^m - K - 1`. So `Γ` is a strictly increasing
   union and is not finitely generated. Neither is `G`, which maps onto `Γ`. ∎

**What stays open.** The source ties Question 3.18 to Observation 5.12 ("`H_1(G)` is
finitely generated iff `G` is strongly shift-similar", for finitely generated `G`). It notes that a "no" answer would make that observation uninteresting. The observation needs a
finitely generated example to have content, and so does the remaining case of Question 5.13. That version is
`fg-infinite-shift-similar-groups-are-strongly-shift-similar` (OPEN).
