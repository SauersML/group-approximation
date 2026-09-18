---
rg: 2
id: lossless-monomial-recursions-give-simple-completions
kind: claim
title: A lossless row-monomial recursion on a free algebra has a monomial self-similar quotient, and if every surviving word erases to the empty word along some branch, its completion is finitely presented and simple
distinct_from:
  scalar-descendants-make-completions-simple: that is the abstract simplicity lemma; this supplies its hypothesis for recursions given by lossless transducers, where no cancellation can occur.
  noninjective-ln-completions-have-self-similar-bases: that identifies the base of the completion as B/J for any recursion; this shows J is spanned by the words that die when the recursion is a lossless transducer, so B/J is a monomial algebra.
---

**ESTABLISHED** through `lossless-monomial-recursions-give-simple-completions-proof` (lane proof,
bh-algebra, elementary, not reviewed).

**Setting.** `B = K<G>` free on a finite set `G`, `d >= 2`, and a *row-monomial* recursion
`ψ : B -> M_d(B)`: for each `g ∈ G` and state `i`, the row `ψ(g)_(i,·)` has at most one nonzero entry,
and that entry is a word in `G` (the empty word `1` allowed). Then for every word `w` and every branch
`μ ∈ {1..d}^N`, `ψ_N(w)_(μ,·)` has at most one nonzero entry. Call it `τ_μ(w)`, in column `δ_μ(w)`.
A word *dies* if `ψ_N(w) = 0` for some `N`.

**Hypotheses.**
- (L) **Lossless.** For each state `i`, `w ↦ (δ_i(w), τ_i(w))` is injective on words with nonzero image.
- (P) **Peel state.** Some state `p` has `ψ(u)_(pp) = 0` for every nonempty word `u`.
- (E) **Erasure.** Every word that does not die has `τ_μ(w) = 1` for some branch `μ`.

**Claim.**
1. Under (L), the self-similar kernel `J` is spanned by the words that die. So `B/J` is the monomial
   algebra `K<G>/(dying words)`.
2. Under (L), (P) and (E), `O_ψ(B)` is a finitely presented simple algebra containing `B/J`.
3. **Application.** Let `M = K<x_1..x_m>/(W)` be a monomial algebra, `W` a set of words, and
   `G ⊇ {x_1..x_m}`. Suppose that in a recursion as in 2, a word in the `x_i` dies exactly when it has a
   factor in `W`. Then `M` embeds in the finitely presented simple algebra `O_ψ(B)`.
