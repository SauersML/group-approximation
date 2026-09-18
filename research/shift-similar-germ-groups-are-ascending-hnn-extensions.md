---
rg: 2
id: shift-similar-germ-groups-are-ascending-hnn-extensions
kind: claim
title: For any infinite shift-similar G, the extended germ group is the ascending HNN extension of Germs(G) by the shift, H_n(G)/FSym is its index-zero power, and it has type F_min(m,n-1) when Germs(G) has type F_m; strong shift-similarity is exactly two-sidedness of the index character in Sigma^1
requires:
  - houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
  - characters-living-on-m-plus-one-factors-lie-in-sigma-m
  - infinite-shift-similar-groups-need-not-be-strongly-shift-similar
distinct_from:
  houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group: that computes H_n(G)/FSym for strongly shift-similar G, where Ĝ = Germs(G) ⋊ Z; this does every infinite shift-similar G, where Ĝ is an ascending HNN extension, and explains the n >= m+1 threshold of Mallery-Zaremsky Question 5.13.
  fg-infinite-shift-similar-groups-are-strongly-shift-similar: that is the open question; this restates it as a one-sidedness statement for Sigma^1 of finitely generated subgroups of the near symmetric group containing the shift.
---

**ESTABLISHED** (lane proof, below). Imports: the refereed `characters-living-on-m-plus-one-factors-lie-in-sigma-m`;
Renz's kernel criterion as imported in `houghton-like-germ-groups-are-index-zero-products-proof` (I1); Geoghegan
§7.2 Exercises 1 and 3 (extensions, graphs of groups), read at source (hash in `finitary-mixing-preserves-type-f-m`); and, for item 4
only, Brown's `Σ^1` criterion for ascending HNN extensions (K. S. Brown, *Trees, valuations, and the
Bieri–Neumann–Strebel invariant*, Invent. Math. 90 (1987)), quoted from memory. Not independently reviewed.

**Setting.** `G <= Sym(N)` is infinite and shift-similar. So `FSym(N) <= G` (Mallery--Zaremsky Theorem 3.12), and
`c(x) = s̄^-1 x s̄` maps `Germs(G)` into itself (step 1 of `infinite-shift-similar-groups-need-not-be-strongly-shift-similar`).
Put `Ĝ = < Germs(G), s̄ > <= NearSym(N)`, `η` = near index, and `Q_n(Ĝ) = {(x_k) ∈ Ĝ^n : Σ η(x_k) = 0}`.

**Statement.**
1. `Ĝ ≅ Germs(G) *_c`, the ascending HNN extension with stable letter `s̄`. Its index-zero part is
   `∪_(j>=0) c^-j(Germs(G))`, a strictly increasing union exactly when `G` is not strongly shift-similar.
2. For every `n >= 1`, recording ray germs gives `H_n(G)/FSym([n] x N) ≅ Q_n(Ĝ)`.
3. If `Germs(G)` has type `F_m` (`m >= 1`), then `Q_n(Ĝ)` has type `F_(min(m, n-1))` for `n >= 2`. If moreover `G` is
   strongly shift-similar, `Q_n(Ĝ)` has type `F_m` for all `n`.
4. **`Σ^1` reformulation.** The following are equivalent.
   - (a) Some finitely generated infinite shift-similar group is not strongly shift-similar.
   - (b) Some finitely generated `Δ <= NearSym(N)` containing `s̄` has `ker(η|_Δ)` not finitely generated while
     `[η] ∈ Σ^1(Δ)`. Here the monoid `{η >= 0}` acts by `g·x = g x g^-1`; in the opposite convention, read `[-η]`.

   So `fg-infinite-shift-similar-groups-are-strongly-shift-similar` says: for finitely generated subgroups of the
   near symmetric group containing the shift, the index character lies in `Σ^1` on both sides or on neither.

**Proof.**
1. The natural map from `Germs(G) *_c` onto `Ĝ` is injective. A normal form `t^i b t^-j` (`i, j >= 0`) maps to
   `s̄^i b s̄^-j`, which has index `i - j`. If it is trivial then `i = j` and `b = 1`. The index-zero part is
   `∪ s̄^j Germs s̄^-j`, and it is stationary iff `c(Germs) = Germs`.
2. Follow step 2 of `houghton-like-germ-groups-are-index-zero-products-proof`, with one change in the onto part. A
   tuple `(s̄^(c_k) y_k)` with `Σ c_k = 0` has `y_k ∈ c^-j(Germs)` for some `j`. Choose `a_k >= max(j, -c_k)` and
   `b_k = a_k + c_k`. Then `c^(a_k)(y_k) ∈ Germs(G)` is realized by some `g'_k ∈ G`, and
   `[M_-, σ(g'_1..g'_n), M_+]` has the prescribed germs. The homomorphism and kernel parts are unchanged.
3. `Ĝ` is a graph of groups with vertex and edge group `Germs(G)`, so it has type `F_m` (Geoghegan §7.2 Exercise 3).
   The character `ψ = Σ_k η∘pr_k` of `Ĝ^n` is discrete and nonzero on every factor. With `m' = min(m, n-1)`, we have
   `n >= m'+1` factors of type `F_(m')`, so `[±ψ] ∈ Σ^(m')(Ĝ^n)` by the refereed node. By Renz, `ker ψ = Q_n(Ĝ)` has
   type `F_(m')`. In the strong case, `Q_n(Ĝ)` contains `Germs(G)^n` as a normal subgroup with quotient
   `Z^(n-1)`, so it has type `F_m` for all `n` (Geoghegan §7.2 Exercise 1).
4. (a ⇒ b): take `Δ = < Germs(G), s̄ > = Ĝ`, which is finitely generated because `Germs(G)` is. By item 1 it is an
   ascending HNN extension over a finitely generated base, which is Brown's characterization of `[η] ∈ Σ^1`
   (stable letter `s̄`, `s̄^-1 B s̄ ⊆ B`). Its index-zero part is strictly increasing, hence not finitely generated.
   (b ⇒ a): Brown gives `Δ = B *_(t)` ascending with `B` finitely generated in `ker η` and `η(t) = 1`. Any other
   element of index 1 can serve as stable letter after enlarging `B` to some `t^j B t^-j`, so take `t = s̄`. Then
   `c(B) ⊆ B`, and `c(B) ≠ B`, since otherwise `ker(η|_Δ) = B`. The preimage of `B` in `Sym(N)` is finitely
   generated, because `FSym` is the normal closure of one transposition. It is shift-similar, since `c(B) ⊆ B`, and
   not strongly shift-similar. ∎

**Reading.**
- The threshold `n >= m+1` in sentence 2 of Mallery--Zaremsky Question 5.13 is, at germ level, exactly the Meinert
  count for a one-sided index character. For `G = FSym(N)`, where `Germs = 1` and `Ĝ = Z`, item 3 gives
  `Q_n = Z^(n-1)`, of type `F_infinity`, while `H_n(FSym) = H_n` is only `F_(n-1)`. That obstruction lives in `FSym`
  (`G` is not finitely generated), not in germs. (Correction: the first landing said `G = 1`, which is finite and
  outside this node.)
- For strongly shift-similar `G` the character is two-sided and the threshold disappears. This matches
  `strongly-shift-similar-type-f-m-passes-to-houghton-like-groups`.
- A prototype of (b) is Thompson's `F`. It is an ascending HNN extension of itself with `[χ_0]` one-sided in
  `Σ^1(F)`. A faithful near action of `F` on `N` with `x_0` acting as the shift and index character `χ_0` would answer
  Question 3.18 for finitely generated groups. This lane found no such near action. The germs of `F` at fixed
  points of interval actions are abelian, which kills the obvious candidates.

**Lesson for general BH.** Germ-level questions about permutation envelopes are `Σ`-invariant questions about a
finitely generated subgroup of the near symmetric group containing the shift. Strong shift-similarity (the class
where envelopes behave) is two-sidedness of the index character in `Σ^1`. Finiteness thresholds such as
`n >= m+1` are Meinert counts. So the whole `Σ`-toolkit (Brown, Renz, Meinert, Bieri–Geoghegan) applies to envelope
design. When searching for new envelopes, test the index character first: a one-sided index character forces
Houghton-type thresholds, and a two-sided one removes them.
