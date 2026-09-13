---
rg: 2
id: thompson-f-interval-stabilizer-cosets-separate-only-if-amenable
kind: claim
title: On pointwise stabilizers of finite unions of intervals, and on amenable subgroups, following models separate the commutator only if Thompson's F is amenable
distinct_from:
  thompson-f-end-rigid-schreier-graphs-are-amenable: that shows some of these coset spaces have Følner sets; this shows that invariant means on them charge the commutator's moved points only if F is amenable.
  thompson-f-is-lea-only-if-amenable: that collapses local embeddability into amenable groups to amenability; this collapses separating following models on these coset spaces to amenability.
  thompson-f-spatial-permutation-models-almost-commute: that covers F-sets over the interval whose points moved by c lie over [1/4,3/4]; the coset spaces here with nondegenerate Z are not of that kind, since c moves points whose endpoint images all lie near 0 and 1.
artifacts:
  - research/artifacts/thompson-f-nonspatial-f-sets-2026-09-13.md
---

**ESTABLISHED.** **Setting.**
- `Z ⊆ [0,1]` is a finite union of closed intervals and points with dyadic endpoints, and `0, 1 ∈ Z`.
- `F_Z = {f ∈ F : f(u) = u for all u ∈ Z}`, and `Ω_Z = F/F_Z`. This is the set of restrictions
  `f|_Z`, with `F` acting by composition.
- `c`, `Moved`, means and labelled models are as in
  `thompson-f-following-models-separate-iff-mean-charges-commutator`.

**Statement.**
1. If `Z` is finite, every invariant mean on `Ω_Z` has `m(Moved(c)) = 0`.
2. If `Z` contains a nondegenerate interval and some invariant mean on `Ω_Z` has
   `m(Moved(c)) > 0`, then `F` is amenable.
3. If `H ≤ F` is amenable and `F/H` carries an invariant mean, then `F` is amenable.

**Consequence.**
- On `Ω_Z`, and on `F/H` for amenable `H`, labelled models with error `→ 0` separate the commutator
  only if `F` is amenable, by item 1 of the companion claim.
- Conversely, if `F` is amenable, the regular `F`-set (`Z = [0,1]`, `H = e`) carries invariant means
  with `m(Moved(c)) = 1`.
- So on these `F`-sets following models give no route to soficity independent of amenability, just as
  in `thompson-f-is-lea-only-if-amenable`.

**Instances.**
- **Amenable subgroups (item 3):** `H = e`, `⟨x_0⟩`, and every elementary amenable subgroup.
- **End-rigid cosets (item 2).** `F_[0,a]`, the elements that are the identity on `[a,1]`, is `F_Z` for
  `Z = {0} ∪ [a,1]`; symmetrically for `F_[a,1]`.
  - Their Schreier graphs have Følner sets, by `thompson-f-end-rigid-schreier-graphs-are-amenable`.
  - For `F_[0,a]`, `c` moves `f|_Z` whenever `f(a) < 3/4`, so the bound of
    `thompson-f-spatial-permutation-models-almost-commute` does not apply.
- **Other interval stabilizers (item 2):** the elements supported in `[a,b]` (`Z = [0,a] ∪ [b,1]`),
  and pointwise stabilizers of any finite union of dyadic intervals.
- **Finite sets (item 1):** pointwise stabilizers of finite sets of dyadics. The spatial bound
  already covers these.

**Scope.** Elementary, and no novelty is claimed. It leaves `thompson-f-is-sofic` open. The survivors
are recorded in the artifact: an `F`-set with an invariant mean charging `Moved(c)` must come from a
non-amenable co-amenable subgroup outside these families, or combine infinitely many orbit types.

Proof route: `thompson-f-interval-stabilizer-cosets-amenability-transfer-proof`.
