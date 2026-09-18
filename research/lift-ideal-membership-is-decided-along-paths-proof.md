---
rg: 2
id: lift-ideal-membership-is-decided-along-paths-proof
kind: route
title: The set of prefixes with no good section is a finite subtree by König's lemma, and a maximal element of it would be lifted into M
target: lift-ideal-membership-is-decided-along-paths
requires: []
---

**Two facts.**
- Sections of relators are relators: a word acting trivially has trivially acting sections.
- A relator has trivial root permutation.

So for every `u ∈ X^*`, `w|_u ∈ N` has trivial root permutation.

**Proof.**
- *The bad set.* Let `D = {u ∈ X^* : w|_{u'} ∉ M for every prefix u' of u, including u}`. `D` is
  prefix-closed, and every vertex of `X^*` has `|X|` children.
- *`D` is finite.* If `D` were infinite, König's lemma would give `ξ ∈ X^ω` with every prefix in `D`,
  so no section of `w` along `ξ` would lie in `M`. That contradicts the hypothesis.
- *`D` is empty.* If `D` is nonempty, take `u ∈ D` maximal. For each letter `x`, the word `ux` is not
  in `D`, while all of its proper prefixes are. So `w|_{ux} = (w|_u)|_x ∈ M`. Since `w|_u` has trivial
  root permutation, lift-closedness of `M` gives `w|_u ∈ M`, contradicting `u ∈ D`. Hence `D = ∅`.
- *Conclusion.* In particular the empty word is not in `D`, so `w = w|_ε ∈ M`.

**The corollary.** The "only if" direction is `n = 0`. For "if", apply the theorem to
`M = ⟨⟨R⟩⟩_lift`, which is contained in `N` because relator kernels are lift ideals. `∎`
