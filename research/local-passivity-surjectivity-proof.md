---
rg: 2
id: local-passivity-surjectivity-proof
kind: route
title: Configurations with finitely many active sites form finite invariant pieces, and they are dense
target: local-passivity-preserving-injective-automata-are-surjective
requires: []
artifacts:
  - research/artifacts/ideas-gottschalk-3-2026-09-14.md
---

Complete direct proof. Notation as in the target: `Φ` is an injective cellular automaton on `A^G`, `W ∋ 1` is
finite, `P ⊆ A^W` contains `a^W`, `Act(x) = { g : (g⁻¹x)|_W ∉ P }`, and `Φ` satisfies (1) and (2).

1. **Finite pieces.** Let `x₀` have finite active set `E = Act(x₀)`. Put
   `D = { z ∈ A^G : z = x₀ on G \ E, and Act(z) ⊆ E }`.
   A configuration in `D` is determined by its values on `E`, so `|D| ≤ |A|^|E|`. Also `x₀ ∈ D`.
2. **`Φ` maps `D` into itself.** Let `z ∈ D`.
   - For `g ∉ E` we have `g ∉ Act(z)`, so (1) gives `Φ(z)(g) = z(g) = x₀(g)`. So `Φ(z) = x₀` on `G \ E`.
   - By (2), `Act(Φ(z)) ⊆ Act(z) ⊆ E`.
   So `Φ(z) ∈ D`.
3. **`x₀` lies in the image.** `Φ` restricts to an injective map from the finite set `D` to itself, which is a
   bijection. So `x₀ = Φ(z)` for some `z ∈ D`.
4. **Configurations with finite active set are dense.** Let `p` be a pattern on a finite set `F ⊆ G`. Extend it
   by the symbol `a` outside `F` to a configuration `x`. If `gW ∩ F = ∅` then `x(gw) = a` for all `w ∈ W`, so
   `(g⁻¹x)|_W = a^W ∈ P` and `g ∉ Act(x)`. Hence `Act(x) ⊆ F W⁻¹` is finite, and `x` lies in the cylinder of `p`.
5. **Conclusion.** `Φ` is continuous and `A^G` is compact, so `Φ(A^G)` is closed. By steps 3 and 4 it contains a
   dense set, so `Φ(A^G) = A^G`.

No property of `G` is used, and the memory and local rule of `Φ` are arbitrary.

**Where the hypotheses enter.**
- (1) enters only in step 2, first bullet.
- (2) enters only in step 2, second bullet. For `W = {1}` it follows from (1): a site with a passive symbol is
  left unchanged, so it stays passive.
- The difference from `passive-fixing-injective-automata-surjective-proof` is the piece: that proof requires every
  site of `E` to stay active (`x(g) ∉ P` on `E`). Here the piece only requires the active set to stay inside `E`.
  That is why "active sites stay active" is not needed.

**Bounded creep under (1) alone.** If `gW ∩ Act(x) = ∅`, then every site of `gW` is passive in `x`. By (1),
`Φ(x) = x` on `gW`, so `g ∉ Act(Φ(x))`. So `Act(Φ(x)) ⊆ Act(x) W⁻¹` always holds under (1). Weakening (2) to
bounded growth is therefore the same as dropping it.
