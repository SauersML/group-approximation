---
rg: 2
id: fw-twisted-normalizing-shell-action-proof
kind: route
title: FW straightens the shift into a genuine equivariant bijection of index m; orbits and index force every orbit to be finite and bounded, so P is finite
target: fw-inputs-admit-no-twisted-normalizing-genuine-shell-action
requires:
  - genuine-action-shell-envelopes-generalize-the-regular-shell
---

Suppose the near equality holds. Write `ρ' = ρ∘φ`, an action of `P` on `N` with **the same
orbits as `ρ`**, because `φ` is surjective. A **near permutation** is a bijection between
cofinite subsets of `N`. Its index is `ind(f) = |N \ im f| - |N \ dom f|`, and two near
permutations that agree off a finite set have the same index. `ind(s^m) = m`.

1. **Straightening (FW).** The hypothesis says `s^m ρ'_g = ρ_g s^m` off a finite set, for
   every `g`. Let `P` act on `N × N` by `g(x,y) = (ρ'_g x, ρ_g y)`. Then the graph `Γ` of
   `s^m` is a commensurated subset. By FW there is a `P`-invariant `Γ'` with `Γ' Δ Γ`
   finite. Let `Γ''` be the set of pairs of `Γ'` whose first coordinate and second
   coordinate each occur in exactly one pair of `Γ'`. It is `P`-invariant, differs from
   `Γ` by a finite set, and is the graph of an equivariant bijection
   `f : (X, ρ') -> (Y, ρ)` between cofinite invariant sets `X, Y`. Here `f = s^m` off a
   finite set, so `ind(f) = m`. Replacing `f, ρ', m` by `f^-1, ρ, -m` and `φ` by `φ^-1`
   if needed, assume `m > 0`.
2. **Orbits.** `X` and `Y` are cofinite and invariant, so they contain every infinite orbit.
   Let `N_fin` be the union of the finite orbits. `f` maps orbits onto orbits of the same
   cardinality, so it maps `N \ N_fin` bijectively onto itself, and `X ∩ N_fin` onto
   `Y ∩ N_fin`. The index is additive over this splitting, and the infinite part
   contributes `0`. So `f` restricted to `N_fin` is a near permutation of `N_fin` of index
   `m`.
3. **Chains.** Choose `M` such that `f = s^m` on `[M, ∞)`. Enlarge it so that every finite
   orbit meeting `[M', ∞)` lies in `[M, ∞)`: only finitely many orbits meet `[0, M)`. For a
   finite orbit `O ⊆ [M, ∞)`, `f(O) = O + m` is a finite orbit. If `O ⊆ [M+m, ∞)`, then
   `O - m = f^-1(O)` is one too. So the finite orbits in `[M, ∞)` form disjoint chains
   `O_i + km`, `k >= 0`, with base orbits `O_i` whose minimum lies in `[M, M+m)`. There are
   at most `m` bases. On their union `F`, `s^m` shifts each chain by one step, so as a near
   permutation of `N_fin` it has index `Σ_i |O_i|`. It agrees with `f` off a finite set, so
   `Σ_i |O_i| = m`.
4. **Density.** Chain `i` puts at least `|O_i|(L - c)` points into `[M, M + Lm)`, for a
   constant `c` independent of `L`. So `F` has at least `m(L - c)` of the `Lm` points
   there, and `[M, ∞) \ F` is finite. An infinite orbit has infinitely many points in
   `[M, ∞)`, so **every orbit is finite**. The orbits in `[M, ∞)` have at most `m` points,
   and there are finitely many others, so all orbits have at most `K` points for some `K`.
5. **Conclusion.** `P` is finitely generated (a countable FW group has property FA, hence is
   finitely generated). So it has finitely many homomorphisms to `Sym(K)`. The
   intersection of their kernels is a finite-index subgroup acting trivially on every
   orbit, hence on `N`. Every nontrivial element moves infinitely many points, so that
   subgroup is trivial and `P` is finite. This contradicts the hypothesis. `∎`
