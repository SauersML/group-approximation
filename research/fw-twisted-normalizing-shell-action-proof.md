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
3. **Residue classes.** Choose `M` such that `f(a) = a + m` for every `a in X ∩ [M, ∞)`,
   and such that `[M, ∞) ⊆ X`. Let `A = N_fin ∩ [M, ∞)`. **For all but finitely many `a`,
   `a in A` iff `a + m in A`.**
   - If `a in A`, then `f` maps the finite orbit of `a` onto a finite orbit containing
     `f(a) = a + m`.
   - Conversely, `Y \ f(X ∩ [M, ∞))` is finite. Outside it, `a + m in N_fin` means
     `a + m = f(a)` with `a >= M`, and the orbit of `a` is `f^-1` of a finite orbit.

   So along each residue class mod `m`, membership in `A` is eventually constant, and
   `A` agrees up to a finite set with `⋃_{r in R} (r + mN)` for a set `R` of residues.
4. **Index.** On `N_fin`, `f` agrees with `s^m` off a finite set, and `N_fin` agrees with
   `A` up to a finite set. As a near permutation of `N_fin`, `s^m` shifts each of the `|R|`
   arithmetic rays by one step, so its index is `|R|`. By step 2 it is `m`. So `R` is
   every residue, and `[M, ∞) \ N_fin` is finite. An infinite orbit would have infinitely
   many points there, so **every orbit is finite**.
5. **Bounded orbits.** Call a finite orbit `O` a *base* if it is not `O' + m = f(O')` for an
   orbit `O' ⊆ [M, ∞)`. A base contains no point of `f(X ∩ [M, ∞))`: if `a = f(b)` with
   `b >= M`, then `O = f(orbit of b) = (orbit of b) + m`. That set has finite complement,
   so there are finitely many bases. Every orbit meeting `[M+m, ∞)` either is a base or
   comes from an orbit with smaller minimum by adding `m`. Iterating down, every orbit is a
   translate of a base or one of the finitely many orbits meeting `[0, M+m)`. So all orbits
   have at most `K` points for some `K`.
6. **Conclusion.** `P` is finitely generated, since a countable FW group has property FA
   and so is finitely generated. So it has finitely many homomorphisms to `Sym(K)`. The
   intersection of their kernels is a finite-index subgroup acting trivially on every
   orbit, hence on `N`. Every nontrivial element moves infinitely many points, so that
   subgroup is trivial and `P` is finite. This contradicts the hypothesis. `∎`
