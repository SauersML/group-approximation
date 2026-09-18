---
rg: 2
id: finite-cloning-group-with-undecidable-lamp-stabilizer
kind: route
title: "Q1 no: a coset-tree cloning system on finite groups with a non-recursive lamp stabilizer has unsolvable word problem, so is not coCF"
target: some-finite-cloning-system-group-is-not-locally-cocf
requires:
  - finite-cloning-groups-realize-every-lamplighter-over-thompson-f
---

Complete argument, given `finite-cloning-groups-realize-every-lamplighter-over-thompson-f`.

1. **A computable independent family in F.** The generator `x_0` is `t/2` on
   `[0,1/2]`, `t - 1/4` on `[1/2,3/4]` and `2t - 1` on `[3/4,1]`. It maps `J_0 := [1/4,1/2]`
   onto `[1/8,1/4]`. So the intervals `J_i := x_0^i(J_0) = [2^{-i-2}, 2^{-i-1}]` have
   pairwise disjoint interiors. Fix a nontrivial `y ∈ F` supported in `[5/16, 7/16]`,
   inside the interior of `J_0`. It exists because `F_{[a,b]} ≅ F` for dyadic `a < b`.
   Fix a word `ŷ` in `x_0^{±1}, x_1^{±1}` for `y`. Put `g_i := x_0^i y x_0^{-i}`, which is
   supported in the interior of `J_i`.
2. **Subgroups H_S.** For `S ⊆ N` let `H_S := ⟨g_i : i ∈ S⟩ ≤ F`. The `g_i` commute and
   have disjoint supports, so every `h ∈ H_S` is a finite product `∏_{i∈S} g_i^{n_i}`,
   and `h` restricted to `J_j` is the identity for `j ∉ S`. Since `g_j` is not the
   identity on `J_j`, we get **`g_i ∈ H_S ⇔ i ∈ S`**.
3. **Reduction.** Take `H = H_S` and `A = Z/2` in the claim. This gives a cloning system
   on finite groups `G_n` and `Γ_S := ⟨x_0, x_1, t⟩ ≤ T(G_*)`, with `[t, f] = 1 ⇔ f ∈ H_S`.
   The word `w_i := t x_0^i ŷ x_0^{-i} t^{-1} x_0^i ŷ^{-1} x_0^{-i}` has length `4i + 2|ŷ| + 2`
   and represents `[t, g_i]`. So `w_i = 1` in `Γ_S` iff `i ∈ S`. The map `i ↦ w_i` is
   computable. If `Γ_S` had solvable word problem, `S` would be recursive.
4. **Conclusion.** Choose a non-recursive `S ⊆ N`, for example the halting set. Then
   `Γ_S` is a finitely generated subgroup of `T(G_*)`, and it has unsolvable word problem.
   A coCF group has solvable word problem, since context-free languages are decidable.
   So `Γ_S` is not coCF. `T(G_*)` itself is finitely generated (claim, item 1) and
   contains `Γ_S`, so its word problem is unsolvable too, and `T(G_*)` is not coCF.
   This establishes `some-finite-cloning-system-group-is-not-locally-cocf`.

## Remarks (not needed for the route)

- **Uncountably many examples.** `S ↦ Γ_S` is injective on marked groups: `S` is read
  off from the relations `w_i = 1`. There are uncountably many marked groups `Γ_S`, but a
  single isomorphism type carries only countably many markings on three generators. So
  uncountably many isomorphism types arise. `V` has only countably many finitely
  generated subgroups, and there are only countably many coCF groups.
- **Computable data do not help.** Let `S` be a recursive set of naturals that is not
  decidable in time polynomial in `i` (such sets exist by the time hierarchy theorem).
  - Membership in `H_S` is then decidable from a tree pair: `f ∈ H_S` iff `f` is supported
    in `∪ int J_i` and each restriction `f|J_i` is a power `g_i^{n}`, with `n = 0` for
    `i ∉ S`. The exponent `n` can be read off from the slope at the left end of the
    support, if `y` is chosen with slope `2` there.
  - So the cloning system has computable `D_n`, `s_k` and `G_n`.
  - A coCF group has a word problem decidable in time cubic in the word length, by CYK
    on the co-word grammar. Since `|w_i| = O(i)`, this would decide `S` in time `O(i^3)`.
    So even computable coset-tree cloning systems give groups that are not coCF.
- **Calibration.**
  - `H = F` gives `D_∞ = {pt} ⊔ F/P` and `T(G_*) ⊇ A × F`.
  - `H = 1` gives `⟨x_0, x_1, t⟩ = A ≀ F`. Whether `A ≀ F` is coCF (or embeds in `V`) is
    open. The HRRT conjecture would settle it negatively: "`G ≀ H` coCF implies `H` virtually
    free" (Holt–Rees–Röver–Thomas 2005). The route above does not depend on it.
