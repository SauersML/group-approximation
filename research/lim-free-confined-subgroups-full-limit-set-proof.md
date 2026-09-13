---
rg: 2
id: lim-free-confined-subgroups-full-limit-set-proof
kind: route
title: Push a conjugate onto a generic attracting point and apply a confining element
target: confined-subgroups-of-lim-free-actions-have-full-limit-set
requires: []
---

**Setting.** `G` acts by isometries on a `δ`-hyperbolic space `S`, the action is of
general type, and the induced action on `Λ := Λ_S(G)` is topologically free. Write
`Ŝ = S ∪ ∂S`, fix `o ∈ S`, and let `(·|·)_o` be the Gromov product. Let `H ≤ G` be
confined, and let `P ⊂ G \ {1}` be a finite confining subset: every conjugate
`gHg^{-1}` meets `P`.

## Standard facts used

Quoted in Rybak, arXiv:2605.14159v3 (TeX on MSI), from Gromov, Hamann and
Das--Simmons--Urbański. They were not re-read at the primary sources.

- **(F1)** Isometries of `S` act on `Ŝ` by homeomorphisms, with `(ga|gb)_{go} = (a|b)_o`
  (l.351). `Ŝ` is Hausdorff (standard).
- **(F2)** For `a ∈ ∂S` the sets `U_o(a,r) = {x ∈ Ŝ : (a|x)_o > r}`, `r ≥ 0`, form a
  neighbourhood base at `a` (l.353--356). So a boundary point in the closure of a set
  is a limit of a sequence from it.
- **(F3)** `(a|b)_o ≥ min{(a|c)_o, (c|b)_o} − δ` on `Ŝ` (l.345).
- **(F4)** A loxodromic `l` has fixed points `l^±` with `l^n x → l^+` for
  `x ∈ Ŝ \ {l^-}`, uniformly on sets whose closure does not contain `l^-`
  (l.364--369). A loxodromic element fixes exactly two points of `∂S` (l.360).
- **(F5)** For a general type action, the endpoint pairs `(g^+, g^-)` of loxodromic
  elements are dense in `Λ × Λ` (l.401--404).
- **(F6)** For a general type action, `Λ` is the smallest nonempty closed invariant
  subset of `∂S`, so the action on `Λ` is minimal (l.395--398).
- **(F7)** Classification (l.371--392). `Λ_S(K) = ∅` iff `K` has bounded orbits. If
  `Λ_S(K)` is infinite, `K` contains loxodromic elements and either fixes a unique
  point of `∂S` (quasi-parabolic) or fixes none (general type).

Two trivial facts: `K` preserves `Λ_S(K)`, and `Λ_S(gKg^{-1}) = gΛ_S(K)`, computing the
second with base point `gs`.

## Step 0

Each `Fix_Λ(p)` is closed, by (F1), and has empty interior, by topological freeness.
So `V := Λ \ ⋃_{p∈P} Fix_Λ(p)` is open and dense in `Λ`, hence nonempty.

**Pigeonhole.** For every sequence `(g_n)` in `G` there are `p ∈ P` and an infinite
`N ⊆ ℕ` with `p ∈ g_n H g_n^{-1}` for all `n ∈ N`.

## Step 1: `H` has no bounded orbit

Suppose `diam(Hs) ≤ D` for some `s ∈ S`. By (F5) pick a loxodromic `l ∈ G` with
`l^+ ∈ V`, and apply Step 0 to `g_n = l^n`, getting `p ∈ P` and `N`.
- For `n ∈ N`, `p = l^n h l^{-n}` with `h ∈ H`, so
  `d(p l^n s, l^n s) = d(hs, s) ≤ D`.
- By (F4), `l^n s → l^+`, so `d(o, l^n s) → ∞`. Then
  `(p l^n s | l^n s)_o ≥ d(o, l^n s) − D → ∞`.
- By (F3), `(p l^n s | l^+)_o ≥ min{(p l^n s | l^n s)_o, (l^n s | l^+)_o} − δ → ∞`.
  So by (F2), `p l^n s → l^+` along `N`.
- By (F1), `p l^n s → p l^+`. Since `Ŝ` is Hausdorff, `p l^+ = l^+`, contradicting
  `l^+ ∈ V`.

So `Λ_S(H) ≠ ∅`.

## Step 2: `Λ_S(H) = Λ`

`Λ_S(H) = \overline{Hs} ∩ ∂S ⊆ Λ` is closed in `∂S`. Suppose `U := Λ \ Λ_S(H)` is
nonempty; it is open in `Λ`.
- By (F5) pick a loxodromic `l ∈ G` with `l^- ∈ U` and `l^+ ∈ V`.
- The closure of `Λ_S(H)` in `Ŝ` meets `∂S` inside `\overline{Hs} ∩ ∂S = Λ_S(H)`,
  so it does not contain `l^-`.
- By (F4), `l^n Λ_S(H) → l^+` uniformly: for every `r` there is `n_0` with
  `l^n Λ_S(H) ⊆ U_o(l^+, r)` for `n ≥ n_0`.

Apply Step 0 to `g_n = l^n`, getting `p ∈ P` and `N`.
- For `n ∈ N`, `p ∈ l^n H l^{-n}` preserves `Λ_S(l^n H l^{-n}) = l^n Λ_S(H)`, which
  is nonempty by Step 1.
- Pick `a_n ∈ l^n Λ_S(H)`. Then `a_n → l^+`, and also `p a_n → l^+`, because
  `p a_n ∈ l^n Λ_S(H)`.
- By (F1), `p a_n → p l^+`, so `p l^+ = l^+`, contradicting `l^+ ∈ V`.

## Step 3: `H` fixes no point of `∂S`

By Step 2 and (F7), `H` contains loxodromic elements. Suppose `H` fixes `ξ ∈ ∂S`.
- For a loxodromic `h ∈ H`, `h` fixes `ξ`, so `ξ ∈ {h^+, h^-} ⊆ Λ_S(H) = Λ` by (F4).
- By (F6) the orbit `Gξ` is dense in `Λ`. Pick `η ∈ V` and, by (F2), `g_n ∈ G` with
  `g_n ξ → η`.
- Apply Step 0 to `(g_n)`: `p ∈ g_n H g_n^{-1}` fixes `g_n ξ` for `n ∈ N`. By (F1),
  `p g_n ξ → p η`, while `p g_n ξ = g_n ξ → η`. So `p η = η`, contradicting `η ∈ V`.

So by (F7), `H` is of general type.

## Step 4: conclusion

`H` is of general type on `S` with `Λ_S(H) = Λ`. Its action on `Λ_S(H)` is the
restriction of `G`'s, hence topologically free, and it is minimal by (F6) applied
to `H`. So `H` is lim-free in Rybak's sense (l.183), through the same space `S`. ∎

**Remark.** Steps 1--3 show more. A subgroup `K ≤ G` is not confined if it has a
bounded orbit, if `Λ_S(K) ≠ Λ`, or if it fixes a point of `Λ`. Countability of `G`
is not used, and no Baire category argument is needed, because only the finitely
many elements of `P` must be avoided.
