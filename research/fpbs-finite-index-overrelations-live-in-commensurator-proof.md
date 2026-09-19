---
rg: 2
id: fpbs-finite-index-overrelations-live-in-commensurator-proof
kind: route
title: The coset set of an E-class is a K-equivariant finite set, its law is a K-invariant probability on a countable set, so it has finite orbits and a finite-index subgroup of K fixes every coset
target: fpbs-finite-index-overrelations-live-in-commensurator
requires: []
---

Complete direct proof. The notation is that of the target. Nothing is imported
beyond the definitions and countable additivity.

**Step 1: the coset map.** For `x ∈ X` put

    Ψ(x) = { Kγ ∈ K\Γ : γx E x }.

This is well defined, because `E_{a|K} ⊆ E` gives `kγx E γx` for `k ∈ K`.
Since `a` is free, `γ ↦ γx` is injective on `Γ`. So the `E_{a|K}`-classes
inside `[x]_E` are exactly the sets `Kγx` with `Kγ ∈ Ψ(x)`, and distinct
cosets give distinct classes. Hence `[x]_E = ⋃_{Kγ ∈ Ψ(x)} Kγx`, and the
number of `E_{a|K}`-classes in `[x]_E` is `|Ψ(x)|`. So
`Z = {x : Ψ(x) finite}`.

**Step 2: measurability and invariance of `Z`.** For each `γ`, the set
`{x : γx E x}` is Borel, since `E` is Borel and `x ↦ (x, γx)` is Borel. So
`x ↦ Ψ(x)` is a Borel map into `2^{K\Γ}`, and `Z` is Borel. If `x E y`, then
`[x]_E = [y]_E` contains the same `E_{a|K}`-classes. So `Z` is `E`-invariant.

**Step 3: equivariance.** For `k ∈ K`, freeness and `kx E x` give

    Ψ(kx) = { Kγ : γkx E kx } = { Kγ : γk x E x }
          = { Kδk^{-1} : δx E x } = Ψ(x) k^{-1}.

Let `P` be the countable set of finite subsets of `K\Γ`. Then `K` acts on `P`
by `A · k = A k^{-1}` (right multiplication of each coset). By Step 3,
`Ψ(k x) = Ψ(x) · k` on `Z`, and `Z` is `K`-invariant.

**Step 4: finite orbits.** Let `ν = Ψ_*(μ|_Z)`, a finite measure on the
countable set `P`. For `A ∈ P` and `k ∈ K`, Step 3 gives
`Ψ^{-1}(A · k) ∩ Z = k (Ψ^{-1}(A) ∩ Z)`. Since `μ` is `a`-invariant,
`ν({A · k}) = ν({A})`. So if `ν({A}) > 0`, all points of the orbit `A · K` have
the same positive mass. Since `ν(P) ≤ 1`, the orbit is finite. The union `Z_0`
of the atoms `Ψ^{-1}(A) ∩ Z` with `ν({A}) > 0` is conull in `Z`, by countable
additivity.

**Step 5: a finite-index subgroup fixes every coset.** Fix `x ∈ Z_0` and
`A = Ψ(x)`. The stabilizer `S = {k ∈ K : A k^{-1} = A}` has index
`|A · K| < ∞` in `K`. The group `S` permutes the finite set `A`. The kernel
`K_0` of `S → Sym(A)` has finite index in `S`, hence in `K`. Let
`Kγ ∈ A`, that is `γx E x`. For `k ∈ K_0` we have `Kγk = Kγ` (using
`k^{-1} ∈ K_0`), so `γkγ^{-1} ∈ K`, that is `k ∈ γ^{-1}Kγ`. Hence
`K_0 ≤ K ∩ γ^{-1}Kγ`, so `[K : K ∩ γ^{-1}Kγ] ≤ [K : K_0] < ∞`, and
`γ ∈ C_K`. This proves item 1 of the target on the conull set `Z_0 ⊆ Z`.

**Step 6: the almost malnormal case.** Let `K` be infinite and almost
malnormal. If `g ∉ K`, then `K ∩ g^{-1}Kg` is finite, so it has infinite index
in the infinite group `K`, and `g ∉ C_K`. If `g ∈ K`, then
`K ∩ g^{-1}Kg = K`. So `C_K = K`. By Step 5, for a.e. `x ∈ Z` every `γ` with
`γx E x` lies in `K`. So `[x]_E = Kx`, which is item 2.

**Step 7: sandwich consequence.** Item 3 restates item 2 for `E` a sandwich
relation over `K = ⟨F⟩`. By item 2, `E|_Z = E_{a|K}|_Z`. By the definition of
`Z`, each `E`-class in `X \ Z` contains infinitely many `E_{a|K}`-classes.
Both pieces are `E`-invariant by Step 2. So there is no set of positive measure
on which `E` has finite index `n ≥ 2` over `E_{a|K}`. ∎

**Remark (sharpness of Step 4).** Step 4 is where finiteness is used. If
`Ψ(x)` is infinite, `ν` lives on infinite subsets of `K\Γ`, which form an
uncountable space, and invariant probabilities with no finite orbits exist.
Intermediate relations of infinite index, for example `E_{a|L}` for
`K < L` with `[L : K] = ∞`, show that nothing like item 2 holds on `X \ Z`.
