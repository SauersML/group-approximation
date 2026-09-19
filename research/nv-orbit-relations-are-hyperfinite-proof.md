---
rg: 2
id: nv-orbit-relations-are-hyperfinite-proof
kind: route
title: Brick maps preserve coordinatewise tail classes, binary expansion turns the tail relation into the dyadic affine relation of an amenable group, and Zimmer's theorem forbids amenable free probability-preserving relations of non-amenable groups
target: nv-orbit-relations-are-hyperfinite
requires:
  - thompson-f-interval-orbit-relation-is-hyperfinite
---

Notation: `E_t` is tail equivalence on `C`, where `x E_t y` iff `σ^a x = σ^b y` for some
`a, b ≥ 0`. `Q ⊂ C` is the countable set of eventually constant sequences, and `C_0 = C \ Q`.

**Step 1. `R_{nV} ⊆ E_t^{×n}`.** An element `g ∈ nV` is a finite brick map. On a brick
`[u_1] × ... × [u_n]` it sends `(u_1 x_1', ..., u_n x_n')` to `(v_1 x_1', ..., v_n x_n')`.
So each coordinate of `g(x)` is tail equivalent to the same coordinate of `x`. For `G ≤ nV`,
`R_G ⊆ E_t^{×n}`. In particular, for each `S ⊆ {1..n}` the Borel set
`D_S = {x : x_i ∈ Q exactly for i ∈ S}` is `G`-invariant, and `C^n` is the disjoint union of
the `D_S`. It suffices to prove hyperfiniteness of `(R_G, μ)` on each `D_S` with `μ(D_S) > 0`.

**Step 2. The tail relation is an amenable orbit relation.**
- Let `π : C → [0,1]` be binary expansion. It is a Borel bijection from `C_0` onto
  `I_0 = (0,1) \ Z[1/2]`.
- Take `x, y ∈ C_0`. Then `σ^a x = σ^b y` iff `2^a π(x) - 2^b π(y) ∈ Z`, because expansions of
  non-dyadic points are unique. That holds iff `π(y) = 2^k π(x) + d` with `k ∈ Z` and
  `d ∈ Z[1/2]`. For the converse, clear the denominator of `d`.
- So `π` carries `E_t|C_0` onto `R_Aff ∩ I_0^2`, where `Aff` is the countable solvable group
  of maps `t ↦ 2^k t + d` of `R`. This is step 1 of
  `thompson-f-interval-orbit-relation-is-hyperfinite`.
- Coordinatewise, `π^{S^c}` carries `E_t^{×S^c}` on `C_0^{S^c}` into the orbit relation of
  the amenable group `Aff^{S^c}` on `R^{S^c}`.

**Step 3. Hyperfiniteness on `D_S`.**
- Identify `D_S = Q^S × C_0^{S^c}`. Then `R_G|D_S ⊆ (Q^S × Q^S) × E_t^{×S^c}`.
- Let `H` be the countable amenable group `Sym_fin(Q^S) × Aff^{S^c}` acting on
  `Q^S × R^{S^c}`. Via `id × π^{S^c}`, its orbit relation contains the image of `R_G|D_S`.
- Push `μ|D_S` forward to `ν`, and set `ν' = Σ_j 2^{-j} (h_j)_* ν` over an enumeration of `H`.
  Then `ν'` is `H`-quasi-invariant and `ν ≪ ν'`.
- By Zimmer 1977 and Connes–Feldman–Weiss 1981, `(R_H, ν')` is hyperfinite. So off an
  `H`-invariant `ν'`-null set `N`, `R_H` is an increasing union of finite Borel subrelations
  `R_k`. The set `N` can be taken invariant by saturating, which keeps it null by
  quasi-invariance.
- `N` is `ν`-null, and it is `G`-invariant because `R_G ⊆ R_H`. Off `N`, `R_G` is the
  increasing union of the finite Borel subrelations `R_G ∩ R_k`.
- So `(R_G, μ)` is hyperfinite on each `D_S`, hence on `C^n`. This proves part 1.

**Step 4. Part 2.**
- Suppose `G ≤ nV` preserves a probability `μ` and acts essentially freely. By part 1, the
  relation `(R_G, μ)` is amenable.
- Zimmer 1984, Prop. 4.3.3: for an essentially free probability-preserving action, amenability
  of the orbit relation is equivalent to amenability of the group. So `G` is amenable.
- For the conjugation form: if `φ ∘ γ = ι(γ) ∘ φ` a.e., then `φ_* m` is an `ι(Γ)`-invariant
  probability and `ι(Γ)` acts essentially freely, so `Γ ≅ ι(Γ)` would be amenable.

**Step 5. Part 3: the affine models are free and probability-preserving.**
- Let `K` be a compact group: `Z_p^2`, an infinite profinite completion of `Z^2` stable under
  `Λ`, or `F_p[[t]]^2`. Let `A_0 = Z^2` or `F_p[t]^2`, dense in `K`.
- Continuous automorphisms and translations preserve Haar probability.
- The affine element `(A, b)` fixes `z` iff `(I - A) z = b`. For `A = I` and `b ≠ 0` there is
  no fixed point.
- For `A ≠ I`, the solution set is empty or a coset of the closed subgroup `ker(I - A)`. A
  closed subgroup has positive Haar measure only if it is open. If `ker(I - A)` were open, it
  would contain a finite-index subgroup of the dense lattice `A_0`: `N ∩ Z^2` in the first two
  cases, and `t^k F_p[t]^2` in the third. So `A` would fix a finite-index subgroup of `A_0` and
  be the identity, since `A_0` is torsion-free over `Z`, or a free module over the domain
  `F_p[t]`.
- The group is countable, so a.e. stabilizer is trivial.
- Both groups are non-amenable:
  - `Λ` is non-amenable by assumption;
  - `EL_2(F_p[t]) = SL_2(F_p[t]) = SL_2(F_p) *_{B(F_p)} B(F_p[t])` (Nagao) is an amalgam
    with indices `p + 1 ≥ 3` and `∞`, so it contains a non-abelian free group.
- Apply part 2.
