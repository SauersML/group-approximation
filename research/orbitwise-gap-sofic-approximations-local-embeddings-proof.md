---
rg: 2
id: orbitwise-gap-sofic-approximations-local-embeddings-proof
kind: route
title: Restrict to the orbits where the finitely many defects vanish; bound orbits of semisimple elementary groups by transitivity on nonzero vectors; round almost invariant sets by the Kazhdan constant
target: orbitwise-gap-sofic-approximations-are-local-embeddings
requires:
  - gap-sofic-approximations-are-local-embeddings
  - elementary-groups-over-fg-rings-have-property-t
  - almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial
---

Notation: `d(a,b) = |{ω : aω ≠ bω}|/|Ω|` and `fpr(x) = 1 − d(x,1)`.

## Theorem O

**(gap ⇒ LEF).** Fix a finite `F ∋ e` and `P = {(g,h) ∈ F² : gh ∈ F}`.
1. For `(g,h) ∈ P` put `x = σ_N(gh)^(−1)σ_N(g)σ_N(h) ∈ H_N`. Then `η_N = max_P (1 − fpr(x)) → 0`.
2. Let `B` be the union of the orbits on which `x` acts nontrivially. On each such orbit `x` moves at least `δ|O|`
   points, so `|B| ≤ η_N|Ω_N|/δ`.
3. `Ω′_N = Ω_N ∖ ⋃_P B` is `H_N`-invariant, with `|Ω′_N| ≥ (1 − |P|η_N/δ)|Ω_N|`.
4. Let `res : H_N → Sym(Ω′_N)` be restriction, and `φ = res∘σ_N|_F`. Each `res(x)` is trivial, so
   `φ(gh) = φ(g)φ(h)` on `P`.
5. For `g ≠ h` in `F`, `d(σ_N(g),σ_N(h)) → 1` (step 3 of the gap route). So `σ_N(g)` and `σ_N(h)` differ at some
   point of `Ω′_N` for large `N`, and `φ` is injective into the finite group `res(H_N)`.

**(LEF ⇒ gap).** The regular actions of the finite groups of an LEF approximation have global, hence orbitwise, gap 1
(gap route). ∎

## Family (E)

- Wedderburn–Artin, with finite division rings being fields, gives `𝒜 = ∏_i M_(d_i)(F_i)`.
  - A unital module is `W = ⊕_i W_i` with `W_i ≅ (F_i^(d_i))^(k_i)`.
  - So `W_i^n ≅ M_(nd_i × k_i)(F_i)`, with `GL_n(M_(d_i)(F_i)) = GL_(nd_i)(F_i)` acting by left multiplication.
- **Elementary part.** For `n ≥ 2`, `EL_n(M_d(F)) = SL_(nd)(F)`.
  - Transvections between different blocks are `e_ij(E_pq)`.
  - Inside block `i`, `I + e_((i,p),(i,q))` with `p ≠ q` equals `[I + e_((i,p),(j,r)), I + e_((j,r),(i,q))]` for any
    `j ≠ i`.
  - `E_(nd)(F) = SL_(nd)(F)` over a field.
  - For `n = 1`, `EL_1` is trivial, and there is nothing to prove.
- **Product structure.** `EL_n(𝒜) = ∏_i EL_n(𝒜_i)` and `GL_n(𝒜) = ∏_i GL_n(𝒜_i)` act componentwise. So an orbit is
  `O = ∏_i O_i`, its uniform measure is the product, and `fpr_O(x) = ∏_i fpr_(O_i)(x_i)`.
- **One factor.** Let `X ∈ M_(nd×k)(F)` have rank `r`, and let `L = SL_(nd)(F)` or `GL_(nd)(F)`.
  - The orbit `LX` carries the push-forward of the uniform measure on `L`.
  - For `y ∈ L` with `P = ker(y − I) ≠ F^(nd)`, a point `gX` is fixed iff `im(gX) ⊆ P`.
  - If `r = 0`, the orbit is `{0}` and is fixed.
  - If `r ≥ 1`, pick `v ≠ 0` in `im X`. Then `gv` is uniform on `F^(nd) ∖ 0`, since `L` is transitive there (for
    `nd = 1` only `GL` occurs, and `P = 0`). So
    ```text
    fpr ≤ Pr(gv ∈ P) ≤ (|F|^(nd−1) − 1)/(|F|^(nd) − 1) < 1/2.
    ```
- **Conclusion.** If `x` acts nontrivially on `O`, some `x_i ≠ I` acts nontrivially on `O_i`, so `r_i ≥ 1` and
  `fpr_O(x) ≤ fpr_(O_i)(x_i) ≤ 1/2`. ∎

## Kazhdan cutting lemma

- On an orbit `O` put `S = Y ∩ O` and `f = 1_S − (|S|/|O|)1_O ⊥ 1_O`. The `H`-invariant vectors of `ℓ²(O)` are the
  constants.
- So `max_a ‖af − f‖² ≥ κ²‖f‖²`, where `‖af − f‖² = |aS Δ S|` and `‖f‖² = |S||O∖S|/|O| ≥ min(|S|,|O∖S|)/2`.
- Summing over orbits: `Σ_O min(|Y∩O|, |O∖Y|) ≤ (2/κ²) Σ_a |aY Δ Y| ≤ (2|A|/κ²)ε|Y|`.
- The union `Z` of the majority orbits has `|Y Δ Z| =` that sum. ∎

## Corollary C

1. **Paths.** Fix a word `w`. Each letter is injective and moves at most `ε_N|Y_N|` points of `Y_N` out of `Y_N`. So
   at most `|w|ε_N|Y_N|` points have a prefix path leaving `Y_N`. At the others, `σ_N(w)` is `ρ_N(w)`.
2. **Round.** The lemma gives an invariant `Z_N` with `|Y_N Δ Z_N| ≤ Cε_N|Y_N|`. Put `σ′_N(g) = ρ_N(ĝ)|_(Z_N)` for
   fixed lifts `ĝ`. The group `ρ_N(H)|_(Z_N)` has the same orbits as before, so it keeps the orbitwise gap.
3. **σ′ is a sofic approximation.**
   - `σ′(g)σ′(h)σ′(gh)^(−1) = ρ_N(k)|_Z` with `k = ĝĥ\widehat{gh}^(−1) ∈ K` fixed. By 1–2 it moves at most
     `o(|Y_N|) + O(ε_N|Y_N|)` points of `Z_N`.
   - For `g ≠ e`, `σ′(g)` agrees with `σ_N(ĝ)` off `O(ε_N|Y_N|)` points, so `fpr → 0`.
4. **Conclude.** Theorem O gives LEF.
5. **IRS-rigid simple `G`.**
   - `Fix_N = {y : σ_N(a)y = y for all a}` differs from `Y_N ∩ Fix(ρ_N(H))` only at points where some `σ_N(a) ≠ a`,
     at most `|A|ε_N|Y_N|` of them. So `Y_N ∖ Fix_N` is `O(ε_N)`-almost invariant.
   - By Consequence 1 of `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`, `σ_N` restricted there is a
     sofic approximation. Apply 1–4.

**For the hosts.**
- `EL_n(F_2⟨A⟩)` has (T) with `e_ij(1)` and the `e_ij(letters)` as a Kazhdan set
  (`elementary-groups-over-fg-rings-have-property-t`).
- A ring homomorphism `F_2⟨A⟩ → 𝒜_N` onto the image algebra gives `ρ_N(H) = EL_n(𝒜_N)`: the `e_ij(x)`, `x ∈ 𝒜_N`, are
  images of `e_ij` of polynomials, which lie in `H`.
- `G_Δ` LEF ⇔ `Δ` LEF is recorded in `research/artifacts/sk-sofic-host-hamming-2026-09-13-part1.md` §3.4(3). ∎
