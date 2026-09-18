---
rg: 2
id: extractable-character-spectra-carry-no-almost-invariant-vectors
kind: claim
title: "Class-kill for C(C,Z) ⋊ V: if the C(C,Z)-spectrum of a vector lies in a V-invariant set of characters with a V-equivariant Borel extraction to Prob(C), then one of three fixed elements of V moves it by at least 1/10; so no witness of non-(T) or of central growth lives on finitely atomic, bounded-phase-variation or F-regular characters"
distinct_from:
  cantor-integer-maps-central-growth-criterion: that reduces central growth (and Problem B(Z)) to almost-invariant laws on characters with χ(1_C) ≠ 1; this kills every such law carried by characters from which a point measure on C can be read off equivariantly
  cantor-integer-maps-by-v-have-haagerup-property: that is Problem B(Z); this rules out the class of all spectral witnesses with equivariantly extractable locations, which includes the finitely supported and signed-measure constructions
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that bounds 1_C in every commensurating action; this bounds the 1_C-growth of the extractable spectral part of an arbitrary cnd function by 400 times its values on three elements of V
  cantor-integer-maps-by-v-are-not-a-t-menable: that is the full negative conjecture; this is only a kill of one class of positive constructions, and leaves scale-incoherent characters open
---

**Setting.** `C = {0,1}^ω`, `A = C(C,Z)`, `G = A ⋊ V`. The dual `Â` is compact. A character `χ`
is the same as a map from clopen sets to `T` that is multiplicative on disjoint unions, via
`χ([U]) = χ(1_U)`. `V` acts on `Â` by `(vχ)(f) = χ(v^{-1}·f)`. For a unitary representation
`π` of `G` and a vector `η`, `μ_η` is its `A`-spectral law on `Â`, with projection-valued
measure `E`. Fix the elements of `V`:
- `h_1`: `0w ↦ 00w`, `10w ↦ 01w`, `11w ↦ 1w`;
- `h_2`: `0w ↦ 01w`, `10w ↦ 00w`, `11w ↦ 1w`;
- `h_3`: `iw ↦ (1−i)w`.

An *extraction* is a `V`-invariant Borel set `𝔐 ⊆ Â` together with a Borel map
`p : 𝔐 → Prob(C)` satisfying `p(vχ) = v_* p(χ)`.

**Theorem K.** Let `(𝔐, p)` be an extraction. Every unit vector `η` with `μ_η(𝔐) = 1`
satisfies `max_i ‖π(h_i)η − η‖ ≥ 1/10`.

**Corollaries.**
1. **Witness laws avoid extractable characters.** For any unit vector `η`,
   `μ_η(𝔐) ≤ 100 · max_i ‖π(h_i)η − η‖²`. So any sequence of almost invariant vectors (for
   `¬RT(G,A)`, or for `¬RT(G,<1_C>)` via `cantor-integer-maps-central-growth-criterion`) has
   laws with `μ_k(𝔐) → 0`.
2. **Bounded central growth.** For any cnd `ψ = ‖b‖²`, the part `ψ_𝔐 = ‖E(𝔐)b‖²` satisfies
   `sup_M ψ_𝔐(M·1_C) ≤ 400 · max_i ψ(h_i)`.
3. **Unions.** A countable union of extractable sets is extractable (define `p` piecewise on
   the invariant differences). So the corollaries apply to the union of the classes below.

**Extractable classes.** Let `N_d(χ) = #{|u| = d : χ([u]) ≠ 1}`, and let `arg` take values in
`(−1/2, 1/2]`.
- **(i) finitely active characters.** `χ ≠ 1` and `sup_d N_d(χ) < ∞`. These are exactly the
  finitely atomic characters `f ↦ Π_i e(θ_i f(x_i))`; `p(χ)` is uniform on the atoms. This
  covers the characters of artifact §3(g) and the Brothier / CSV-type constructions built
  from finitely many points.
- **(ii) bounded phase variation.** `χ ≠ 1` and `sup_d Σ_{|u|=d} |arg χ([u])| < ∞`. This
  includes every `χ_λ(f) = e(∫ f dλ)` for a finite signed measure `λ`. Here `p(χ)` is the
  normalized limit measure `M(w) = lim_d Σ_{|u|=d, u⊒w} |arg χ([u])|`.
- **(iii) F-regular characters.** For a Borel `F : T → [0,∞)`, the limit
  `M_F(w) = lim_d Σ_{|u|=d, u⊒w} F(χ([u]))` exists and is finite for all words `w`, and is
  positive at `w = ∅`. Then `p(χ) = M_F / M_F(∅)`.

**Survivors.** Take the almost invariant unit vectors of the growth criterion, with laws `μ_k`,
and fix any countable family of Borel functions `F_n`. Every witness for Problem B(Z), and hence
for Haagerup of `nV`, has laws `μ_k` that
- give zero mass to `{χ(1_C) = 1}`, and
- give mass tending to `0` to the union of classes (i), (ii) and `(iii)_{F_n}`.

So its mass sits, asymptotically, on characters with infinite phase variation whose
`F_n`-variations fail to converge. Call these *scale-incoherent* characters.
