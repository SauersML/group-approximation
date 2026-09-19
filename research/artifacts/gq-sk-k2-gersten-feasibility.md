# Two-generator Gersten in Lean: what the sources allow (lane sk-k2-gersten, 2026-09-19)

Target: `LVPolyK2.skLoc_GerstenTwoStatement`, i.e. `LVFreeAlgK2.AugNilK2Trivial (freeAug (ZMod 2) (Fin 2))`.
On main it is reduced (by the scaling deformation, `LVFreeAlgGersten.skGer_augNil_freeAlgebra_of_polyNil`)
to `NK₂(𝔽₂⟨x₀,x₁⟩) = 0`, which is a priori stronger. It feeds the one open simple-Kazhdan row
(768ac9454e9b, tex l.733-735) through stable `K₂(L_{𝔽₂}(1,2)) = 0`.

## Findings

1. **Gersten's theorem is a Quillen K-theory result.** Gersten, *K-theory of free rings*, Comm. Algebra 1
   (1974) 39-64, proves `K_n(R⟨X⟩) = K_n(R)` for `R` regular right noetherian, for Quillen `K_n`. The
   abstract gives the equivalent form `H_n(GL(R)) = H_n(GL(R⟨X⟩))`. The later proofs also use higher
   K-theory:
   - coherent regularity of free algebras plus Quillen's fundamental theorem (Swan's notes on K-theory
     of coherent rings);
   - Waldhausen 1978, generalized free products.
   Mathlib has none of this: no exact categories and no Q- or plus-construction.
2. **No Steinberg-group-level proof was found.**
   - The weak algorithm (Cohn) gives the GE property, hence `K₁(𝔽₂⟨X⟩) = 𝔽₂^×`, but I know of no
     weak-algorithm proof of the `K₂` statement.
   - The one-generator Lean proof (`LVPolyK2/Basic`) uses the Euclidean/Nagao argument for `𝔽₂[x]`.
   - The naive two-generator attempt fails. It would write `E_n(k⟨x,y⟩)` as the amalgam
     `E_n(k[x]) *_{E_n(k)} E_n(k[y])` and apply Mayer-Vietoris. For `n ≥ 3` that decomposition is
     false: `[e₁₂(x), e₂₃(y)] = e₁₃(xy)` lies in neither factor.
3. **Khanh 2026 does not bypass Ara-Brustenga-Cortiñas (ABC).** Khanh, arXiv:2609.08428, is the paper
   the Lean route already cites. It proves `St_r(L) ≅ GL_r(L)` for `r ≥ 3` (Thm 5.4) over
   `L = L_{𝔽₂}(1,2)`.
   - Its rank-3 step needs `H₂(GL₃(L); ℤ) = 0`, which comes from Thm 4.4 (integral acyclicity).
   - Thm 4.4 rests on Prop 3.2, where ABC Thm 7.6 gives `K_i(L) = 0` because the map `1 - 2 = -1` is
     invertible.
   - Khanh's other inputs (GE property, Voronetsky centrality, Brown's presentation theorem,
     simple connectivity of `|X₄(L)|`) are elementary, and the last is proved by coning.
   So the only non-elementary input of the whole route is still `K₂(L) = 0`, stably. Equivalently,
   `H₂(GL₃(L)) = 0` together with the rest of Khanh's Thm 4.4.

## Consequence

Proving row 768ac9454e9b unconditionally in Lean needs one of two things:
- (a) Quillen-level algebraic K-theory in Lean, enough for Gersten plus Neeman-Ranicki localization,
  or for ABC. That is a large library effort.
- (b) A new elementary proof of stable `K₂(L_{𝔽₂}(1,2)) = 0`, or of `H₂(GL₃(L); ℤ) = 0`. That is a
  research problem; none is known to this lane.
The tex sentence itself cites Caprace-Rémy for the fact. Whether the row should be graded as
attribution is a decision for the census owner and the user; this lane does not make it.

Sources: [Gersten 1974](https://www.tandfonline.com/doi/abs/10.1080/00927877408548608),
[Swan, K-theory of coherent rings](http://math.uchicago.edu/~swan/coherent.pdf),
[Khanh 2026](https://arxiv.org/abs/2609.08428).
