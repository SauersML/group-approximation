import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateProj
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDilateStatement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev dilation: reduction to `K₂` elements in rank `≥ 5`

Lane `bh-met-90h`.  `k2CubeDilate_DilatesAt s` (Tulenbaev dilation, padded form) is reduced to
`k2Dilate_K2DilatesAt s`, the same statement only for `N ≥ 5` and `g ∈ K₂(N, A[X])`.

**The torsion step (proved, `k2Dilate_dilatesAt_of_K2`).**  Take `g ∈ St(N, A[X])` with
`g(0) = 1`, and suppose the image of `g` over `A_s[X]` dies after padding.  Let `P ∈ E(N, A[X])`
be the matrix of `g`.  Then `P(0) = 1`, and `P = 1` over `A_s[X]` because padding of matrices is
injective at `1`.  So every entry of `P - 1` has zero constant term and `s`-torsion
coefficients.  Hence `P(s^m X) = 1` for some `m` (`k2Dilate_scale_mapMatrix_eq_one`), which
means `g' = g(s^m X) ∈ K₂`.  Also `g'(0) = 1`, and `g'` still dies over `A_s[X]`.  The residual
at `g'` gives `r` with `g'(s^r X) = g(s^{m+r} X)` dying after padding.  **The padding step
(proved, `k2Dilate_K2DilatesAt_all`)** removes `N ≥ 5` by padding to rank `max N 5`.

## LOUD: status of the residual

* `k2Dilate_K2DilatesAt s` is **equivalent** to `k2CubeDilate_DilatesAt s` for each `A` and
  `s`, by the two proved directions.  It is **strictly smaller in proof content**: the
  non-`K₂` part of Tulenbaev's lemma (the torsion argument above) and the small-rank cases are
  proved here, and what is left is Tulenbaev's lemma on `NK₂`-type elements in rank `≥ 5`.
* `k2Dilate_PolyK2Statement`, the residual the endpoint uses, keeps only prime `p`.  It is
  implied by `k2CubeDilate_PolyDilationStatement` (`k2Dilate_polyK2_of_polyDilation`).  So it is
  **formally weaker** than D, but not provably strictly weaker, because both are true.
* **Truth**: it follows from Tulenbaev's lemma (every commutative ring, rank `≥ 5`).  For
  `A = F_p[s_1..s_k][t]` it also follows from Quillen's `NK₂(A) = 0` with `r = 0`, because
  `g ∈ K₂` with `g(0) = 1` then dies after padding.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section DilateK2

variable {A : Type*} [CommRing A]

/-- **Tulenbaev dilation on `K₂` in rank `≥ 5`.**  Take `g ∈ K₂(N, A[X])` with `N ≥ 5` and
`g(0) = 1`, and suppose the image of `g` over `A_s[X]` dies after padding.  Then some dilation
`g(s^r X)` dies after padding. -/
def k2Dilate_K2DilatesAt (s : A) : Prop :=
  ∀ N : ℕ, 5 ≤ N → ∀ g : SteinbergGroup (Fin N) (Polynomial A), g ∈ K2 (Fin N) (Polynomial A) →
    SteinbergGroup.ringMap (Polynomial.evalRingHom (0 : A)) g = 1 →
      cubeDiagDilate_StDies
          (SteinbergGroup.ringMap (Polynomial.mapRingHom (algebraMap A (Localization.Away s))) g) →
        ∃ r : ℕ, cubeDiagDilate_StDies (SteinbergGroup.ringMap (k2CubeDilate_scale A (s ^ r)) g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_K2DilatesAt

/-- **Padding step**: the `K₂` residual in rank `≥ 5` gives it in every rank. -/
theorem k2Dilate_K2DilatesAt_all {s : A} (h : k2Dilate_K2DilatesAt s) (N : ℕ)
    (g : SteinbergGroup (Fin N) (Polynomial A)) (hK : g ∈ K2 (Fin N) (Polynomial A))
    (hev : SteinbergGroup.ringMap (Polynomial.evalRingHom (0 : A)) g = 1)
    (hloc : cubeDiagDilate_StDies
      (SteinbergGroup.ringMap (Polynomial.mapRingHom (algebraMap A (Localization.Away s))) g)) :
    ∃ r : ℕ, cubeDiagDilate_StDies (SteinbergGroup.ringMap (k2CubeDilate_scale A (s ^ r)) g) := by
  have hN : N ≤ max N 5 := le_max_left N 5
  obtain ⟨r, hr⟩ := h (max N 5) (le_max_right N 5)
    (SteinbergGroup.indexMap (Fin.castLEEmb hN) g) (indexMap_mem_K2 _ hK)
    (by rw [← GroupApproximation.Full.LVStableK2.indexMap_ringMap, hev, map_one])
    (by
      rw [← GroupApproximation.Full.LVStableK2.indexMap_ringMap]
      exact cubeDiagDilate_stDies_indexMap hN hloc)
  refine ⟨r, cubeDiagDilate_stDies_of_indexMap hN ?_⟩
  rw [GroupApproximation.Full.LVStableK2.indexMap_ringMap]
  exact hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_K2DilatesAt_all

/-- **Torsion step**: Tulenbaev dilation at `s` follows from its `K₂` case. -/
theorem k2Dilate_dilatesAt_of_K2 {s : A} (h : k2Dilate_K2DilatesAt s) :
    k2CubeDilate_DilatesAt s := by
  intro N g hev hloc
  have h0 := k2Dilate_mapMatrix_eq_one_of_stDies (Polynomial.evalRingHom (0 : A)) g
    (by rw [hev]; exact cubeDiagDilate_stDies_one)
  have hs := k2Dilate_mapMatrix_eq_one_of_stDies _ g hloc
  obtain ⟨m, hm⟩ := k2Dilate_scale_mapMatrix_eq_one s _ h0 hs
  have hK := k2Dilate_mem_K2_of_mapMatrix _ g hm
  have hev' : SteinbergGroup.ringMap (Polynomial.evalRingHom (0 : A))
      (SteinbergGroup.ringMap (k2CubeDilate_scale A (s ^ m)) g) = 1 := by
    rw [SteinbergBasic.ringMap_ringMap, k2Dilate_evalZero_comp_scale]
    exact hev
  have hloc' : cubeDiagDilate_StDies (SteinbergGroup.ringMap
      (Polynomial.mapRingHom (algebraMap A (Localization.Away s)))
      (SteinbergGroup.ringMap (k2CubeDilate_scale A (s ^ m)) g)) := by
    rw [SteinbergBasic.ringMap_ringMap, k2Dilate_map_comp_scale,
      ← SteinbergBasic.ringMap_ringMap]
    exact cubeDiagDilate_stDies_ringMap _ hloc
  obtain ⟨r, hr⟩ := k2Dilate_K2DilatesAt_all h N _ hK hev' hloc'
  refine ⟨m + r, ?_⟩
  rw [SteinbergBasic.ringMap_ringMap, k2Dilate_scale_comp] at hr
  rw [pow_add]
  exact hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_dilatesAt_of_K2

/-- The converse: the `K₂` case is a special case. -/
theorem k2Dilate_K2DilatesAt_of_dilatesAt {s : A} (h : k2CubeDilate_DilatesAt s) :
    k2Dilate_K2DilatesAt s :=
  fun N _ g _ hev hloc ↦ h N g hev hloc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_K2DilatesAt_of_dilatesAt

end DilateK2

section DilateK2Statement

/-- The full Tulenbaev dilation lemma from its `K₂` case in rank `≥ 5`. -/
theorem k2Dilate_dilation_of_K2
    (h : ∀ (A : Type) [CommRing A] (s : A), k2Dilate_K2DilatesAt s) :
    k2CubeDilate_DilationStatement := by
  intro A _ s
  exact k2Dilate_dilatesAt_of_K2 (h A s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_dilation_of_K2

/-- The polynomial dilation residual D from its `K₂` case in rank `≥ 5`, for every `p`. -/
theorem k2Dilate_polyDilation_of_allK2
    (h : ∀ (p k : ℕ) (s₀ : MvPolynomial (Fin k) (ZMod p)),
      k2Dilate_K2DilatesAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))) :
    k2CubeDilate_PolyDilationStatement :=
  fun p k s₀ ↦ k2Dilate_dilatesAt_of_K2 (h p k s₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_polyDilation_of_allK2

/-- **The residual of lane `bh-met-90h`**: Tulenbaev dilation on `K₂` in rank `≥ 5`, only for
`A = F_p[s_1..s_k][t]` with `p` prime and constants `s = C s₀`. -/
def k2Dilate_PolyK2Statement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (k : ℕ) (s₀ : MvPolynomial (Fin k) (ZMod p)),
    k2Dilate_K2DilatesAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_PolyK2Statement

/-- The residual is implied by the dilation residual D. -/
theorem k2Dilate_polyK2_of_polyDilation (h : k2CubeDilate_PolyDilationStatement) :
    k2Dilate_PolyK2Statement :=
  fun p _ k s₀ ↦ k2Dilate_K2DilatesAt_of_dilatesAt (h p k s₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_polyK2_of_polyDilation

end DilateK2Statement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
