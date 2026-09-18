import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.Algebra.Polynomial.Eval.Coeff
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJResMain
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Ultramatricial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgK2.ZModTwo
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.CohnLimK2DegZero
import GroupApproximation.Meta.AxiomGuard

/-!
# Untwisted polynomial `K₂` over `𝔽_p` and over ultramatricial `𝔽₂`-rings (lane ms-sk-uncond-a)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  The Boone–Higman
chain proves `K₂(N, 𝔽_p[X]) = ⊥` for every prime `p` and `N ≥ 5`
(`BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_K2_bot`, lane bh-met-94e: Euclid and Weyl
moves on orbit vectors, no literature input).  This file carries that theorem into the stable
`K₂` language of the simple Kazhdan chain (`LVH2GL3.StableK2Trivial`).  None of these results is
in the corpus in this form.

* `skPolyK2_stableK2Trivial_polynomial_zmod`: stable `K₂(𝔽_p[X]) = 0`.
* `skPolyK2_polyNilZModTwo`: `NK₂(𝔽₂) = 0`, i.e. the nil part of `t ↦ 0 : 𝔽₂[t] → 𝔽₂`.  This is
  the commutative scope witness that `LVFreeAlgGersten.skGer_polyNilZModTwo_of_polyNil` derives
  from the residual `skGer_PolyNilStatement`.  It now holds with no hypothesis.
* `skPolyK2_stableK2Trivial_polynomial_matrix_zmod`: stable `K₂(M_m(𝔽_p)[X]) = 0`, by
  `M_m(𝔽_p)[X] ≅ M_m(𝔽_p[X])` and Morita invariance.
* `skPolyK2_stableK2Trivial_polynomial_of_isUltramatricialF2`: for every ultramatricial
  `𝔽₂`-ring `S`, stable `K₂(S[X]) = 0`.  A finite set of polynomials has its coefficients in a
  subring `T ≅ ∏ M_{d_j}(𝔽₂)`, and `T[X] ≅ ∏ M_{d_j}(𝔽₂[X])`.
* `skPolyK2_augNil_polynomial_of_isUltramatricialF2`: untwisted `NK₂(S) = 0` for such `S`.  This
  is the case `φ = id` of the twisted nil-`K₂` input `LVSkewLaurentK2.NilK2Trivial` (lane 3b of
  WO-LVCohnK2-3).  The twisted case is NOT proved here.
* `skPolyK2_stableK2Trivial_polynomial_cohnDegreeZero`: stable `K₂(C₀[X]) = 0` for the
  degree-zero part `C₀` of the Cohn algebra `C_2(𝔽₂)`.
* `skPolyK2_freeAlgebraOneEquiv`, `skPolyK2_stableK2Trivial_freeAlgebra_one_zmod`,
  `skPolyK2_augNil_freeAlgebra_one_zmodTwo`: Gersten's theorem `K₂(𝔽⟨x⟩) = K₂(𝔽)` for ONE
  generator (`𝔽_p⟨x⟩ = 𝔽_p[x]`).  The case of two generators, `LVFreeAlgK2`'s target, stays
  open: it is the residual `LVFreeAlgGersten.skGer_PolyNilStatement` (via the deformation) or,
  directly, `LVFreeAlgK2.AugNilK2Trivial (LVFreeAlgK2.freeAug (ZMod 2) (Fin 2))`.
-/

namespace GroupApproximation.Full.LVPolyK2

open SteinbergGroup

/-- **Stable `K₂(𝔽_p[X]) = 0`** for every prime `p`: an element of `K₂(n, 𝔽_p[X])` dies in
`St_{n+5}(𝔽_p[X])`, where `K₂(n + 5, 𝔽_p[X]) = ⊥` (lane bh-met-94e).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_stableK2Trivial_polynomial_zmod {p : ℕ} (hp : p.Prime) :
    LVH2GL3.StableK2Trivial (Polynomial (ZMod p)) := by
  intro n k hk
  refine ⟨n + 5, Nat.le_add_right n 5, ?_⟩
  have hmem : indexMap (Fin.castLEEmb (Nat.le_add_right n 5)) k ∈
      BooneHigman.SteinbergBasic.K2n (n + 5) (Polynomial (ZMod p)) :=
    (BooneHigman.SteinbergBasic.mem_K2_iff _).mpr (LVH2GL3.projection_indexMap_eq_one _ hk)
  rw [BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_K2_bot hp (Nat.le_add_left 5 n)] at hmem
  exact Subgroup.mem_bot.mp hmem

#audit_axioms GroupApproximation.Full.LVPolyK2.skPolyK2_stableK2Trivial_polynomial_zmod

/-- **`NK₂(𝔽₂) = 0`**: the nil part of stable `K₂` for `t ↦ 0 : 𝔽₂[t] → 𝔽₂` vanishes.  This is
the conclusion of `LVFreeAlgGersten.skGer_polyNilZModTwo_of_polyNil`, now unconditional.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_polyNilZModTwo :
    LVFreeAlgK2.AugNilK2Trivial (Polynomial.constantCoeff (R := ZMod 2)) :=
  LVFreeAlgK2.augNilK2Trivial_of_stableK2Trivial _
    (skPolyK2_stableK2Trivial_polynomial_zmod Nat.prime_two)

#audit_axioms GroupApproximation.Full.LVPolyK2.skPolyK2_polyNilZModTwo

/-- Stable `K₂(M_m(𝔽_p[X])) = 0` (Morita invariance).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_stableK2Trivial_matrix_polynomial_zmod {p : ℕ} (hp : p.Prime) (m : ℕ) :
    LVH2GL3.StableK2Trivial (Matrix (Fin m) (Fin m) (Polynomial (ZMod p))) :=
  LVCohnK2.stableK2Trivial_matrix m (skPolyK2_stableK2Trivial_polynomial_zmod hp)

#audit_axioms GroupApproximation.Full.LVPolyK2.skPolyK2_stableK2Trivial_matrix_polynomial_zmod

/-- Stable `K₂(M_m(𝔽_p)[X]) = 0`, through `M_m(𝔽_p[X]) ≅ M_m(𝔽_p)[X]` (`matPolyEquiv`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_stableK2Trivial_polynomial_matrix_zmod {p : ℕ} (hp : p.Prime) (m : ℕ) :
    LVH2GL3.StableK2Trivial (Polynomial (Matrix (Fin m) (Fin m) (ZMod p))) :=
  LVCohnK2.stableK2Trivial_of_ringEquiv (matPolyEquiv (R := ZMod p) (n := Fin m)).toRingEquiv
    (skPolyK2_stableK2Trivial_matrix_polynomial_zmod hp m)

#audit_axioms GroupApproximation.Full.LVPolyK2.skPolyK2_stableK2Trivial_polynomial_matrix_zmod

/-- Stable `K₂((∏_j M_{d_j}(𝔽₂))[X]) = 0`, through `(∏_j A_j)[X] ≅ ∏_j A_j[X]`
(`Polynomial.piEquiv`) and finite products.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_stableK2Trivial_polynomial_matrixPi_zmodTwo (k : ℕ) (d : Fin (k + 1) → ℕ) :
    LVH2GL3.StableK2Trivial
      (Polynomial ((j : Fin (k + 1)) → Matrix (Fin (d j)) (Fin (d j)) (ZMod 2))) :=
  LVCohnK2.stableK2Trivial_of_ringEquiv
    (Polynomial.piEquiv (fun j : Fin (k + 1) => Matrix (Fin (d j)) (Fin (d j)) (ZMod 2))).symm
    (LVCohnK2.stableK2Trivial_pi (k + 1)
      (fun j => Polynomial (Matrix (Fin (d j)) (Fin (d j)) (ZMod 2)))
      (fun j => skPolyK2_stableK2Trivial_polynomial_matrix_zmod Nat.prime_two (d j)))

#audit_axioms GroupApproximation.Full.LVPolyK2.skPolyK2_stableK2Trivial_polynomial_matrixPi_zmodTwo

/-- **Stable `K₂(S[X]) = 0` for every ultramatricial `𝔽₂`-ring `S`.**  The coefficients of a
finite set of polynomials lie in a subring `T ≅ ∏_j M_{d_j}(𝔽₂)`; the polynomials lie in the
image of `T[X] → S[X]`, which is isomorphic to `T[X]`; conclude by directed unions.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_stableK2Trivial_polynomial_of_isUltramatricialF2 {S : Type*} [Ring S]
    (hS : LVSkewLaurentK2.IsUltramatricialF2 S) :
    LVH2GL3.StableK2Trivial (Polynomial S) := by
  classical
  refine LVCohnK2.stableK2Trivial_of_subrings ?_
  intro s
  obtain ⟨k, d, T, hcT, ⟨e⟩⟩ := hS (s.biUnion Polynomial.coeffs)
  refine ⟨(Polynomial.mapRingHom T.subtype).range, ?_, ?_⟩
  · intro q hq
    have hq' : (↑q.coeffs : Set S) ⊆ T := fun c hc =>
      hcT (Finset.mem_coe.mpr
        (Finset.mem_biUnion.mpr ⟨q, Finset.mem_coe.mp hq, Finset.mem_coe.mp hc⟩))
    exact RingHom.mem_range.mpr ⟨q.toSubring T hq', by simp [Polynomial.coe_mapRingHom]⟩
  · have hinj : Function.Injective (Polynomial.map T.subtype) :=
      Polynomial.map_injective (f := T.subtype) T.subtype_injective
    have hT : LVH2GL3.StableK2Trivial (Polynomial T) :=
      LVCohnK2.stableK2Trivial_of_ringEquiv (Polynomial.mapEquiv e).symm
        (skPolyK2_stableK2Trivial_polynomial_matrixPi_zmodTwo k d)
    refine LVCohnK2.stableK2Trivial_of_ringEquiv
      (RingEquiv.ofBijective (Polynomial.mapRingHom T.subtype).rangeRestrict ⟨?_, ?_⟩) hT
    · intro a b h
      apply hinj
      have h' := congrArg Subtype.val h
      simpa [Polynomial.coe_mapRingHom] using h'
    · exact (Polynomial.mapRingHom T.subtype).rangeRestrict_surjective

#audit_axioms
  GroupApproximation.Full.LVPolyK2.skPolyK2_stableK2Trivial_polynomial_of_isUltramatricialF2

/-- **Untwisted `NK₂(S) = 0`** for every ultramatricial `𝔽₂`-ring `S`: the nil part of
`t ↦ 0 : S[t] → S` vanishes.  This is the case `φ = id` of the twisted input
`LVSkewLaurentK2.NilK2Trivial`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_augNil_polynomial_of_isUltramatricialF2 {S : Type*} [Ring S]
    (hS : LVSkewLaurentK2.IsUltramatricialF2 S) :
    LVFreeAlgK2.AugNilK2Trivial (Polynomial.constantCoeff (R := S)) :=
  LVFreeAlgK2.augNilK2Trivial_of_stableK2Trivial _
    (skPolyK2_stableK2Trivial_polynomial_of_isUltramatricialF2 hS)

#audit_axioms GroupApproximation.Full.LVPolyK2.skPolyK2_augNil_polynomial_of_isUltramatricialF2

/-- Stable `K₂(C₀[X]) = 0` for the degree-zero part `C₀` of the Cohn algebra `C_2(𝔽₂)`
(`C₀` is ultramatricial, `LVCohnColimit.skCohnLimK2_isUltramatricialF2_degreeZero`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_stableK2Trivial_polynomial_cohnDegreeZero :
    LVH2GL3.StableK2Trivial (Polynomial LVCohnDegZero.cohnDegreeZero) :=
  skPolyK2_stableK2Trivial_polynomial_of_isUltramatricialF2
    LVCohnColimit.skCohnLimK2_isUltramatricialF2_degreeZero

#audit_axioms GroupApproximation.Full.LVPolyK2.skPolyK2_stableK2Trivial_polynomial_cohnDegreeZero

/-- The free algebra on one generator is the polynomial ring: `F⟨x⟩ ≃ₐ F[X]`, `x ↦ X`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
noncomputable def skPolyK2_freeAlgebraOneEquiv (F : Type*) [CommRing F] :
    FreeAlgebra F (Fin 1) ≃ₐ[F] Polynomial F :=
  AlgEquiv.ofAlgHom (FreeAlgebra.lift F (fun _ => Polynomial.X))
    (Polynomial.aeval (FreeAlgebra.ι F (0 : Fin 1)))
    (by
      apply Polynomial.algHom_ext
      simp)
    (by
      apply FreeAlgebra.hom_ext
      funext i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      simp)

/-- **Gersten for one generator**: stable `K₂(𝔽_p⟨x⟩) = 0` for every prime `p`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_stableK2Trivial_freeAlgebra_one_zmod {p : ℕ} (hp : p.Prime) :
    LVH2GL3.StableK2Trivial (FreeAlgebra (ZMod p) (Fin 1)) :=
  LVCohnK2.stableK2Trivial_of_ringEquiv (skPolyK2_freeAlgebraOneEquiv (ZMod p)).symm.toRingEquiv
    (skPolyK2_stableK2Trivial_polynomial_zmod hp)

#audit_axioms GroupApproximation.Full.LVPolyK2.skPolyK2_stableK2Trivial_freeAlgebra_one_zmod

/-- The Gersten nil part of `K₂(𝔽₂⟨x⟩)` vanishes (one generator; the two-generator case is the
open target of `LVFreeAlgK2`).  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skPolyK2_augNil_freeAlgebra_one_zmodTwo :
    LVFreeAlgK2.AugNilK2Trivial (LVFreeAlgK2.freeAug (ZMod 2) (Fin 1)) :=
  (LVFreeAlgK2.stableK2Trivial_freeAlgebra_zmodTwo_iff (Fin 1)).mp
    (skPolyK2_stableK2Trivial_freeAlgebra_one_zmod Nat.prime_two)

#audit_axioms GroupApproximation.Full.LVPolyK2.skPolyK2_augNil_freeAlgebra_one_zmodTwo

end GroupApproximation.Full.LVPolyK2
