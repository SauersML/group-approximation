import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDilateMaps
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilLocal
import GroupApproximation.Meta.AxiomGuard

/-!
# The Tulenbaev dilation step and the local step of the cube gap

Lane `bh-met-90c`.  This module splits the proof of `PolyK2CubeNilLocalStatement` into two parts.

**Dilation** (`k2CubeDilate_DilatesAt s`, Tulenbaev's lemma in padded form).  Let `A` be a
commutative ring, `s ∈ A` and `g ∈ St(N, A[X])` with `g(0) = 1`.  Suppose the image of `g` in
`St(N, A_s[X])` dies after padding.  Then some dilation `g(s^r X)` already dies after padding over
`A[X]`.  `k2CubeDilate_DilationStatement` asserts this for all `A` and `s`.
`k2CubeDilate_PolyDilationStatement` asserts it only for `A = B[t]`, `B = F_p[s_1..s_k]` and
`s = C s₀`; the endpoint needs only this case.

**Local step** (`k2CubeDilate_LocalStatement`).  The hypotheses are those of the gap.  The
conclusion is that `ψ u` dies after padding over `B[t]_{C s₀}` for some `s₀ ∉ m`.  Here
`B[t]_{C s₀} ≅ B_{s₀}[t]`.

Proved here, all by Steinberg-group functoriality:

* `k2CubeDilate_evalZero_stDiff`: `ev_{y=0}(v_a(w)) = 1`, because `ev_{y=0} ∘ σ_a = id` and
  `ev_{y=0} ∘ C = id`.
* `k2CubeDilate_stDies_loc_stDiff`: if `w` dies over `L = B[t]_{C s₀}`, then so does the image
  of `v_a(w)` in `St(N, L[y])`.  Both factors of `ι[y](v_a w)` factor through `ι`.
* `k2CubeDilate_ringMap_scale_stDiff`: dilating `y` by `(C s₀)^r` turns `v_a(w)` into
  `v_{s₀^r a}(w)`.
* Sanity checks of the dilation statement: it holds outright for `s` nilpotent
  (`k2CubeDilate_dilatesAt_of_isNilpotent`, since `g(0 · X) = C(g(0)) = 1`) and for `s` a unit
  (`k2CubeDilate_dilatesAt_of_isUnit`, since `A → A_s` has a left inverse).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section DilateSt

variable {B : Type*} [CommRing B] {N : ℕ}

/-- `ev_{y=0}(v_a(w)) = 1`: the Quillen difference is trivial at `y = 0`. -/
theorem k2CubeDilate_evalZero_stDiff (w : SteinbergGroup (Fin N) (Polynomial B)) (a : B) :
    SteinbergGroup.ringMap (Polynomial.evalRingHom (0 : Polynomial B))
      (cubeDiagDilate_stDiff w a) = 1 := by
  rw [cubeDiagDilate_stDiff, map_mul, map_inv, SteinbergBasic.ringMap_ringMap,
    SteinbergBasic.ringMap_ringMap, k2CubeDilate_evalZero_comp_shift,
    k2CubeDilate_evalZero_comp_C]
  exact mul_inv_cancel _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_evalZero_stDiff

/-- If `w` dies over `L = B[t]_{C s₀}`, then the image of `v_a(w)` in `St(N, L[y])` dies. -/
theorem k2CubeDilate_stDies_loc_stDiff (w : SteinbergGroup (Fin N) (Polynomial B)) (s₀ a : B)
    (hw : cubeDiagDilate_StDies (SteinbergGroup.ringMap
      (algebraMap (Polynomial B) (Localization.Away (Polynomial.C s₀ : Polynomial B))) w)) :
    cubeDiagDilate_StDies (SteinbergGroup.ringMap (Polynomial.mapRingHom
      (algebraMap (Polynomial B) (Localization.Away (Polynomial.C s₀ : Polynomial B))))
        (cubeDiagDilate_stDiff w a)) := by
  rw [cubeDiagDilate_stDiff, map_mul, map_inv, SteinbergBasic.ringMap_ringMap,
    SteinbergBasic.ringMap_ringMap, k2CubeDilate_loc_comp_shift, k2CubeDilate_loc_comp_C,
    ← SteinbergBasic.ringMap_ringMap, ← SteinbergBasic.ringMap_ringMap]
  exact cubeDiagDilate_stDies_mul (cubeDiagDilate_stDies_ringMap _ hw)
    (cubeDiagDilate_stDies_inv (cubeDiagDilate_stDies_ringMap _ hw))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_stDies_loc_stDiff

/-- Dilating `y` by `(C s₀)^r` turns `v_a(w)` into `v_{s₀^r a}(w)`. -/
theorem k2CubeDilate_ringMap_scale_stDiff (w : SteinbergGroup (Fin N) (Polynomial B))
    (s₀ a : B) (r : ℕ) :
    SteinbergGroup.ringMap (k2CubeDilate_scale (Polynomial B) ((Polynomial.C s₀) ^ r))
      (cubeDiagDilate_stDiff w a) = cubeDiagDilate_stDiff w (s₀ ^ r * a) := by
  rw [← map_pow (Polynomial.C : B →+* Polynomial B) s₀ r, k2CubeDilate_scale_polynomial,
    cubeDiagDilate_ringMap_quillenScale_stDiff]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_ringMap_scale_stDiff

end DilateSt

section DilateStatement

/-- **Tulenbaev dilation at `s`**, in padded form.  Take `g ∈ St(N, A[X])` with `g(0) = 1`, and
suppose the image of `g` in `St(N, A_s[X])` dies after padding.  Then `g(s^r X)` dies after
padding for some `r`. -/
def k2CubeDilate_DilatesAt {A : Type*} [CommRing A] (s : A) : Prop :=
  ∀ (N : ℕ) (g : SteinbergGroup (Fin N) (Polynomial A)),
    SteinbergGroup.ringMap (Polynomial.evalRingHom (0 : A)) g = 1 →
      cubeDiagDilate_StDies
          (SteinbergGroup.ringMap (Polynomial.mapRingHom (algebraMap A (Localization.Away s))) g) →
        ∃ r : ℕ, cubeDiagDilate_StDies (SteinbergGroup.ringMap (k2CubeDilate_scale A (s ^ r)) g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_DilatesAt

/-- **Tulenbaev's dilation lemma** (padded form), for every commutative ring and every element. -/
def k2CubeDilate_DilationStatement : Prop :=
  ∀ (A : Type) [CommRing A] (s : A), k2CubeDilate_DilatesAt s

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_DilationStatement

/-- **The dilation residual**: Tulenbaev's lemma only for `A = F_p[s_1..s_k][t]` and constants
`s = C s₀`.  This is all the endpoint needs. -/
def k2CubeDilate_PolyDilationStatement : Prop :=
  ∀ (p k : ℕ) (s₀ : MvPolynomial (Fin k) (ZMod p)),
    k2CubeDilate_DilatesAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_PolyDilationStatement

theorem k2CubeDilate_polyDilation_of_dilation (h : k2CubeDilate_DilationStatement) :
    k2CubeDilate_PolyDilationStatement :=
  fun p k s₀ ↦ h (Polynomial (MvPolynomial (Fin k) (ZMod p))) (Polynomial.C s₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_polyDilation_of_dilation

/-- **The local residual**.  The hypotheses are those of `PolyK2CubeNilLocalStatement`.  The
conclusion is that `ψ u` dies after padding over `B[t]_{C s₀} ≅ B_{s₀}[t]` for some `s₀ ∉ m`. -/
def k2CubeDilate_LocalStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, k + 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin (k + 1)) (ZMod p)),
      (∀ i : Fin (k + 1), K2Map (cubeKill (ZMod p) i) u = 1) →
        ∀ m : Ideal (MvPolynomial (Fin k) (ZMod p)), m.IsMaximal →
          ∃ s₀ : MvPolynomial (Fin k) (ZMod p), s₀ ∉ m ∧
            cubeDiagDilate_StDies
              (SteinbergGroup.ringMap
                (algebraMap (Polynomial (MvPolynomial (Fin k) (ZMod p)))
                  (Localization.Away
                    (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))))
                (SteinbergGroup.ringMap
                  (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom
                  (u : SteinbergGroup (Fin N) (MvPolynomial (Fin (k + 1)) (ZMod p)))))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_LocalStatement

end DilateStatement

section DilateSanity

variable {A : Type*} [CommRing A]

/-- Sanity check: dilation holds outright at a nilpotent `s`, with `s^r = 0`. -/
theorem k2CubeDilate_dilatesAt_of_isNilpotent {s : A} (hs : IsNilpotent s) :
    k2CubeDilate_DilatesAt s := by
  intro N g hg _
  obtain ⟨r, hr⟩ := hs
  refine ⟨r, ?_⟩
  rw [hr, k2CubeDilate_scale_zero, ← SteinbergBasic.ringMap_ringMap, hg, map_one]
  exact cubeDiagDilate_stDies_one

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_dilatesAt_of_isNilpotent

/-- Sanity check: dilation holds at a unit `s` with `r = 0`, since `A → A_s` has a left
inverse. -/
theorem k2CubeDilate_dilatesAt_of_isUnit {s : A} (hs : IsUnit s) : k2CubeDilate_DilatesAt s := by
  intro N g _ hloc
  refine ⟨0, ?_⟩
  have hs' : IsUnit ((RingHom.id A) s) := hs
  have e : (Polynomial.mapRingHom
      (IsLocalization.Away.lift (S := Localization.Away s) s hs')).comp
        (Polynomial.mapRingHom (algebraMap A (Localization.Away s))) =
      RingHom.id (Polynomial A) := by
    rw [Polynomial.mapRingHom_comp, IsLocalization.Away.lift_comp, Polynomial.mapRingHom_id]
  have h := cubeDiagDilate_stDies_ringMap
    (Polynomial.mapRingHom (IsLocalization.Away.lift (S := Localization.Away s) s hs')) hloc
  rw [SteinbergBasic.ringMap_ringMap, e, SteinbergBasic.ringMap_id, MonoidHom.id_apply] at h
  rw [pow_zero, k2CubeDilate_scale_one, SteinbergBasic.ringMap_id, MonoidHom.id_apply]
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_dilatesAt_of_isUnit

end DilateSanity

end GroupApproximation.BooneHigman.Metabelian.ElemFP
