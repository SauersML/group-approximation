import GroupApproximation.CharClass.BundleCoordEmbed
import GroupApproximation.CharClass.BundleInvariance

/-!
# Complex vector bundles in the projection model, XVI: trivializing a line

A line bundle is trivial as soon as it has a nowhere-vanishing section, and on a
projection-valued map a section is free: the `i`-th **column** of `p x` lies in
the fibre, because `p` is idempotent, and it is nonzero exactly where the
diagonal entry `p x i i` is.  So over the standard chart `{x | p x i i ≠ 0}` a
rank-one bundle is trivial, with no choice and no local triviality argument.

That is `lineIso`.  Its consequence, which is what the Leray-Hirsch base case
needs, is that the projective bundle of `p ⊕ 1` over such a chart is a product:

    Proj (p ⊕ 1) ≃ₜ X × ℂP¹,   over `X`.

The chain is `lineIso`, then `isoPlusOne` to add the trivial line to both
sides, then `projHomeo` to move the projective bundle along the isomorphism,
then `projTrivHomeoCP`, which says the projective bundle of a trivial rank-`d+1`
bundle is `X × ℂP^d` because the absorption condition against `1` is vacuous.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

/-! ### A nonzero vector of a rank-one fibre spans it -/

section Fibre

variable {ι : Type} [Fintype ι]

theorem rankOneProj_mulVec (w v : ι → ℂ) :
    rankOneProj w *ᵥ v = (∑ k, star (w k) * v k) • w := by
  funext j
  rw [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rankOneProj_apply]
  ring

/-- **A nonzero vector of the fibre of a rank-one projection spans it.** -/
theorem lineOf_eq_of_mem_fibre {q : Matrix ι ι ℂ} (hq : IsStarProjection q)
    (htr : q.trace = 1) {v : ι → ℂ} (hv : v ≠ 0) (hfix : q *ᵥ v = v) : lineOf v = q := by
  obtain ⟨w, hw, rfl⟩ := eq_rankOneProj_of_trace_one hq htr
  have hfix' := hfix
  rw [rankOneProj_mulVec] at hfix'
  set lam := ∑ k, star (w k) * v k with hlam
  have hne : lam ≠ 0 := by
    intro h
    apply hv
    rw [← hfix', h, zero_smul]
  calc lineOf v = lineOf (lam • w) := by rw [hfix']
    _ = lineOf w := lineOf_smul hne w
    _ = rankOneProj w := lineOf_of_mem_unitVectors hw

end Fibre

/-! ### The column section -/

section Column

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- The `i`-th column of `p x`, a section of `p` over the whole base. -/
def colOf (p : Bundle X ι) (i : ι) (x : X) : ι → ℂ := fun j => p x j i

theorem colOf_mem_fibre (p : Bundle X ι) (i : ι) (x : X) :
    p x *ᵥ colOf p i x = colOf p i x := by
  funext j
  show (p x *ᵥ fun k => p x k i) j = p x j i
  rw [Matrix.mulVec_apply_eq_sum]
  have h : (∑ k, p x j k * p x k i) = (p x * p x) j i := (Matrix.mul_apply).symm
  rw [h, p.mul_self]

theorem colOf_ne_zero (p : Bundle X ι) {i : ι} {x : X} (hi : p x i i ≠ 0) :
    colOf p i x ≠ 0 := by
  intro h
  exact hi (congrFun h i)

theorem continuous_colOf (p : Bundle X ι) (i : ι) : Continuous (colOf p i) :=
  continuous_pi fun j => p.continuous.matrix_elem j i

end Column

/-! ### A rank-one bundle with a nonvanishing diagonal entry is trivial -/

section LineIso

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- The trivializing row: the normalized `i`-th column, conjugated. -/
noncomputable def lineHom (p : Bundle X ι) (i : ι) (x : X) : Matrix (Fin 1) ι ℂ :=
  Matrix.of fun _ j => star (normalizeVec (colOf p i x) j)

theorem lineHom_apply (p : Bundle X ι) (i : ι) (x : X) (k : Fin 1) (j : ι) :
    lineHom p i x k j = star (normalizeVec (colOf p i x) j) := rfl

theorem lineHom_conjTranspose_mul (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) {i : ι}
    (hi : ∀ x, p x i i ≠ 0) (x : X) : (lineHom p i x)ᴴ * lineHom p i x = p x := by
  have hne : colOf p i x ≠ 0 := colOf_ne_zero p (hi x)
  have hline : lineOf (colOf p i x) = p x :=
    lineOf_eq_of_mem_fibre (p.isStarProjection x) (hp x) hne (colOf_mem_fibre p i x)
  rw [← hline, lineOf_eq_rankOneProj_normalizeVec hne]
  ext j j'
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, lineHom_apply,
    lineHom_apply, star_star, rankOneProj_apply]

theorem lineHom_mul_conjTranspose (p : Bundle X ι) {i : ι} (hi : ∀ x, p x i i ≠ 0) (x : X) :
    lineHom p i x * (lineHom p i x)ᴴ = 1 := by
  have hu : normalizeVec (colOf p i x) ∈ unitVectors ι :=
    normalizeVec_mem_unitVectors (colOf_ne_zero p (hi x))
  ext k k'
  have hkk' : k = k' := Subsingleton.elim k k'
  subst hkk'
  rw [Matrix.mul_apply, Matrix.one_apply_eq]
  have hterm : ∀ j : ι, lineHom p i x k j * ((lineHom p i x)ᴴ) j k
      = star (normalizeVec (colOf p i x) j) * normalizeVec (colOf p i x) j := by
    intro j
    rw [Matrix.conjTranspose_apply, lineHom_apply, star_star]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  exact sum_star_mul_self hu

/-- **A rank-one bundle with a nowhere-vanishing diagonal entry is trivial.**
The trivializing section is the `i`-th column of `p`, normalized. -/
noncomputable def lineIso (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) (i : ι)
    (hi : ∀ x, p x i i ≠ 0) : BundleIso p (triv X (Fin 1)) where
  hom x := lineHom p i x
  continuous_hom := by
    refine continuous_matrix fun _ j => ?_
    exact ((continuous_apply j).comp
      (continuous_normalizeVec (continuous_colOf p i)
        fun x => colOf_ne_zero p (hi x))).star
  conjTranspose_mul x := lineHom_conjTranspose_mul p hp hi x
  mul_conjTranspose x := lineHom_mul_conjTranspose p hi x

end LineIso

/-! ### Adding a trivial line, and reindexing a trivial bundle -/

section Plus

variable {X : Type} [TopologicalSpace X] {ι κ : Type} [Fintype ι] [Fintype κ]

/-- An isomorphism survives adding a trivial line. -/
def isoPlusOne {p : Bundle X ι} {q : Bundle X κ} (e : BundleIso p q) :
    BundleIso p.plusOne q.plusOne where
  hom x := Matrix.fromBlocks (e.hom x) 0 0 1
  continuous_hom := by
    refine continuous_matrix fun s s' => ?_
    cases s with
    | inl k =>
        cases s' with
        | inl i => exact e.continuous_hom.matrix_elem k i
        | inr u => exact continuous_const
    | inr u =>
        cases s' with
        | inl i => exact continuous_const
        | inr u' => exact continuous_const
  conjTranspose_mul x := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [e.conjTranspose_mul x]
  mul_conjTranspose x := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp [e.mul_conjTranspose x]

theorem coordIncl_mul_conjTranspose_of_bijective {ρ : Type} [Fintype ρ] [DecidableEq ρ]
    {f : ι → ρ} (hf : Function.Bijective f) :
    coordIncl f * (coordIncl f)ᴴ = 1 := by
  have h1 : coordIncl f = (1 : Matrix ρ ρ ℂ).submatrix id f := rfl
  rw [h1, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
    ← Matrix.submatrix_mul (1 : Matrix ρ ρ ℂ) (1 : Matrix ρ ρ ℂ) id f id hf,
    Matrix.one_mul, Matrix.submatrix_id_id]

/-- **A trivial bundle plus a trivial line is trivial**, along any reindexing. -/
def plusOneTrivIso (X : Type) [TopologicalSpace X] [DecidableEq ι] [DecidableEq κ]
    (e : (ι ⊕ Unit) ≃ κ) : BundleIso ((triv X ι).plusOne) (triv X κ) where
  hom _ := coordIncl (e : (ι ⊕ Unit) → κ)
  continuous_hom := continuous_const
  conjTranspose_mul x := by
    rw [coordIncl_isometry e.injective, plusOne_apply, triv_apply, Matrix.fromBlocks_one]
  mul_conjTranspose x := coordIncl_mul_conjTranspose_of_bijective e.bijective

end Plus

/-! ### The projective bundle of a trivial bundle -/

section ProjTriv

variable {X : Type} [TopologicalSpace X] {d : ℕ}

theorem projSetCP_triv : projSetCP (triv X (Fin (d + 1))) = (Set.univ : Set (X × CP d)) := by
  ext z
  simp only [Set.mem_univ, iff_true]
  show (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (z.2 : Matrix _ _ ℂ) = (z.2 : Matrix _ _ ℂ)
  exact Matrix.one_mul _

/-- **The projective bundle of a trivial bundle is a product.** -/
noncomputable def projTrivHomeoCP : Proj (triv X (Fin (d + 1))) ≃ₜ X × CP d :=
  (projHomeoCP (triv X (Fin (d + 1)))).trans
    ((Homeomorph.setCongr projSetCP_triv).trans (Homeomorph.Set.univ (X × CP d)))

theorem projTrivHomeoCP_over_base (z : Proj (triv X (Fin (d + 1)))) :
    (projTrivHomeoCP z).1 = projPi (triv X (Fin (d + 1))) z := rfl

end ProjTriv

/-! ### The base case of Leray-Hirsch over a chart -/

section Chart

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `Fin 1 ⊕ Unit ≃ Fin 2`. -/
def sumUnitEquivTwo : (Fin 1 ⊕ Unit) ≃ Fin 2 where
  toFun s := Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)) s
  invFun k := if k = 0 then Sum.inl 0 else Sum.inr ()
  left_inv s := by
    cases s with
    | inl a =>
        have : a = 0 := Subsingleton.elim a 0
        subst this
        rfl
    | inr u =>
        cases u
        rfl
  right_inv k := by
    fin_cases k <;> rfl

/-- **The base case of Leray-Hirsch over a chart.**  If `p` is a rank-one bundle
whose `i`-th diagonal entry never vanishes -- which is exactly the defining
condition of the `i`-th standard chart of `ℂP^d` when `p` is the tautological
line -- then the projective bundle of `p ⊕ 1` is the product `X × ℂP¹`, over
`X`. -/
noncomputable def projPlusOneHomeoCPOne (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1)
    (i : ι) (hi : ∀ x, p x i i ≠ 0) : Proj p.plusOne ≃ₜ X × CP 1 :=
  (_root_.GroupApproximation.CharClass.Bundle.BundleIso.projHomeo
      (isoPlusOne (lineIso p hp i hi))).trans
    ((_root_.GroupApproximation.CharClass.Bundle.BundleIso.projHomeo
      (plusOneTrivIso X sumUnitEquivTwo)).trans projTrivHomeoCP)

omit [DecidableEq ι] in
theorem projPlusOneHomeoCPOne_over_base (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1)
    (i : ι) (hi : ∀ x, p x i i ≠ 0) (z : Proj p.plusOne) :
    (projPlusOneHomeoCPOne p hp i hi z).1 = projPi p.plusOne z := rfl

end Chart

end Bundle

end CharClass
end GroupApproximation
