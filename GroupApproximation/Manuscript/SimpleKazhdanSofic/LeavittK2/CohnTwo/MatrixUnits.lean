import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.RelativeKOne
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# The ideal `(p)` of `C_2` is `M_∞(k)` with basis `α p β*`

Lane `sk-leavitt-18`, seventh module.

* `matrixUnit_mul`: `u(α, β) u(γ, δ) = δ_{βγ} u(α, δ)` for `u(α, β) = α p β*`, from lane
  `sk-leavitt-19`'s `unit_mul_unit`. So the `u(α, β)` multiply like the matrix units of
  `M_∞(k)`, indexed by finite binary words.
* `linearCombination_matrixUnit_injective`: the `u(α, β)` are linearly independent. On the
  Fock space, `u(α, β)` sends the point mass at `β` to the point mass at `α` (`fock_unit`).
  Reading that coefficient (`coeffMap`) recovers every finitely supported combination.
* **Endpoint** `span_p_equiv_matrixUnits`: the `k`-span of the matrix units is linearly
  isomorphic to `⊕_{(α, β)} k`, the underlying space of `M_∞(k)`, with basis `α p β*`.
* `matrixUnitSpan_le_pIdeal`: the span lies in `(p)`. Over `𝔽₂` it is all of `(p)`
  (`mem_pIdeal_iff_mem_matrixUnitSpan`), by lane 19's `mem_unitSpan_of_mem_span_p` and
  `mem_monomialSpan`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

namespace CohnTwo

section Field

variable (k : Type*) [Field k]

/-- The matrix unit `u(α, β) = α p β*`. -/
def matrixUnit (ab : List (Fin 2) × List (Fin 2)) : CohnTwo k :=
  (data k).unit ab.1 ab.2

theorem matrixUnit_mul (ab cd : List (Fin 2) × List (Fin 2)) :
    matrixUnit k ab * matrixUnit k cd =
      if ab.2 = cd.1 then matrixUnit k (ab.1, cd.2) else 0 :=
  (data k).unit_mul_unit ab.1 ab.2 cd.1 cd.2

/-- The `k`-span of the matrix units. -/
def matrixUnitSpan : Submodule k (CohnTwo k) :=
  Submodule.span k (Set.range (matrixUnit k))

/-- The coefficient of `x` at `(α, β)`: the value at `α` of `x` applied to the point mass at
`β`. -/
def coeffMap : CohnTwo k →ₗ[k] (List (Fin 2) × List (Fin 2) → k) where
  toFun x ab := fock k x (pt k ab.2 1) ab.1
  map_add' x y := by
    funext ab
    show fock k (x + y) (pt k ab.2 1) ab.1 =
      fock k x (pt k ab.2 1) ab.1 + fock k y (pt k ab.2 1) ab.1
    rw [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c x := by
    funext ab
    show fock k (c • x) (pt k ab.2 1) ab.1 = c * fock k x (pt k ab.2 1) ab.1
    rw [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]

theorem coeffMap_apply (x : CohnTwo k) (ab : List (Fin 2) × List (Fin 2)) :
    coeffMap k x ab = fock k x (pt k ab.2 1) ab.1 := rfl

theorem coeffMap_matrixUnit (ab' ab : List (Fin 2) × List (Fin 2)) :
    coeffMap k (matrixUnit k ab') ab = if ab' = ab then 1 else 0 := by
  rcases ab' with ⟨α, β⟩
  rcases ab with ⟨a, b⟩
  show coeffMap k ((data k).unit α β) (a, b) = _
  rw [coeffMap_apply, fock_unit]
  show (if a = α then (if β = b then (1 : k) else 0) else 0) =
    if ((α, β) : List (Fin 2) × List (Fin 2)) = (a, b) then 1 else 0
  by_cases h : ((α, β) : List (Fin 2) × List (Fin 2)) = (a, b)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [if_pos h, if_pos h1.symm, if_pos h2]
  · rw [if_neg h]
    by_cases h1 : a = α
    · rw [if_pos h1, if_neg (fun h2 => h (by rw [h1, h2]))]
    · rw [if_neg h1]

theorem coeffMap_linearCombination (l : List (Fin 2) × List (Fin 2) →₀ k) :
    coeffMap k (Finsupp.linearCombination k (matrixUnit k) l) = ⇑l := by
  induction l using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.coe_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, Finsupp.coe_add]
  | single a b =>
    rw [Finsupp.linearCombination_single, map_smul]
    funext ab
    rw [Pi.smul_apply, Finsupp.single_apply, coeffMap_matrixUnit, smul_eq_mul]
    by_cases h : a = ab
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]

/-- The matrix units are linearly independent. -/
theorem linearCombination_matrixUnit_injective :
    Function.Injective (Finsupp.linearCombination k (matrixUnit k)) := by
  intro l l' h
  have h1 := coeffMap_linearCombination k l
  rw [h, coeffMap_linearCombination] at h1
  exact DFunLike.coe_injective h1.symm

/-- The matrix units span a subspace of `(p)`. -/
theorem matrixUnitSpan_le_pIdeal {x : CohnTwo k} (hx : x ∈ matrixUnitSpan k) :
    x ∈ pIdeal k := by
  have hp : cohnP k ∈ pIdeal k := TwoSidedIdeal.subset_span (Set.mem_singleton _)
  rw [matrixUnitSpan] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    show (data k).word ab.1 * cohnP k * (data k).coword ab.2 ∈ pIdeal k
    exact (pIdeal k).mul_mem_right _ _ ((pIdeal k).mul_mem_left _ _ hp)
  | zero => exact _root_.zero_mem _
  | add x y _ _ hx hy => exact _root_.add_mem hx hy
  | smul c x _ hx =>
    rw [Algebra.smul_def]
    exact (pIdeal k).mul_mem_left _ _ hx

end Field

/-- Over `𝔽₂` the ideal `(p)` is exactly the span of the matrix units. -/
theorem mem_pIdeal_iff_mem_matrixUnitSpan (x : CohnTwo (ZMod 2)) :
    x ∈ pIdeal (ZMod 2) ↔ x ∈ matrixUnitSpan (ZMod 2) :=
  ⟨fun hx => (data (ZMod 2)).mem_unitSpan_of_mem_span_p mem_monomialSpan hx,
    fun hx => matrixUnitSpan_le_pIdeal (ZMod 2) hx⟩

end CohnTwo

/-- **Lane endpoint.** The span of the matrix units `α p β*` in `C_2(k)` is linearly isomorphic
to `⊕_{(α, β)} k`, the space of finitely supported infinite matrices indexed by finite binary
words. The basis vector at `(α, β)` goes to `α p β*`, and the units multiply as matrix units
(`CohnTwo.matrixUnit_mul`). Over `𝔽₂` this span is the whole ideal `(p)`
(`CohnTwo.mem_pIdeal_iff_mem_matrixUnitSpan`). -/
noncomputable def span_p_equiv_matrixUnits (k : Type*) [Field k] :
    (List (Fin 2) × List (Fin 2) →₀ k) ≃ₗ[k] CohnTwo.matrixUnitSpan k :=
  (LinearEquiv.ofInjective (Finsupp.linearCombination k (CohnTwo.matrixUnit k))
      (CohnTwo.linearCombination_matrixUnit_injective k)).trans
    (LinearEquiv.ofEq _ _ (Finsupp.range_linearCombination (R := k) (v := CohnTwo.matrixUnit k)))

theorem span_p_equiv_matrixUnits_single (k : Type*) [Field k]
    (ab : List (Fin 2) × List (Fin 2)) :
    (span_p_equiv_matrixUnits k (Finsupp.single ab 1) : CohnTwo k) = CohnTwo.matrixUnit k ab := by
  show Finsupp.linearCombination k (CohnTwo.matrixUnit k) (Finsupp.single ab 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.matrixUnit
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.matrixUnit_mul
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.matrixUnitSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.coeffMap
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.coeffMap_apply
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.coeffMap_matrixUnit
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.coeffMap_linearCombination
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.linearCombination_matrixUnit_injective
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.matrixUnitSpan_le_pIdeal
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.mem_pIdeal_iff_mem_matrixUnitSpan
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.span_p_equiv_matrixUnits
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.span_p_equiv_matrixUnits_single
