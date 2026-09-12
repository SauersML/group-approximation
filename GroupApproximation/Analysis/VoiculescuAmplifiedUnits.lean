import GroupApproximation.Analysis.VoiculescuAmplifiedState

/-!
# (V3) The matrix units, and the obstruction subspace of the block space

Two pieces of bookkeeping stand between the amplified state of
`Analysis/VoiculescuAmplifiedState` and Glimm's lemma.

**The finite set.**  Glimm's lemma is run on a finite subset of `Mₙ(A)`, and the
elements Voiculescu's argument needs are the matrix units `ι_k a π_l`: pairing a
vector `η` of `Hⁿ` against `ι_k a π_l` reads off exactly `⟪η_k, a η_l⟫`, which is
the entry the frame is built from, and the state's value on it is
`n⁻¹⟪e_k, ρ(a) e_l⟫`.  So a single finite set of matrix units, taken over the
given finite subset of `A` together with `1`, controls every entry at once.

**The obstruction.**  Glimm's lemma returns a vector orthogonal to a prescribed
finite-dimensional subspace of the space it is run on, and what the frame needs
is that *each coordinate* of that vector avoids the prescribed subspace of `H`.
`blockObstruction V n` is the subspace of `Hⁿ` that arranges this: it is the
range of a linear map from `(Fin n → V)`, so its finite-dimensionality is the
finite-dimensionality of a range rather than a statement about suprema of
submodules, and a vector orthogonal to it has every coordinate orthogonal to `V`
because `⟪ι_i v, η⟫ = ⟪v, η_i⟫`.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {K₀ : Type} [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
  [CompleteSpace K₀]
  {n : ℕ} {A : StarSubalgebra ℂ (H →L[ℂ] H)}

/-! ## The matrix units -/

variable (n) in
/-- The matrix unit with `a` in position `(k,l)`. -/
def matrixUnitOp (a : H →L[ℂ] H) (k l : Fin n) :
    BlockSpace H n →L[ℂ] BlockSpace H n :=
  (hBlockIncl H n k) ∘L a ∘L (hBlockProj H n l)

theorem blockEntry_matrixUnitOp (a : H →L[ℂ] H) (k l i j : Fin n) :
    blockEntry (matrixUnitOp n a k l) i j
      = if i = k then (if l = j then a else 0) else 0 := by
  by_cases hik : i = k
  · subst hik
    by_cases hlj : l = j
    · subst hlj
      rw [if_pos rfl, if_pos rfl]
      ext x
      show hBlockIncl H n i (a (hBlockIncl H n l x l)) i = a x
      rw [hBlockIncl_coord_same, hBlockIncl_coord_same]
    · rw [if_pos rfl, if_neg hlj]
      ext x
      show hBlockIncl H n i (a (hBlockIncl H n j x l)) i = 0
      rw [hBlockIncl_coord_ne hlj x, map_zero, hBlockIncl_coord_same]
  · rw [if_neg hik]
    ext x
    show hBlockIncl H n k (a (hBlockIncl H n j x l)) i = 0
    exact hBlockIncl_coord_ne hik _

theorem matrixUnitOp_mem (a : ↥A) (k l : Fin n) :
    matrixUnitOp n (a : H →L[ℂ] H) k l ∈ ampSubalgebra A n := by
  intro i j
  rw [blockEntry_matrixUnitOp]
  split
  · split
    · exact a.2
    · exact zero_mem A
  · exact zero_mem A

variable (A) in
/-- The matrix unit, as an element of `Mₙ(A)`. -/
def matrixUnit (a : ↥A) (k l : Fin n) : ↥(ampSubalgebra A n) :=
  ⟨matrixUnitOp n (a : H →L[ℂ] H) k l, matrixUnitOp_mem a k l⟩

theorem blockEntryMem_matrixUnit (a : ↥A) (k l i j : Fin n) :
    blockEntryMem (matrixUnit A a k l) i j = if i = k then (if l = j then a else 0) else 0 := by
  apply Subtype.ext
  rw [coe_blockEntryMem]
  show blockEntry (matrixUnitOp n (a : H →L[ℂ] H) k l) i j
      = ((if i = k then (if l = j then a else (0 : ↥A)) else 0 : ↥A) : H →L[ℂ] H)
  rw [blockEntry_matrixUnitOp]
  by_cases hik : i = k
  · by_cases hlj : l = j <;> simp [hik, hlj]
  · simp [hik]

/-- Pairing a vector of `Hⁿ` against a matrix unit reads off one entry. -/
theorem inner_matrixUnitOp (a : H →L[ℂ] H) (k l : Fin n) (eta : BlockSpace H n) :
    ⟪eta, matrixUnitOp n a k l eta⟫_ℂ
      = ⟪hBlockProj H n k eta, a (hBlockProj H n l eta)⟫_ℂ :=
  inner_hBlockIncl_right k eta (a (hBlockProj H n l eta))

/-! ## The state on a matrix unit -/

/-- The coordinate of the diagonal vector, in the form the block form of the
inner product produces. -/
theorem diagVector_coord' (b : OrthonormalBasis (Fin n) ℂ K₀) (r : Fin n) :
    (diagVector K₀ b) r = (((Real.sqrt n)⁻¹ : ℝ) : ℂ) • b r :=
  diagVector_coord b r

theorem ampStateLin_matrixUnit (hn : n ≠ 0) (b : OrthonormalBasis (Fin n) ℂ K₀)
    (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) (a : ↥A) (k l : Fin n) :
    ampStateLin A n b rho (matrixUnit A a k l)
      = ((n : ℂ))⁻¹ * ⟪b k, rho a (b l)⟫_ℂ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsq : ((Real.sqrt n)⁻¹ : ℝ) * ((Real.sqrt n)⁻¹ : ℝ) = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hnpos.le]
  have hcast : (((n : ℝ)⁻¹ : ℝ) : ℂ) = ((n : ℂ))⁻¹ := by push_cast; ring
  have hmat : ∀ i j : Fin n,
      ampMatrix A rho (matrixUnit A a k l) i j
        = if i = k then (if l = j then rho a else 0) else 0 := by
    intro i j
    rw [ampMatrix_apply, blockEntryMem_matrixUnit]
    by_cases hik : i = k
    · by_cases hlj : l = j <;> simp [hik, hlj]
    · simp [hik]
  rw [ampStateLin_apply, ampRep_apply, inner_hBlockOp]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · rw [hmat k l, if_pos rfl, if_pos rfl,
        diagVector_coord' b k, diagVector_coord' b l,
        inner_smul_left, map_smul, inner_smul_right]
      simp only [Complex.conj_ofReal]
      rw [← mul_assoc, ← Complex.ofReal_mul, hsq, hcast]
    · intro j _ hj
      rw [hmat k j, if_pos rfl, if_neg (fun h : l = j ↦ hj h.symm)]
      simp
    · intro h
      exact absurd (Finset.mem_univ l) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [hmat i j, if_neg hi]
    simp
  · intro h
    exact absurd (Finset.mem_univ k) h

/-! ## The obstruction subspace of the block space -/

variable (n) in
/-- The map whose range is the obstruction subspace. -/
def blockObstructionMap (V : Submodule ℂ H) :
    (Fin n → ↥V) →ₗ[ℂ] BlockSpace H n :=
  ∑ i : Fin n, (hBlockIncl H n i).toLinearMap ∘ₗ V.subtype ∘ₗ LinearMap.proj i

theorem blockObstructionMap_apply (V : Submodule ℂ H) (f : Fin n → ↥V) :
    blockObstructionMap n V f = ∑ i : Fin n, hBlockIncl H n i (f i) := by
  rw [blockObstructionMap, LinearMap.sum_apply]
  rfl

variable (n) in
/-- **The obstruction subspace of `Hⁿ`**: the vectors whose coordinates all lie
in `V`. -/
def blockObstruction (V : Submodule ℂ H) : Submodule ℂ (BlockSpace H n) :=
  LinearMap.range (blockObstructionMap n V)

theorem finiteDimensional_blockObstruction (V : Submodule ℂ H)
    [FiniteDimensional ℂ ↥V] :
    FiniteDimensional ℂ ↥(blockObstruction n V) :=
  LinearMap.finiteDimensional_range _

theorem hBlockIncl_mem_blockObstruction (V : Submodule ℂ H) (i : Fin n) {v : H}
    (hv : v ∈ V) : hBlockIncl H n i v ∈ blockObstruction n V := by
  refine ⟨Pi.single i ⟨v, hv⟩, ?_⟩
  rw [blockObstructionMap_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    show hBlockIncl H n j (0 : H) = 0
    exact map_zero _
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The escape transfers to the coordinates.** -/
theorem coord_mem_orthogonal (V : Submodule ℂ H) {eta : BlockSpace H n}
    (heta : eta ∈ (blockObstruction n V)ᗮ) (i : Fin n) :
    hBlockProj H n i eta ∈ Vᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  have h := (Submodule.mem_orthogonal _ _).mp heta (hBlockIncl H n i u)
    (hBlockIncl_mem_blockObstruction V i hu)
  rwa [inner_hBlockIncl_left] at h

end

end ShulmanFill
end GroupApproximation
