import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.TrivialCharacterState

/-!
# Hulanicki: the trivial character of `C⋆_r(G)` for amenable `G`

Lane TWWUCT (work order WO-TWWCore-2), third step of Hulanicki's theorem.
The limit state `ω` of almost invariant unit vectors satisfies
`ω(S λ_g) = ω(S) = ω(λ_g S)`.  Hence `ω(λ_g) = 1`, and every `λ_g` lies in the
multiplicative domain
`M = {T | ∀ S, ω(S T) = ω(S) ω(T) ∧ ω(T S) = ω(T) ω(S)}`.
`M` is a norm-closed subalgebra of `B(ℓ²(G))`.  It contains `λ_g` and
`λ_g⋆ = λ_{g⁻¹}`, so it contains the closed star subalgebra `C⋆_r(G)` that they
generate.  Restricting `ω` to `C⋆_r(G)` gives a star algebra homomorphism
`χ : C⋆_r(G) → ℂ` with `χ(λ_g) = 1`.

* `AlmostInvariantVectors.multDomain`, `isClosed_multDomain`.
* `AlmostInvariantVectors.mem_multDomain_of_mem`.
* `AlmostInvariantVectors.trivialCharacter`, `trivialCharacter_leftRegular`.
* `exists_trivialCharacter`.
-/

namespace GroupApproximation.Full.TWWUCT

open Filter Topology ReducedGroupCStarTrace

universe u

variable {G : Type u} [Group G]

/-- `λ_g` belongs to the concrete reduced group C⋆-algebra. -/
theorem leftRegularOperator_mem_reduced (g : G) :
    leftRegularOperator G g ∈ reducedGroupCStarSubalgebra G :=
  StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ (Set.range (leftRegularOperator G)) ⟨g, rfl⟩)

namespace AlmostInvariantVectors

variable (V : AlmostInvariantVectors G)

/-- The multiplicative domain of the limit state. -/
noncomputable def multDomain : Subalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) where
  carrier := {T | ∀ S : GroupHilbert G →L[ℂ] GroupHilbert G,
    V.limitState (S * T) = V.limitState S * V.limitState T ∧
      V.limitState (T * S) = V.limitState T * V.limitState S}
  mul_mem' := by
    intro T₁ T₂ h₁ h₂ S
    refine ⟨?_, ?_⟩
    · rw [← mul_assoc, (h₂ (S * T₁)).1, (h₁ S).1, (h₂ T₁).1]
      ring
    · rw [mul_assoc, (h₁ (T₂ * S)).2, (h₂ S).2, (h₂ T₁).1]
      ring
  add_mem' := by
    intro T₁ T₂ h₁ h₂ S
    refine ⟨?_, ?_⟩
    · rw [mul_add, map_add, map_add, (h₁ S).1, (h₂ S).1]
      ring
    · rw [add_mul, map_add, map_add, (h₁ S).2, (h₂ S).2]
      ring
  algebraMap_mem' := by
    intro c S
    rw [Algebra.algebraMap_eq_smul_one]
    refine ⟨?_, ?_⟩ <;>
      simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul, map_smul, V.limitState_one,
        smul_eq_mul] <;>
      ring

theorem mem_multDomain_iff {T : GroupHilbert G →L[ℂ] GroupHilbert G} :
    T ∈ V.multDomain ↔ ∀ S : GroupHilbert G →L[ℂ] GroupHilbert G,
      V.limitState (S * T) = V.limitState S * V.limitState T ∧
        V.limitState (T * S) = V.limitState T * V.limitState S :=
  Iff.rfl

theorem isClosed_multDomain :
    IsClosed (V.multDomain : Set (GroupHilbert G →L[ℂ] GroupHilbert G)) := by
  change IsClosed {T : GroupHilbert G →L[ℂ] GroupHilbert G |
    ∀ S : GroupHilbert G →L[ℂ] GroupHilbert G,
      V.limitState (S * T) = V.limitState S * V.limitState T ∧
        V.limitState (T * S) = V.limitState T * V.limitState S}
  rw [Set.setOf_forall]
  refine isClosed_iInter fun S ↦ ?_
  rw [Set.setOf_and]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_eq (V.limitState.continuous.comp (continuous_const_mul S))
      (continuous_const.mul V.limitState.continuous)
  · exact isClosed_eq (V.limitState.continuous.comp (continuous_mul_const S))
      (V.limitState.continuous.mul continuous_const)

theorem limitState_leftRegular (g : G) : V.limitState (leftRegularOperator G g) = 1 := by
  have h := V.limitState_mul_leftRegular 1 g
  rwa [one_mul, V.limitState_one] at h

theorem leftRegularOperator_mem_multDomain (g : G) : leftRegularOperator G g ∈ V.multDomain := by
  rw [mem_multDomain_iff]
  intro S
  rw [V.limitState_leftRegular g, mul_one, one_mul]
  exact ⟨V.limitState_mul_leftRegular S g, V.limitState_leftRegular_mul S g⟩

theorem adjoin_le_multDomain :
    (StarAlgebra.adjoin ℂ (Set.range (leftRegularOperator G))).toSubalgebra ≤ V.multDomain := by
  rw [StarAlgebra.adjoin_toSubalgebra]
  refine Algebra.adjoin_le ?_
  rintro T (⟨g, rfl⟩ | hT)
  · exact V.leftRegularOperator_mem_multDomain g
  · obtain ⟨h, hh⟩ : star T ∈ Set.range (leftRegularOperator G) := hT
    have hT' : T = leftRegularOperator G h⁻¹ := by
      rw [← GroupVonNeumann.star_leftRegularOperator, hh, star_star]
    rw [hT']
    exact V.leftRegularOperator_mem_multDomain h⁻¹

/-- The reduced group C⋆-algebra lies in the multiplicative domain. -/
theorem mem_multDomain_of_mem {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ reducedGroupCStarSubalgebra G) : T ∈ V.multDomain := by
  have hsub : ((StarAlgebra.adjoin ℂ (Set.range (leftRegularOperator G)) :
        StarSubalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G)) :
          Set (GroupHilbert G →L[ℂ] GroupHilbert G)) ⊆
      (V.multDomain : Set (GroupHilbert G →L[ℂ] GroupHilbert G)) :=
    fun x hx ↦ V.adjoin_le_multDomain hx
  have hT' : T ∈ closure ((StarAlgebra.adjoin ℂ (Set.range (leftRegularOperator G)) :
        StarSubalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G)) :
          Set (GroupHilbert G →L[ℂ] GroupHilbert G)) :=
    hT
  exact closure_minimal hsub V.isClosed_multDomain hT'

theorem limitState_algebraMap (c : ℂ) :
    V.limitState (algebraMap ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, V.limitState_one, smul_eq_mul, mul_one]

/-- The trivial character of `C⋆_r(G)`, the restriction of the limit state. -/
noncomputable def trivialCharacter : ReducedGroupCStar G →⋆ₐ[ℂ] ℂ where
  toFun a := V.limitState (a : GroupHilbert G →L[ℂ] GroupHilbert G)
  map_one' := V.limitState_one
  map_mul' a b := (V.mem_multDomain_iff.mp (V.mem_multDomain_of_mem b.2)
    (a : GroupHilbert G →L[ℂ] GroupHilbert G)).1
  map_zero' := map_zero V.limitState
  map_add' a b := map_add V.limitState (a : GroupHilbert G →L[ℂ] GroupHilbert G)
    (b : GroupHilbert G →L[ℂ] GroupHilbert G)
  commutes' c := V.limitState_algebraMap c
  map_star' a := V.limitState_star (a : GroupHilbert G →L[ℂ] GroupHilbert G)

theorem trivialCharacter_apply (a : ReducedGroupCStar G) :
    V.trivialCharacter a = V.limitState (a : GroupHilbert G →L[ℂ] GroupHilbert G) :=
  rfl

theorem trivialCharacter_leftRegular (g : G) :
    V.trivialCharacter ⟨leftRegularOperator G g, leftRegularOperator_mem_reduced g⟩ = 1 :=
  V.limitState_leftRegular g

end AlmostInvariantVectors

/-- **Hulanicki.**  A countable amenable group has a character on `C⋆_r(G)`
sending every `λ_g` to `1`. -/
theorem exists_trivialCharacter [Countable G] (hG : Amenability.IsAmenable G) :
    ∃ χ : ReducedGroupCStar G →⋆ₐ[ℂ] ℂ,
      ∀ g : G, χ ⟨leftRegularOperator G g, leftRegularOperator_mem_reduced g⟩ = 1 := by
  obtain ⟨V⟩ := exists_almostInvariantVectors hG
  exact ⟨V.trivialCharacter, V.trivialCharacter_leftRegular⟩

end GroupApproximation.Full.TWWUCT
