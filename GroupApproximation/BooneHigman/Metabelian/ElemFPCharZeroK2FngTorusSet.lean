import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngTorusDiag
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPPTorus
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngFourGroup
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# The finite torus family `T_m` and the torus-stability step (lane `bh-met-92w`, part 2)

* `czK2FngTorus_torusSet n m`: the finite set of torus elements `H_ab(v)` of `St_n(ℤ[1/m])`,
  `a ≠ b`, `v ∈ {-1, m}` (`czStFourFP_u m`), the intended `T` of `czK2FngFour_TorusStatement`.
  It is finite (`czK2FngTorus_torusSet_finite`) and its images in `E_n(ℤ[1/m])` pairwise commute
  (`czK2FngTorus_torusSet_commute`, from `czK2FngTorus_projection_H_commute`).
* `czK2FngTorus_fng_of_le`: for a fixed `m`, `K₂(4, ℤ[1/m]) ≤ ⟪S⟫ ⊔ ⟨T_m⟩` with `S ⊆ K₂` finite
  gives finite normal generation.  **LOUD: this is the torus residual with `T` fixed; as a
  Statement it is EQUIVALENT to the `m`-slice of the target** (take `S` a normal generating set).
  It is a helper, not a residual.
* `czK2FngTorus_succ_of_le_sup`: the torus-stability step for any ring `R` and rank `n`:
  if `K₂(n, R)` is finitely normally generated and `K₂(n+1, R) ≤ ⟪stab K₂(n, R)⟫ ⊔ ⟨T⟩` for a
  finite `T` with pairwise commuting images, then `K₂(n+1, R)` is finitely normally generated.
  This weakens the hypothesis `K₂(n+1) ≤ stab K₂(n)` of `czK2Fng_succ_of_le_map` twice: the
  stabilised `K₂(n)` may be conjugated, and a commuting-torus error term is allowed.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- The two torus parameters `v ∈ {-1, m}` of `ℤ[1/m]ˣ`. -/
noncomputable def czK2FngTorus_unit (m : ℕ) (b : Bool) : (Localization.Away (m : ℤ))ˣ :=
  cond b (czStFourFP_u m) (-1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_unit

/-- The finite torus family `T_m = {H_ab(v) : a ≠ b, v ∈ {-1, m}}` in `St_n(ℤ[1/m])`. -/
noncomputable def czK2FngTorus_torusSet (n m : ℕ) :
    Set (SteinbergGroup (Fin n) (Localization.Away (m : ℤ))) :=
  Set.range fun q : {p : Fin n × Fin n // p.1 ≠ p.2} × Bool ↦
    czStFourFP_H q.1.1.1 q.1.1.2 q.1.2 (czK2FngTorus_unit m q.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_torusSet

theorem czK2FngTorus_torusSet_finite (n m : ℕ) : (czK2FngTorus_torusSet n m).Finite :=
  Set.finite_range _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_torusSet_finite

/-- The images of the torus family in `E_n(ℤ[1/m])` pairwise commute. -/
theorem czK2FngTorus_torusSet_commute (n m : ℕ) :
    ∀ x ∈ czK2FngTorus_torusSet n m, ∀ y ∈ czK2FngTorus_torusSet n m,
      projection x * projection y = projection y * projection x := by
  rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩
  exact czK2FngTorus_projection_H_commute _ _ _ _ q.1.2 q'.1.2 _ _

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_torusSet_commute

/-- **Fixed-torus form (helper; equivalent to the `m`-slice, see the module docstring).** -/
theorem czK2FngTorus_fng_of_le (m : ℕ)
    (S : Set (SteinbergGroup (Fin 4) (Localization.Away (m : ℤ)))) (hS : S.Finite)
    (hSK : S ⊆ K2 (Fin 4) (Localization.Away (m : ℤ)))
    (hle : K2 (Fin 4) (Localization.Away (m : ℤ)) ≤
      Subgroup.normalClosure S ⊔ Subgroup.closure (czK2FngTorus_torusSet 4 m)) :
    (K2 (Fin 4) (Localization.Away (m : ℤ))).IsFinitelyNormallyGenerated :=
  czK2FngFour_ker_fng_of_le_sup_closure
    (projection (I := Fin 4) (R := Localization.Away (m : ℤ))) S _ hS hSK
    (czK2FngTorus_torusSet_finite 4 m) (czK2FngTorus_torusSet_commute 4 m) hle

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_fng_of_le

/-- **Torus-stability step, any ring.**  `K₂(n, R)` finitely normally generated and
`K₂(n+1, R) ≤ ⟪stab K₂(n, R)⟫ ⊔ ⟨T⟩` (`T` finite, commuting images) give finite normal
generation of `K₂(n+1, R)` in `St_{n+1}(R)`. -/
theorem czK2FngTorus_succ_of_le_sup {R : Type*} [Ring R] {n : ℕ}
    (hfn : (K2 (Fin n) R).IsFinitelyNormallyGenerated) (T : Set (St (n + 1) R))
    (hT : T.Finite)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, projection x * projection y = projection y * projection x)
    (hle : K2 (Fin (n + 1)) R ≤
      Subgroup.normalClosure (stab n R '' K2 (Fin n) R) ⊔ Subgroup.closure T) :
    (K2 (Fin (n + 1)) R).IsFinitelyNormallyGenerated := by
  obtain ⟨s, hsfin, hs⟩ := hfn
  have hsK : s ⊆ K2 (Fin n) R := by
    intro k hk
    rw [← hs]
    exact Subgroup.subset_normalClosure hk
  have hnc : Subgroup.normalClosure (stab n R '' K2 (Fin n) R) ≤
      Subgroup.normalClosure (stab n R '' s) := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k ∈ Subgroup.normalClosure s := by
      rw [hs]
      exact hk
    exact Subgroup.map_normalClosure_le s (stab n R) (Subgroup.mem_map_of_mem _ hk')
  have hSK : stab n R '' s ⊆ K2 (Fin (n + 1)) R := by
    rintro _ ⟨k, hk, rfl⟩
    exact (K2Stab n R ⟨k, hsK hk⟩).2
  exact czK2FngFour_ker_fng_of_le_sup_closure (projection (I := Fin (n + 1)) (R := R))
    (stab n R '' s) T (hsfin.image _) hSK hT hcomm (hle.trans (sup_le_sup_right hnc _))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_succ_of_le_sup

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
