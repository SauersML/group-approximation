import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraTowerPermCocycle
import GroupApproximation.Meta.AxiomGuard

/-!
# Tower permutations, part 2: `Sym(n)` embeds in `[[T]]` along a clopen tower

Infrastructure for census row `2e7c7d9ab149` (tex: "for topological full groups the converse
holds"; the key is absent from the current tex, so there is no line number).  Lane sk-flip-04.

Let `T : X ≃ₜ X`, `V` clopen and the levels `T^i V` (`i < n`) pairwise disjoint.

* `towerHomeo`: `towerFun T V π` is a homeomorphism with inverse `towerFun T V π⁻¹`
  (`towerFun_mul`, `towerFun_one`); both are continuous (`continuous_towerFun`).
* `towerHomeo_mem`: it lies in `[[T]]`, with the continuous cocycle `towerCocycle T V π`.
* `towerPerm : Equiv.Perm (Fin n) →* [[T]]`; the homomorphism law is `towerFun_mul`.
* `towerPerm_supportedIn`: `towerPerm π` is supported in the tower `⋃_{i<n} T^i V`.
* `towerPerm_level`: `towerPerm π (T^i v) = T^{π i} v` for `v ∈ V`.
* `towerPerm_injective`: if `V ≠ ∅`, pick `v ∈ V`; `towerPerm π = towerPerm σ` gives
  `T^{π i} v = T^{σ i} v`, a common point of the levels `T^{π i} V` and `T^{σ i} V`, so
  `π i = σ i` by disjointness.  No aperiodicity is needed.
* `exists_towerPerm_embedding`: the existential packaging of the three facts above.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

variable {X : Type*} [TopologicalSpace X]

/-- The tower permutation `π` as a homeomorphism of `X`. -/
noncomputable def towerHomeo (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) : X ≃ₜ X :=
  ⟨⟨towerFun T V π, towerFun T V π⁻¹,
    fun z => by rw [← towerFun_mul T hdisj, inv_mul_cancel, towerFun_one T hdisj],
    fun z => by rw [← towerFun_mul T hdisj, mul_inv_cancel, towerFun_one T hdisj]⟩,
    continuous_towerFun T hV π, continuous_towerFun T hV π⁻¹⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerHomeo

theorem towerHomeo_apply (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) (z : X) : towerHomeo T V hV hdisj π z = towerFun T V π z :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerHomeo_apply

theorem towerHomeo_mem (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) : towerHomeo T V hV hdisj π ∈ topologicalFullGroup T :=
  mem_topologicalFullGroup.2 ⟨towerCocycle T V π, continuous_towerCocycle T hV π, fun _ => rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerHomeo_mem

/-- Permutations of the levels of a clopen tower, as a homomorphism `Sym(n) → [[T]]`. -/
noncomputable def towerPerm (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V)) :
    Equiv.Perm (Fin n) →* topologicalFullGroup T where
  toFun π := ⟨towerHomeo T V hV hdisj π, towerHomeo_mem T V hV hdisj π⟩
  map_one' := Subtype.ext <| Homeomorph.ext fun z => towerFun_one T hdisj z
  map_mul' π σ := Subtype.ext <| Homeomorph.ext fun z => towerFun_mul T hdisj π σ z

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm

theorem towerPerm_apply (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) (z : X) :
    ((towerPerm T V hV hdisj π : topologicalFullGroup T) : X ≃ₜ X) z = towerFun T V π z :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm_apply

theorem towerPerm_level (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) (i : Fin n) {v : X} (hv : v ∈ V) :
    ((towerPerm T V hV hdisj π : topologicalFullGroup T) : X ≃ₜ X) ((T ^ ((i : ℕ) : ℤ)) v) =
      (T ^ ((π i : ℕ) : ℤ)) v := by
  rw [towerPerm_apply]
  exact towerFun_level T hdisj π i hv

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm_level

theorem towerPerm_supportedIn (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (π : Equiv.Perm (Fin n)) :
    SupportedIn ((towerPerm T V hV hdisj π : topologicalFullGroup T) : X ≃ₜ X)
      (⋃ i : Fin n, (T ^ ((i : ℕ) : ℤ)) '' V) := by
  intro z hz
  rw [towerPerm_apply]
  refine towerFun_of_notMem T V π fun i hi => hz ?_
  exact Set.mem_iUnion.2 ⟨i, (mem_image_homeoPow_iff T ((i : ℕ) : ℤ) V z).2 hi⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm_supportedIn

theorem towerPerm_injective (T : X ≃ₜ X) (V : Set X) (hV : IsClopen V) {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V))
    (hne : V.Nonempty) : Function.Injective (towerPerm T V hV hdisj) := by
  obtain ⟨v, hv⟩ := hne
  intro π σ hπσ
  refine Equiv.ext fun i => ?_
  have h1 : (T ^ ((π i : ℕ) : ℤ)) v = (T ^ ((σ i : ℕ) : ℤ)) v := by
    rw [← towerPerm_level T V hV hdisj π i hv, ← towerPerm_level T V hV hdisj σ i hv, hπσ]
  by_contra hij
  have hval : (π i : ℕ) ≠ (σ i : ℕ) := fun h => hij (Fin.ext h)
  have hA : (T ^ ((π i : ℕ) : ℤ)) v ∈ (T ^ ((π i : ℕ) : ℤ)) '' V :=
    Set.mem_image_of_mem _ hv
  have hB : (T ^ ((π i : ℕ) : ℤ)) v ∈ (T ^ ((σ i : ℕ) : ℤ)) '' V := ⟨v, hv, h1.symm⟩
  exact Set.disjoint_left.1 (hdisj (π i : ℕ) (π i).2 (σ i : ℕ) (σ i).2 hval) hA hB

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm_injective

/-- Lane sk-flip-04 endpoint: a nonempty clopen `V` whose first `n` translates `T^i V` are
pairwise disjoint carries an injective homomorphism `Sym(n) → [[T]]`, supported in the tower and
acting by `T^i v ↦ T^{π i} v` on `V`. -/
theorem exists_towerPerm_embedding (T : X ≃ₜ X) {V : Set X} (hV : IsClopen V) (hne : V.Nonempty)
    {n : ℕ}
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint ((T ^ (i : ℤ)) '' V) ((T ^ (j : ℤ)) '' V)) :
    ∃ φ : Equiv.Perm (Fin n) →* topologicalFullGroup T, Function.Injective φ ∧
      (∀ π, SupportedIn ((φ π : topologicalFullGroup T) : X ≃ₜ X)
        (⋃ i : Fin n, (T ^ ((i : ℕ) : ℤ)) '' V)) ∧
      ∀ π (i : Fin n) (v : X), v ∈ V →
        ((φ π : topologicalFullGroup T) : X ≃ₜ X) ((T ^ ((i : ℕ) : ℤ)) v) =
          (T ^ ((π i : ℕ) : ℤ)) v :=
  ⟨towerPerm T V hV hdisj, towerPerm_injective T V hV hdisj hne,
    towerPerm_supportedIn T V hV hdisj, fun π i _ hv => towerPerm_level T V hV hdisj π i hv⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_towerPerm_embedding

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
