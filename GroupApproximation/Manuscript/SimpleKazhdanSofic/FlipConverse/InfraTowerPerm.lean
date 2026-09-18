import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraTowerPermCocycle
import GroupApproximation.Meta.AxiomGuard

/-!
# Tower permutations, part 2: `Sym(n)` embeds in `[[T]]` along a clopen tower

Infrastructure for census row `2e7c7d9ab149` (tex: "for topological full groups the converse
holds"; the key is absent from the current tex, so there is no line number).  Lane sk-flip-04.

Let `T : X ≃ₜ X`, `V` clopen, `k : Fin n → ℤ`, and the levels `T^{k i} V` pairwise disjoint.

* `towerHomeo`: `towerFun T V k π` is a homeomorphism with inverse `towerFun T V k π⁻¹`
  (`towerFun_mul`, `towerFun_one`); both are continuous (`continuous_towerFun`).
* `towerHomeo_mem`: it lies in `[[T]]`, with the continuous cocycle `towerCocycle T V k π`.
* `towerPerm : Equiv.Perm (Fin n) →* [[T]]`; the homomorphism law is `towerFun_mul`.
* `towerPerm_supportedIn`: `towerPerm π` is supported in the tower `⋃_i T^{k i} V`.
* `towerPerm_level`: `towerPerm π (T^{k i} v) = T^{k (π i)} v` for `v ∈ V`.
* `towerPerm_injective`: if `V ≠ ∅`, pick `v ∈ V`; `towerPerm π = towerPerm σ` gives
  `T^{k (π i)} v = T^{k (σ i)} v`, a common point of the levels `T^{k (π i)} V` and
  `T^{k (σ i)} V`, so `π i = σ i` by disjointness.  No aperiodicity is needed.

The consecutive-exponent form of the lane (`k i = i`, disjointness indexed by `i < n`) is in
`InfraTowerPermNat`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

variable {X : Type*} [TopologicalSpace X]

/-- The tower permutation `π` as a homeomorphism of `X`. -/
noncomputable def towerHomeo (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ) (hV : IsClopen V)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π : Equiv.Perm (Fin n)) : X ≃ₜ X :=
  ⟨⟨towerFun T V k π, towerFun T V k π⁻¹,
    fun z => by rw [← towerFun_mul T hdisj, inv_mul_cancel, towerFun_one T hdisj],
    fun z => by rw [← towerFun_mul T hdisj, mul_inv_cancel, towerFun_one T hdisj]⟩,
    continuous_towerFun T hV k π, continuous_towerFun T hV k π⁻¹⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerHomeo

theorem towerHomeo_apply (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ) (hV : IsClopen V)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π : Equiv.Perm (Fin n)) (z : X) : towerHomeo T V k hV hdisj π z = towerFun T V k π z :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerHomeo_apply

theorem towerHomeo_mem (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ) (hV : IsClopen V)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π : Equiv.Perm (Fin n)) : towerHomeo T V k hV hdisj π ∈ topologicalFullGroup T :=
  mem_topologicalFullGroup.2
    ⟨towerCocycle T V k π, continuous_towerCocycle T hV k π, fun _ => rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerHomeo_mem

/-- Permutations of the levels of a clopen tower, as a homomorphism `Sym(n) → [[T]]`. -/
noncomputable def towerPerm (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ) (hV : IsClopen V)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V)) :
    Equiv.Perm (Fin n) →* topologicalFullGroup T where
  toFun π := ⟨towerHomeo T V k hV hdisj π, towerHomeo_mem T V k hV hdisj π⟩
  map_one' := Subtype.ext <| Homeomorph.ext fun z => towerFun_one T hdisj z
  map_mul' π σ := Subtype.ext <| Homeomorph.ext fun z => towerFun_mul T hdisj π σ z

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm

theorem towerPerm_apply (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ) (hV : IsClopen V)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π : Equiv.Perm (Fin n)) (z : X) :
    ((towerPerm T V k hV hdisj π : topologicalFullGroup T) : X ≃ₜ X) z = towerFun T V k π z :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm_apply

theorem towerPerm_level (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ) (hV : IsClopen V)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π : Equiv.Perm (Fin n)) (i : Fin n) {v : X} (hv : v ∈ V) :
    ((towerPerm T V k hV hdisj π : topologicalFullGroup T) : X ≃ₜ X) ((T ^ k i) v) =
      (T ^ k (π i)) v := by
  rw [towerPerm_apply]
  exact towerFun_level T hdisj π i hv

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm_level

theorem towerPerm_supportedIn (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ) (hV : IsClopen V)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (π : Equiv.Perm (Fin n)) :
    SupportedIn ((towerPerm T V k hV hdisj π : topologicalFullGroup T) : X ≃ₜ X)
      (⋃ i : Fin n, (T ^ k i) '' V) := by
  intro z hz
  rw [towerPerm_apply]
  refine towerFun_of_notMem T V k π fun i hi => hz ?_
  exact Set.mem_iUnion.2 ⟨i, (mem_image_homeoPow_iff T (k i) V z).2 hi⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm_supportedIn

theorem towerPerm_injective (T : X ≃ₜ X) (V : Set X) {n : ℕ} (k : Fin n → ℤ) (hV : IsClopen V)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V))
    (hne : V.Nonempty) : Function.Injective (towerPerm T V k hV hdisj) := by
  obtain ⟨v, hv⟩ := hne
  intro π σ hπσ
  refine Equiv.ext fun i => ?_
  have h1 : (T ^ k (π i)) v = (T ^ k (σ i)) v := by
    rw [← towerPerm_level T V k hV hdisj π i hv, ← towerPerm_level T V k hV hdisj σ i hv, hπσ]
  by_contra hij
  have hA : (T ^ k (π i)) v ∈ (T ^ k (π i)) '' V := Set.mem_image_of_mem _ hv
  have hB : (T ^ k (π i)) v ∈ (T ^ k (σ i)) '' V := ⟨v, hv, h1.symm⟩
  exact Set.disjoint_left.1 (hdisj (π i) (σ i) hij) hA hB

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.towerPerm_injective

/-- Lane sk-flip-04 endpoint (general exponents): a nonempty clopen `V` whose translates
`T^{k i} V` are pairwise disjoint carries an injective homomorphism `Sym(n) → [[T]]`, supported
in the tower and acting by `T^{k i} v ↦ T^{k (π i)} v` on `V`. -/
theorem exists_towerPerm_embedding (T : X ≃ₜ X) {V : Set X} (hV : IsClopen V) (hne : V.Nonempty)
    {n : ℕ} (k : Fin n → ℤ)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V)) :
    ∃ φ : Equiv.Perm (Fin n) →* topologicalFullGroup T, Function.Injective φ ∧
      (∀ π, SupportedIn ((φ π : topologicalFullGroup T) : X ≃ₜ X) (⋃ i : Fin n, (T ^ k i) '' V)) ∧
      ∀ π (i : Fin n) (v : X), v ∈ V →
        ((φ π : topologicalFullGroup T) : X ≃ₜ X) ((T ^ k i) v) = (T ^ k (π i)) v :=
  ⟨towerPerm T V k hV hdisj, towerPerm_injective T V k hV hdisj hne,
    towerPerm_supportedIn T V k hV hdisj, fun π i _ hv => towerPerm_level T V k hV hdisj π i hv⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_towerPerm_embedding

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
