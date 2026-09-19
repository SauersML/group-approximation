import GroupApproximation.Higman.RowKernel

/-!
# Higman's endomorphisms `ξ_l : b ↦ b_l, c ↦ c²`

Higman's Example 3.7 --- the half row is benign --- runs on two injective
endomorphisms of `F₀ = ⟨b, c⟩`:

    ξ₁ : b ↦ b₁, c ↦ c²        and        ξ₀ : b ↦ b₀ = b, c ↦ c² .

Their point is what they do to the row: `ξ_l bᵢ = b_{2i+l}`, so `ξ₁` produces
the odd indices and `ξ₀` the even ones, and *every* nonnegative index is
reached from `b₀` by a sequence of them --- the binary expansion of the index.
That is the generation half of Example 3.7.  The other half is that they do
not reach anything else, and for that one needs them to be injective, and one
needs the half row to be stable under both of them in *both* directions.

## Why `c ↦ c²`

Because `c ↦ c` would make `ξ_l` an inner automorphism, and an automorphism
generates the whole row, not the half.  Doubling the `c`-exponent is exactly
what makes the two endomorphisms *non-surjective*, so that iterating them
walks in one direction only; the binary expansion is the shape of that walk.

## How injectivity is proved

Not by ping-pong and not by a normal form.  If `ξ_l x = 1` then `x` has
`c`-exponent zero --- because `ξ_l` doubles the exponent, and
`Higman.RowKernel` identifies the row as the kernel of the exponent --- so `x`
is a word in the `bᵢ`, which are a free basis.  On that basis `ξ_l` is the
relabelling `i ↦ 2i + l` of `FreeGroup ℤ`, which is injective because
`i ↦ (i - l)/2` undoes it.  So the whole argument is: doubling is injective on
`ℤ`, and everything else is transport.

## Contents

* `xi`, `xi_row` --- the endomorphism and its action on the row.
* `mem_Row_of_xi_mem_Row` --- it reflects membership in the row.
* `mapIdx`, `xi_basisHom` --- it is the relabelling `i ↦ 2i + l` on the basis.
* `xi_injective`.
* `xi_mem_halfRow`, `mem_halfRow_of_xi_mem_halfRow` --- stability of the half
  row in both directions, for `l = 0` and `l = 1`.
* `range_xi`, `fg_range_xi` --- the image is the two-generator subgroup
  `⟨b_l, c²⟩`, so it is finitely generated, which is what the HNN extension
  built on `ξ_l` needs in order to be finitely presented.
-/

namespace GroupApproximation
namespace Higman
namespace Row

/-! ## 1.  The endomorphism -/

/-- **Higman's endomorphism** `ξ_l`: `b ↦ bₗ`, `c ↦ c²`. -/
def xi (l : ℤ) : F₀ →* F₀ :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then row l else c ^ (2 : ℤ))

@[simp] theorem xi_b (l : ℤ) : xi l b = row l := by
  simp [xi, b]

@[simp] theorem xi_c (l : ℤ) : xi l c = c ^ (2 : ℤ) := by
  simp [xi, c]

theorem xi_zpow_c (l n : ℤ) : xi l (c ^ n) = c ^ (2 * n) := by
  rw [map_zpow, xi_c, ← zpow_mul]

/-- **What `ξ_l` does to the row**: it doubles the index and shifts by `l`. -/
theorem xi_row (l i : ℤ) : xi l (row i) = row (2 * i + l) := by
  have hneg : (2 : ℤ) * (-i) = -(2 * i) := by ring
  have hx : xi l (row i) = c ^ (-(2 * i)) * row l * c ^ (2 * i) := by
    calc
      xi l (row i) = xi l (c ^ (-i)) * xi l b * xi l (c ^ i) := by
        rw [row, map_mul, map_mul]
      _ = c ^ (-(2 * i)) * row l * c ^ (2 * i) := by
        rw [xi_b, xi_zpow_c, xi_zpow_c, hneg]
  rw [hx, conj_row']
  congr 1
  ring

/-! ## 2.  The row and the exponent -/

theorem xi_mem_Row (l : ℤ) {x : F₀} (hx : x ∈ Row) : xi l x ∈ Row := by
  refine Subgroup.closure_induction (p := fun z _ => xi l z ∈ Row) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    rw [xi_row]
    exact row_mem _
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro y z _ _ hy hz
    rw [map_mul]
    exact Subgroup.mul_mem _ hy hz
  · intro y _ hy
    rw [map_inv]
    exact Subgroup.inv_mem _ hy

/-- **`ξ_l` reflects membership in the row.**  It doubles the `c`-exponent, and
the row is exactly the words of exponent zero. -/
theorem mem_Row_of_xi_mem_Row (l : ℤ) {x : F₀} (h : xi l x ∈ Row) : x ∈ Row := by
  obtain ⟨r, hr, hx⟩ := exists_row_mul x
  have hxi : xi l x = xi l r * c ^ (2 * Multiplicative.toAdd (expHom x)) := by
    conv_lhs => rw [hx]
    rw [map_mul, xi_zpow_c]
  have hxr : xi l r ∈ Row := xi_mem_Row l hr
  have hc : c ^ (2 * Multiplicative.toAdd (expHom x)) ∈ Row := by
    have heq : c ^ (2 * Multiplicative.toAdd (expHom x)) = (xi l r)⁻¹ * xi l x := by
      rw [hxi]
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxr) h
  have h2 : 2 * Multiplicative.toAdd (expHom x) = 0 := zpow_c_mem_Row_iff.mp hc
  have h0 : Multiplicative.toAdd (expHom x) = 0 := by omega
  rw [h0, zpow_zero, mul_one] at hx
  rw [hx]
  exact hr

/-! ## 3.  On the basis, `ξ_l` is the relabelling `i ↦ 2i + l` -/

/-- The relabelling of indices. -/
def mapIdx (l : ℤ) : FreeGroup ℤ →* FreeGroup ℤ :=
  FreeGroup.map (fun i : ℤ => 2 * i + l)

theorem mapIdx_of (l i : ℤ) : mapIdx l (FreeGroup.of i) = FreeGroup.of (2 * i + l) := rfl

theorem xi_basisHom (l : ℤ) (V : FreeGroup ℤ) :
    xi l (basisHom V) = basisHom (mapIdx l V) := by
  have h : (xi l).comp basisHom = basisHom.comp (mapIdx l) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show xi l (basisHom (FreeGroup.of i)) = basisHom (mapIdx l (FreeGroup.of i))
    rw [basisHom_of, xi_row, mapIdx_of, basisHom_of]
  exact congrArg (fun f : FreeGroup ℤ →* F₀ => f V) h

theorem mapIdx_injective (l : ℤ) : Function.Injective (mapIdx l) := by
  have hcomp : (fun j : ℤ => (j - l) / 2) ∘ (fun i : ℤ => 2 * i + l) = id := by
    funext i
    show (2 * i + l - l) / 2 = i
    have h : 2 * i + l - l = 2 * i := by ring
    rw [h]
    exact Int.mul_ediv_cancel_left i (by norm_num)
  have key : ∀ z : FreeGroup ℤ,
      FreeGroup.map (fun j : ℤ => (j - l) / 2) (mapIdx l z) = z := by
    intro z
    unfold mapIdx
    rw [FreeGroup.map.comp, hcomp, FreeGroup.map.id]
  intro x y hxy
  rw [← key x, ← key y, hxy]

/-- **`ξ_l` is injective.** -/
theorem xi_injective (l : ℤ) : Function.Injective (xi l) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxR : xi l x ∈ Row := by
    rw [hx]
    exact Subgroup.one_mem _
  have hR : x ∈ Row := mem_Row_of_xi_mem_Row l hxR
  have hrange : x ∈ basisHom.range := by
    rw [range_basisHom]
    exact hR
  obtain ⟨V, hV⟩ := hrange
  have h1 : basisHom (mapIdx l V) = 1 := by
    rw [← xi_basisHom, hV, hx]
  have h2 : mapIdx l V = 1 := by
    apply basisHom_injective
    rw [h1, map_one]
  have h3 : V = 1 := by
    apply mapIdx_injective l
    rw [h2, map_one]
  rw [← hV, h3, map_one]

/-! ## 4.  The half row is stable, both ways -/

theorem xi_mem_halfRow {l : ℤ} (hl : 0 ≤ l) {x : F₀} (hx : x ∈ HalfRow) :
    xi l x ∈ HalfRow := by
  rw [halfRow_eq_closure] at hx ⊢
  refine Subgroup.closure_induction
    (p := fun z _ => xi l z ∈
      Subgroup.closure ((fun i : ℤ => row i) '' {i : ℤ | 0 ≤ i})) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    have hi' : 0 ≤ i := hi
    rw [xi_row]
    refine Subgroup.subset_closure ⟨2 * i + l, ?_, rfl⟩
    show (0 : ℤ) ≤ 2 * i + l
    omega
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro y z _ _ hy hz
    rw [map_mul]
    exact Subgroup.mul_mem _ hy hz
  · intro y _ hy
    rw [map_inv]
    exact Subgroup.inv_mem _ hy

/-- The relabelling commutes with the retraction that deletes negative
letters, because for `l = 0` and `l = 1` the index `2i + l` is nonnegative
exactly when `i` is. -/
theorem killNeg_mapIdx {l : ℤ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (W : FreeGroup ℤ) :
    killNeg (mapIdx l W) = mapIdx l (killNeg W) := by
  have h : killNeg.comp (mapIdx l) = (mapIdx l).comp killNeg := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    show killNeg (mapIdx l (FreeGroup.of i)) = mapIdx l (killNeg (FreeGroup.of i))
    rw [mapIdx_of, killNeg_of, killNeg_of]
    by_cases hi : 0 ≤ i
    · rw [if_pos hi, if_pos (show (0 : ℤ) ≤ 2 * i + l by omega), mapIdx_of]
    · rw [if_neg hi, if_neg (show ¬ (0 : ℤ) ≤ 2 * i + l by omega), map_one]
  exact congrArg (fun f : FreeGroup ℤ →* FreeGroup ℤ => f W) h

theorem mem_posSub_of_mapIdx_mem {l : ℤ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    {W : FreeGroup ℤ} (h : mapIdx l W ∈ posSub) : W ∈ posSub := by
  rw [mem_posSub_iff] at h ⊢
  have h' : mapIdx l (killNeg W) = mapIdx l W := by
    rw [← killNeg_mapIdx hl0 hl1, h]
  exact mapIdx_injective l h'

/-- **`ξ_l` reflects membership in the half row**, for `l = 0` and `l = 1`.
This is the direction Britton's lemma consumes: a word the stable letter
carries into the half row was in the half row to begin with. -/
theorem mem_halfRow_of_xi_mem_halfRow {l : ℤ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    {x : F₀} (h : xi l x ∈ HalfRow) : x ∈ HalfRow := by
  have hR : x ∈ Row := mem_Row_of_xi_mem_Row l (halfRow_le_Row h)
  have hrange : x ∈ basisHom.range := by
    rw [range_basisHom]
    exact hR
  obtain ⟨V, hV⟩ := hrange
  have h1 : basisHom (mapIdx l V) ∈ HalfRow := by
    rw [← xi_basisHom, hV]
    exact h
  have h2 : mapIdx l V ∈ posSub := mem_halfRow_iff.mp h1
  have h3 : V ∈ posSub := mem_posSub_of_mapIdx_mem hl0 hl1 h2
  rw [← hV]
  exact ⟨V, h3, rfl⟩

/-! ## 5.  The image is finitely generated -/

theorem closure_bc : Subgroup.closure ({b, c} : Set F₀) = ⊤ := by
  apply top_unique
  intro W _
  refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
  · exact Subgroup.one_mem _
  · intro i
    rcases fin_two_cases i with rfl | rfl
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · intro i hmem
    exact Subgroup.inv_mem _ hmem
  · intro x y hx hy
    exact Subgroup.mul_mem _ hx hy

theorem range_xi (l : ℤ) :
    (xi l).range = Subgroup.closure ({row l, c ^ (2 : ℤ)} : Set F₀) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine FreeGroup.induction_on x ?_ ?_ ?_ ?_
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro i
      rcases fin_two_cases i with rfl | rfl
      · show xi l b ∈ _
        rw [xi_b]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · show xi l c ∈ _
        rw [xi_c]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · intro i hmem
      rw [map_inv]
      exact Subgroup.inv_mem _ hmem
    · intro y z hy hz
      rw [map_mul]
      exact Subgroup.mul_mem _ hy hz
  · refine (Subgroup.closure_le _).mpr ?_
    rintro y hy
    rcases hy with rfl | hy
    · exact ⟨b, xi_b l⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨c, xi_c l⟩

theorem fg_range_xi (l : ℤ) : ((xi l).range).FG := by
  refine (Subgroup.fg_iff _).mpr ⟨{row l, c ^ (2 : ℤ)}, (range_xi l).symm, ?_⟩
  exact (Set.finite_singleton _).insert _

end Row
end Higman
end GroupApproximation
