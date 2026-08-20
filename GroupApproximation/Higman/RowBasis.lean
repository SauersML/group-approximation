import GroupApproximation.Higman.RowSubgroup

/-!
# The row elements are a free basis

`Higman.Row` proves that `Row = ⟨bᵢ : i ∈ ℤ⟩` is benign in `⟨b, c⟩`.  Higman's
Sections 3.2 and 4 need more: that the `bᵢ` *freely* generate, so that a
subset of `ℤ` --- and later a subset of the sequence space --- can be read off
the subgroup it generates.  That is what this file proves.

The proof avoids both ping-pong sets and normal forms in free products.  Let
`F₀` act on `FreeGroup ℤ × ℤ` by

    c · (w, n) = (w, n + 1),        b · (w, n) = (of (-n) · w, n).

Then `bᵢ = c⁻ⁱ b cⁱ` acts on the slice `n = 0` as left multiplication by
`of (-i)`, and it preserves that slice.  So the image of a word `W` in the
`bᵢ` acts on `(1, 0)` as left multiplication by the image of `W` under the
automorphism `of i ↦ of (-i)` of `FreeGroup ℤ`.  If the word dies in `F₀`, the
action is trivial, so `W` dies in `FreeGroup ℤ`.

The action is defined by `FreeGroup.lift` on two explicit permutations, so
nothing beyond the universal property of a free group is used.
-/

namespace GroupApproximation
namespace Higman
namespace Row

/-! ## 1.  The action -/

/-- The set acted on: words in the free group on `ℤ`, tagged by an integer. -/
abbrev Slice : Type := FreeGroup ℤ × ℤ

/-- The permutation `c` acts by. -/
def cPerm : Equiv.Perm Slice where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv p := by
    refine Prod.ext rfl ?_
    show p.2 + 1 - 1 = p.2
    ring
  right_inv p := by
    refine Prod.ext rfl ?_
    show p.2 - 1 + 1 = p.2
    ring

/-- The permutation `b` acts by. -/
def bPerm : Equiv.Perm Slice where
  toFun p := (FreeGroup.of (-p.2) * p.1, p.2)
  invFun p := ((FreeGroup.of (-p.2))⁻¹ * p.1, p.2)
  left_inv p := by
    refine Prod.ext ?_ rfl
    show (FreeGroup.of (-p.2))⁻¹ * (FreeGroup.of (-p.2) * p.1) = p.1
    group
  right_inv p := by
    refine Prod.ext ?_ rfl
    show FreeGroup.of (-p.2) * ((FreeGroup.of (-p.2))⁻¹ * p.1) = p.1
    group

/-- The action of `F₀` on the slice. -/
def act : F₀ →* Equiv.Perm Slice :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then bPerm else cPerm)

@[simp] theorem act_b : act b = bPerm := by
  unfold act b
  rw [FreeGroup.lift.of]
  simp

@[simp] theorem act_c : act c = cPerm := by
  unfold act c
  rw [FreeGroup.lift.of]
  simp

theorem act_c_zpow (i : ℤ) (p : Slice) : act (c ^ i) p = (p.1, p.2 + i) := by
  rw [map_zpow, act_c]
  induction i using Int.induction_on with
  | hz =>
      show p = (p.1, p.2 + 0)
      rw [add_zero]
      exact Prod.ext rfl rfl
  | hp n ih =>
      have hstep : (cPerm ^ ((n : ℤ) + 1)) p = cPerm ((cPerm ^ (n : ℤ)) p) := by
        rw [zpow_add, zpow_one]
        rfl
      rw [hstep, ih]
      show ((p.1, p.2 + (n : ℤ)).1, (p.1, p.2 + (n : ℤ)).2 + 1) = _
      refine Prod.ext rfl ?_
      show p.2 + (n : ℤ) + 1 = p.2 + ((n : ℤ) + 1)
      ring
  | hn n ih =>
      have hstep : (cPerm ^ (-(n : ℤ) - 1)) p = cPerm.symm ((cPerm ^ (-(n : ℤ))) p) := by
        rw [zpow_sub, zpow_one]
        rfl
      rw [hstep, ih]
      show ((p.1, p.2 + -(n : ℤ)).1, (p.1, p.2 + -(n : ℤ)).2 - 1) = _
      refine Prod.ext rfl ?_
      show p.2 + -(n : ℤ) - 1 = p.2 + (-(n : ℤ) - 1)
      ring

/-- **What a row element does on the zero slice.** -/
theorem act_row (i : ℤ) (w : FreeGroup ℤ) :
    act (row i) (w, (0 : ℤ)) = (FreeGroup.of (-i) * w, 0) := by
  unfold row
  rw [map_mul, map_mul]
  show act (c ^ (-i)) (act b (act (c ^ i) (w, (0 : ℤ)))) = _
  rw [act_c_zpow]
  show act (c ^ (-i)) (act b (w, (0 : ℤ) + i)) = _
  rw [act_b]
  show act (c ^ (-i))
    (FreeGroup.of (-((0 : ℤ) + i)) * w, (0 : ℤ) + i) = _
  rw [act_c_zpow]
  refine Prod.ext ?_ ?_
  · show FreeGroup.of (-((0 : ℤ) + i)) * w = FreeGroup.of (-i) * w
    congr 2
    ring
  · show (0 : ℤ) + i + -i = 0
    ring

/-! ## 2.  The basis map -/

/-- The homomorphism from the free group on `ℤ` sending the `i`-th generator to
the `i`-th row element. -/
def basisHom : FreeGroup ℤ →* F₀ := FreeGroup.lift row

@[simp] theorem basisHom_of (i : ℤ) : basisHom (FreeGroup.of i) = row i := by
  unfold basisHom
  rw [FreeGroup.lift.of]

/-- The sign-reversing automorphism of `FreeGroup ℤ`. -/
def negHom : FreeGroup ℤ →* FreeGroup ℤ :=
  FreeGroup.lift (fun i : ℤ => FreeGroup.of (-i))

@[simp] theorem negHom_of (i : ℤ) : negHom (FreeGroup.of i) = FreeGroup.of (-i) := by
  unfold negHom
  rw [FreeGroup.lift.of]

theorem negHom_comp_negHom : negHom.comp negHom = MonoidHom.id (FreeGroup ℤ) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  show negHom (negHom (FreeGroup.of i)) = FreeGroup.of i
  rw [negHom_of, negHom_of, neg_neg]

theorem negHom_injective : Function.Injective negHom := by
  intro x y hxy
  have hx := congrArg (fun f : FreeGroup ℤ →* FreeGroup ℤ => f x) negHom_comp_negHom
  have hy := congrArg (fun f : FreeGroup ℤ →* FreeGroup ℤ => f y) negHom_comp_negHom
  show x = y
  calc x = negHom (negHom x) := hx.symm
    _ = negHom (negHom y) := by rw [hxy]
    _ = y := hy

/-! ## 3.  The action computes the basis map -/

/-- The words whose image acts on the zero slice by left multiplication with
their sign reversal.  It is a subgroup, and it contains the generators. -/
def GoodSub : Subgroup (FreeGroup ℤ) where
  carrier := {W : FreeGroup ℤ | ∀ w : FreeGroup ℤ,
    act (basisHom W) (w, (0 : ℤ)) = (negHom W * w, 0)}
  one_mem' := by
    intro w
    rw [map_one, map_one, map_one, one_mul]
    rfl
  mul_mem' := by
    intro x y hx hy w
    rw [map_mul, map_mul]
    show act (basisHom x) (act (basisHom y) (w, (0 : ℤ))) = _
    rw [hy w, hx (negHom y * w)]
    refine Prod.ext ?_ rfl
    show negHom x * (negHom y * w) = negHom x * negHom y * w
    group
  inv_mem' := by
    intro x hx w
    have hkey : act (basisHom x) ((negHom x)⁻¹ * w, (0 : ℤ)) = (w, 0) := by
      rw [hx ((negHom x)⁻¹ * w)]
      refine Prod.ext ?_ rfl
      show negHom x * ((negHom x)⁻¹ * w) = w
      group
    rw [map_inv, map_inv]
    have : (act (basisHom x))⁻¹ (w, (0 : ℤ)) = ((negHom x)⁻¹ * w, 0) := by
      refine (Equiv.eq_symm_apply _).mpr ?_
      · exact hkey.symm
    show (act (basisHom x))⁻¹ (w, (0 : ℤ)) = _
    rw [this]

theorem goodSub_eq_top : GoodSub = ⊤ := by
  refine top_le_iff.mp ?_
  intro W -
  refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
  · exact Subgroup.one_mem _
  · intro i
    intro w
    rw [basisHom_of, negHom_of, act_row]
  · intro i hmem
    exact Subgroup.inv_mem _ hmem
  · intro x y hx hy
    exact Subgroup.mul_mem _ hx hy

/-! ## 4.  The basis map is injective -/

/-- **The row elements freely generate.** -/
theorem basisHom_injective : Function.Injective basisHom := by
  rw [injective_iff_map_eq_one]
  intro W hW
  have hgood : W ∈ GoodSub := by
    rw [goodSub_eq_top]
    exact Subgroup.mem_top W
  have h := hgood 1
  rw [hW, map_one] at h
  have h1 : ((1 : FreeGroup ℤ), (0 : ℤ)) = (negHom W * 1, 0) := h
  have h2 : negHom W = 1 := by
    have := congrArg Prod.fst h1
    show negHom W = 1
    rw [← mul_one (negHom W)]
    exact this.symm
  have : W = 1 := by
    apply negHom_injective
    rw [h2, map_one]
  exact this

/-- The row subgroup is free on the row elements: the range of the basis map
is exactly it. -/
theorem range_basisHom : basisHom.range = Row := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨W, rfl⟩
    refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro i
      rw [basisHom_of]
      exact row_mem i
    · intro i hmem
      rw [map_inv]
      exact Subgroup.inv_mem _ hmem
    · intro x y hx hy
      rw [map_mul]
      exact Subgroup.mul_mem _ hx hy
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨FreeGroup.of i, basisHom_of i⟩

end Row
end Higman
end GroupApproximation
