import GroupApproximation.Higman.HNNEmbedding

/-!
# The three-generator bridge, part 1: the free basis inside `F(x,y)`

This file formalizes the setup paragraph of the subsection *A three-generator
embedding* of `mf_recognition_complexity.tex`, and the first sentence of the
printed proof of `lem:bridge` (1):

> Let `F = F(x,y,t)` be the free group on `x,y,t`, and let `y_i = x^i y x^{-i}`
> for `i ∈ ℤ`.

> The elements `y_i`, `i ∈ ℤ`, freely generate the normal closure of `y` in
> `F(x,y)` (Lyndon--Schupp, Chapter I).

The manuscript cites Lyndon--Schupp for that sentence.  It is proved here
rather than assumed, by the ping-pong device the repository already uses for
the Higman--Neumann--Neumann family (`Higman.HNNEmbedding`): the free group on
`ℤ` acts on `FreeGroup ℤ × ℤ`, `x` lowers the counter and `y` writes the
counter into the word, so that `y_i` acts on the slice `(·, 0)` exactly as left
multiplication by the `i`-th free generator.

Two statements come out of it, and both are used later:

* `yFreeHom_injective` --- the `y_i` are a free basis;
* `range_yFreeHom_eq_normalClosure` --- the subgroup they generate is the
  normal closure of `y`.

Everything here happens inside the two free groups `F(x,y,t)` and `F(x,y)`;
the group `C` and the HNN extension enter in
`Manuscript/MFRecognition/ThreeGeneratorBridge`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Bridge

/-! ## 1.  The two free groups of the printed setup -/

/-- `F = F(x,y,t)`, the free group on the three printed generators.  The
indices are `x = 0`, `y = 1`, `t = 2`, matching the repository's existing
three-generator presentation map `Higman.BridgeEff.gen3`. -/
abbrev FreeXYT : Type := FreeGroup (Fin 3)

/-- `F(x,y)`, the free group on the first two printed generators, with
`x = 0` and `y = 1`. -/
abbrev FreeXY : Type := FreeGroup (Fin 2)

/-- The printed generator `x` of `F = F(x,y,t)`. -/
def xLetter : FreeXYT := FreeGroup.of 0

/-- The printed generator `y` of `F = F(x,y,t)`. -/
def yLetter : FreeXYT := FreeGroup.of 1

/-- The printed generator `t` of `F = F(x,y,t)`. -/
def tLetter : FreeXYT := FreeGroup.of 2

/-- `y_i = x^i y x^{-i}`, in `F = F(x,y,t)`. -/
def yLetterFam (i : ℤ) : FreeXYT := xLetter ^ i * yLetter * xLetter ^ (-i)

/-- The printed generator `x` of `F(x,y)`. -/
def xTwo : FreeXY := FreeGroup.of 0

/-- The printed generator `y` of `F(x,y)`. -/
def yTwo : FreeXY := FreeGroup.of 1

/-- `y_i = x^i y x^{-i}`, in `F(x,y)`. -/
def yFree (i : ℤ) : FreeXY := xTwo ^ i * yTwo * xTwo ^ (-i)

/-- The homomorphism from the free group on `ℤ` that sends the `i`-th free
generator to `y_i`.  The printed sentence "the `y_i` freely generate" is the
injectivity of this map, `yFreeHom_injective`. -/
def yFreeHom : FreeGroup ℤ →* FreeXY := FreeGroup.lift yFree

theorem yFreeHom_of (i : ℤ) : yFreeHom (FreeGroup.of i) = yFree i := by
  simp [yFreeHom]

/-! ## 2.  The ping-pong action -/

/-- The state of the ping-pong action: a word over `ℤ`, together with the
current exponent of `x`. -/
abbrev St : Type := FreeGroup ℤ × ℤ

/-- `x` lowers the counter. -/
def xPerm : Equiv.Perm St where
  toFun p := (p.1, p.2 - 1)
  invFun p := (p.1, p.2 + 1)
  left_inv p := by
    refine Prod.ext rfl ?_
    show p.2 - 1 + 1 = p.2
    ring
  right_inv p := by
    refine Prod.ext rfl ?_
    show p.2 + 1 - 1 = p.2
    ring

/-- `y` writes the counter into the word. -/
def yPerm : Equiv.Perm St where
  toFun p := (FreeGroup.of p.2 * p.1, p.2)
  invFun p := ((FreeGroup.of p.2)⁻¹ * p.1, p.2)
  left_inv p := by
    refine Prod.ext ?_ rfl
    show (FreeGroup.of p.2)⁻¹ * (FreeGroup.of p.2 * p.1) = p.1
    group
  right_inv p := by
    refine Prod.ext ?_ rfl
    show FreeGroup.of p.2 * ((FreeGroup.of p.2)⁻¹ * p.1) = p.1
    group

/-- The ping-pong action of `F(x,y)`. -/
def act : FreeXY →* Equiv.Perm St :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then xPerm else yPerm)

theorem act_x : act xTwo = xPerm := by
  simp [act, xTwo]

theorem act_y : act yTwo = yPerm := by
  simp [act, yTwo]

theorem act_x_zpow (k : ℤ) (p : St) : act (xTwo ^ k) p = (p.1, p.2 - k) := by
  rw [map_zpow, act_x]
  induction k using Int.induction_on generalizing p with
  | zero =>
      show p = (p.1, p.2 - 0)
      rw [sub_zero]
  | succ n ih =>
      rw [zpow_add, zpow_one]
      change (xPerm ^ (n : ℤ)) (xPerm p) = _
      rw [ih]
      refine Prod.ext rfl ?_
      show p.2 - 1 - (n : ℤ) = p.2 - ((n : ℤ) + 1)
      ring
  | pred n ih =>
      rw [zpow_sub, zpow_one]
      change (xPerm ^ (-(n : ℤ))) (xPerm.symm p) = _
      rw [ih]
      refine Prod.ext rfl ?_
      show p.2 + 1 - -(n : ℤ) = p.2 - (-(n : ℤ) - 1)
      ring

/-- **What the printed family does on the zero slice.**  `y_i` acts as left
multiplication by the `i`-th free generator. -/
theorem act_yFree (i : ℤ) (w : FreeGroup ℤ) :
    act (yFree i) (w, (0 : ℤ)) = (FreeGroup.of i * w, 0) := by
  have hz : (0 : ℤ) - -i = i := by ring
  unfold yFree
  rw [map_mul, map_mul]
  show act (xTwo ^ i) (act yTwo (act (xTwo ^ (-i)) (w, (0 : ℤ)))) = _
  rw [act_x_zpow (-i) (w, (0 : ℤ))]
  show act (xTwo ^ i) (act yTwo (w, (0 : ℤ) - -i)) = _
  rw [act_y]
  show act (xTwo ^ i) (FreeGroup.of ((0 : ℤ) - -i) * w, (0 : ℤ) - -i) = _
  rw [act_x_zpow i (FreeGroup.of ((0 : ℤ) - -i) * w, (0 : ℤ) - -i)]
  refine Prod.ext ?_ ?_
  · show FreeGroup.of ((0 : ℤ) - -i) * w = FreeGroup.of i * w
    rw [hz]
  · show (0 : ℤ) - -i - i = 0
    ring

/-- The words on which the ping-pong action is left multiplication. -/
def Good : Subgroup (FreeGroup ℤ) where
  carrier := {W : FreeGroup ℤ | ∀ w : FreeGroup ℤ,
    act (yFreeHom W) (w, (0 : ℤ)) = (W * w, 0)}
  one_mem' := by
    intro w
    rw [map_one, map_one, one_mul]
    rfl
  mul_mem' := by
    intro u v hu hv w
    rw [map_mul, map_mul]
    show act (yFreeHom u) (act (yFreeHom v) (w, (0 : ℤ))) = _
    rw [hv w, hu (v * w)]
    refine Prod.ext ?_ rfl
    show u * (v * w) = u * v * w
    group
  inv_mem' := by
    intro u hu w
    have hkey : act (yFreeHom u) (u⁻¹ * w, (0 : ℤ)) = (w, 0) := by
      rw [hu (u⁻¹ * w)]
      refine Prod.ext ?_ rfl
      show u * (u⁻¹ * w) = w
      group
    rw [map_inv, map_inv]
    have hinv : (act (yFreeHom u))⁻¹ (w, (0 : ℤ)) = (u⁻¹ * w, 0) := by
      apply (act (yFreeHom u)).injective
      simpa using hkey.symm
    show (act (yFreeHom u))⁻¹ (w, (0 : ℤ)) = _
    rw [hinv]

theorem good_eq_top : Good = ⊤ := by
  refine top_le_iff.mp ?_
  intro W _hW
  refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
  · exact Subgroup.one_mem _
  · intro i w
    rw [yFreeHom_of]
    exact act_yFree i w
  · intro i hmem
    exact Subgroup.inv_mem _ hmem
  · intro u v hu hv
    exact Subgroup.mul_mem _ hu hv

/-- **`lem:bridge` (1), first sentence, freeness half.**  "The elements `y_i`,
`i ∈ ℤ`, freely generate..." -/
theorem yFreeHom_injective : Function.Injective yFreeHom := by
  rw [injective_iff_map_eq_one]
  intro W hW
  have hgood : W ∈ Good := by
    rw [good_eq_top]
    exact Subgroup.mem_top W
  have h := hgood 1
  rw [hW, map_one] at h
  have hfst := congrArg Prod.fst h
  show W = 1
  rw [← mul_one W]
  exact hfst.symm

/-! ## 3.  The subgroup they generate is the normal closure of `y` -/

/-- `x` shifts the printed index: `x · y_i · x⁻¹ = y_{i+1}`. -/
theorem yFree_shiftUp (i : ℤ) : xTwo * yFree i * xTwo⁻¹ = yFree (i + 1) := by
  have h1 : xTwo ^ (i + 1) = xTwo * xTwo ^ i := by
    have hi : (i + 1 : ℤ) = 1 + i := by ring
    rw [hi, zpow_add, zpow_one]
  have h2 : xTwo ^ (-(i + 1)) = xTwo ^ (-i) * xTwo⁻¹ := by
    have hi : (-(i + 1) : ℤ) = -i + -1 := by ring
    rw [hi, zpow_add]
    congr 1
  unfold yFree
  rw [h1, h2]
  simp only [mul_assoc]

/-- `x⁻¹` shifts the printed index the other way. -/
theorem yFree_shiftDown (i : ℤ) : xTwo⁻¹ * yFree i * xTwo = yFree (i - 1) := by
  have h1 : xTwo ^ (i - 1) = xTwo⁻¹ * xTwo ^ i := by
    have hi : (i - 1 : ℤ) = -1 + i := by ring
    rw [hi, zpow_add]
    congr 1
  have h2 : xTwo ^ (-(i - 1)) = xTwo ^ (-i) * xTwo := by
    have hi : (-(i - 1) : ℤ) = -i + 1 := by ring
    rw [hi, zpow_add, zpow_one]
  unfold yFree
  rw [h1, h2]
  simp only [mul_assoc]

theorem yFree_mem_range (i : ℤ) : yFree i ∈ yFreeHom.range :=
  ⟨FreeGroup.of i, yFreeHom_of i⟩

theorem yTwo_mem_range : yTwo ∈ yFreeHom.range := by
  have h : yFree 0 = yTwo := by
    unfold yFree
    rw [neg_zero, zpow_zero, one_mul, mul_one]
  rw [← h]
  exact yFree_mem_range 0

theorem conj_xTwo_mem_range (W : FreeGroup ℤ) :
    xTwo * yFreeHom W * xTwo⁻¹ ∈ yFreeHom.range := by
  refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
  · rw [map_one, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro i
    rw [yFreeHom_of, yFree_shiftUp]
    exact yFree_mem_range (i + 1)
  · intro i hmem
    rw [map_inv]
    have hswap : xTwo * (yFreeHom (FreeGroup.of i))⁻¹ * xTwo⁻¹
        = (xTwo * yFreeHom (FreeGroup.of i) * xTwo⁻¹)⁻¹ := by group
    rw [hswap]
    exact Subgroup.inv_mem _ hmem
  · intro u v hu hv
    rw [map_mul]
    have hsplit : xTwo * (yFreeHom u * yFreeHom v) * xTwo⁻¹
        = (xTwo * yFreeHom u * xTwo⁻¹) * (xTwo * yFreeHom v * xTwo⁻¹) := by group
    rw [hsplit]
    exact Subgroup.mul_mem _ hu hv

theorem conj_xTwoInv_mem_range (W : FreeGroup ℤ) :
    xTwo⁻¹ * yFreeHom W * xTwo ∈ yFreeHom.range := by
  refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
  · rw [map_one, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro i
    rw [yFreeHom_of, yFree_shiftDown]
    exact yFree_mem_range (i - 1)
  · intro i hmem
    rw [map_inv]
    have hswap : xTwo⁻¹ * (yFreeHom (FreeGroup.of i))⁻¹ * xTwo
        = (xTwo⁻¹ * yFreeHom (FreeGroup.of i) * xTwo)⁻¹ := by group
    rw [hswap]
    exact Subgroup.inv_mem _ hmem
  · intro u v hu hv
    rw [map_mul]
    have hsplit : xTwo⁻¹ * (yFreeHom u * yFreeHom v) * xTwo
        = (xTwo⁻¹ * yFreeHom u * xTwo) * (xTwo⁻¹ * yFreeHom v * xTwo) := by group
    rw [hsplit]
    exact Subgroup.mul_mem _ hu hv

/-- The subgroup generated by the `y_i` is invariant under conjugation by every
element of `F(x,y)`: it is enough to check the two free generators, and `y`
itself lies in it. -/
theorem conj_mem_range_yFreeHom (g : FreeXY) :
    ∀ u ∈ yFreeHom.range, g * u * g⁻¹ ∈ yFreeHom.range := by
  refine FreeGroup.induction_on g ?_ ?_ ?_ ?_
  · intro u hu
    rw [one_mul, inv_one, mul_one]
    exact hu
  · intro i u hu
    have hi : FreeGroup.of i = xTwo ∨ FreeGroup.of i = yTwo := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    obtain ⟨W, rfl⟩ := hu
    rcases hi with h | h
    · rw [h]
      exact conj_xTwo_mem_range W
    · rw [h]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ yTwo_mem_range ⟨W, rfl⟩) (Subgroup.inv_mem _ yTwo_mem_range)
  · intro i _hi u hu
    obtain ⟨W, rfl⟩ := hu
    have hcase : FreeGroup.of i = xTwo ∨ FreeGroup.of i = yTwo := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hcase with h | h
    · rw [h]
      exact conj_xTwoInv_mem_range W
    · rw [h]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ yTwo_mem_range) ⟨W, rfl⟩) yTwo_mem_range
  · intro u v hu hv w hw
    have hsplit : u * v * w * (u * v)⁻¹ = u * (v * w * v⁻¹) * u⁻¹ := by group
    rw [hsplit]
    exact hu _ (hv w hw)

theorem range_yFreeHom_normal : (yFreeHom.range).Normal :=
  ⟨fun u hu g => conj_mem_range_yFreeHom g u hu⟩

/-- **`lem:bridge` (1), first sentence.**  "The elements `y_i`, `i ∈ ℤ`, freely
generate the normal closure of `y` in `F(x,y)`."  The manuscript cites
Lyndon--Schupp, Chapter I; the statement is proved here.

Freeness is `yFreeHom_injective`; this is the identification of the subgroup
they generate. -/
theorem range_yFreeHom_eq_normalClosure :
    yFreeHom.range = Subgroup.normalClosure ({yTwo} : Set FreeXY) := by
  haveI := range_yFreeHom_normal
  refine le_antisymm ?_ ?_
  · rintro _ ⟨W, rfl⟩
    refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro i
      have hy : yTwo ∈ Subgroup.normalClosure ({yTwo} : Set FreeXY) :=
        Subgroup.subset_normalClosure (Set.mem_singleton _)
      have hconj :=
        (Subgroup.normalClosure_normal (s := ({yTwo} : Set FreeXY))).conj_mem
          yTwo hy (xTwo ^ i)
      have hx : xTwo ^ i * yTwo * (xTwo ^ i)⁻¹ = yFree i := by
        unfold yFree
        rw [← zpow_neg]
      rw [hx] at hconj
      rw [yFreeHom_of]
      exact hconj
    · intro i hmem
      rw [map_inv]
      exact Subgroup.inv_mem _ hmem
    · intro u v hu hv
      rw [map_mul]
      exact Subgroup.mul_mem _ hu hv
  · exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr yTwo_mem_range)

end Bridge
end MFRecognition
end Manuscript
end GroupApproximation
