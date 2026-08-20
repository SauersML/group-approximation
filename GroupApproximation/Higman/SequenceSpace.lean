import GroupApproximation.Higman.ConjugateBasis
import GroupApproximation.Higman.BenignJoin
import Mathlib.Data.Finsupp.Order

/-!
# Higman's sequence space, and the first two of his operations

Higman codes a recursively enumerable set by a set of finitely supported
integer sequences.  This file sets up that dictionary and proves that the
family of sets it makes benign is closed under the two operations that need no
construction: intersection and union.

* `E = ℤ →₀ ℤ` --- the sequence space;
* `elt f = ∏ᵢ (of i) ^ f i` in `FreeGroup ℤ`, the product over the support in
  increasing order;
* `bElt f` --- its image under `of i ↦ bᵢ`, so `bElt f = ∏ᵢ bᵢ ^ f i` in
  `F₃ = ⟨a, b, c⟩`;
* `aElt f = a ^ (bElt f)` and `ASub B = ⟨aElt f : f ∈ B⟩`.

Three facts make the dictionary faithful, and all three are proved:

* `elt_injective` --- by abelianization: `FreeGroup ℤ → Multiplicative (ℤ →₀ ℤ)`
  sends `elt f` to `f`, so no ordering subtlety can intervene;
* `rowHom_injective` --- the row elements of `F₃` are a free basis, by
  retracting `F₃` onto `⟨b, c⟩` and quoting `Higman.Row.basisHom_injective`;
* `aElt_injective` --- by `Conj.cbHom_injective`.

Then `ASub_union` and `ASub_inter` identify the subgroup attached to a union
and to an intersection, and with `Benign.sup` and `Benign.inf` they give
Higman's operations `υ` and `ι`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj

/-- Higman's sequence space. -/
abbrev E : Type := ℤ →₀ ℤ

/-! ## 1.  Sequences as elements of a free group on `ℤ` -/

/-- The element of `FreeGroup ℤ` attached to a sequence. -/
noncomputable def elt (f : E) : FreeGroup ℤ :=
  ((f.support.sort (· ≤ ·)).map (fun i => FreeGroup.of i ^ f i)).prod

/-- The abelianization of `FreeGroup ℤ`, written on the sequence space. -/
noncomputable def ab : FreeGroup ℤ →* Multiplicative E :=
  FreeGroup.lift (fun i : ℤ => Multiplicative.ofAdd (Finsupp.single i (1 : ℤ)))

@[simp] theorem ab_of (i : ℤ) :
    ab (FreeGroup.of i) = Multiplicative.ofAdd (Finsupp.single i (1 : ℤ)) := by
  unfold ab
  rw [FreeGroup.lift.of]

/-- **The abelianization undoes the coding.** -/
theorem ab_elt (f : E) : ab (elt f) = Multiplicative.ofAdd f := by
  unfold elt
  rw [map_list_prod, List.map_map]
  have hstep : ∀ i : ℤ, (ab ∘ fun i : ℤ => FreeGroup.of i ^ f i) i
      = Multiplicative.ofAdd (Finsupp.single i (f i)) := by
    intro i
    show ab (FreeGroup.of i ^ f i) = _
    rw [map_zpow, ab_of, ← Multiplicative.ofAdd_zsmul]
    congr 1
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [List.map_congr_left (fun i _ => hstep i)]
  have hperm : ((f.support.sort (· ≤ ·)).map
      (fun i => Multiplicative.ofAdd (Finsupp.single i (f i)))).prod
      = ∏ i ∈ f.support, Multiplicative.ofAdd (Finsupp.single i (f i)) := by
    rw [Finset.prod_eq_multiset_prod]
    refine List.Perm.prod_eq ?_
    exact (Finset.sort_perm_toList _ _).map _
  rw [hperm]
  have hsum : ∏ i ∈ f.support, Multiplicative.ofAdd (Finsupp.single i (f i))
      = Multiplicative.ofAdd (∑ i ∈ f.support, Finsupp.single i (f i)) := by
    rw [Multiplicative.ofAdd_sum]
  rw [hsum]
  congr 1
  exact Finsupp.sum_single f

theorem elt_injective : Function.Injective elt := by
  intro f g hfg
  have h := congrArg ab hfg
  rw [ab_elt, ab_elt] at h
  exact Multiplicative.ofAdd.injective h

/-! ## 2.  The row elements of `F₃` -/

/-- The row elements, inside the rank-three free group. -/
def rowElt (i : ℤ) : F₃ := c ^ (-i) * b * c ^ i

theorem rowElt_mem_K (i : ℤ) : rowElt i ∈ K := by
  unfold rowElt
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ b_mem_K) ?_
  · exact Subgroup.zpow_mem _ c_mem_K _
  · exact Subgroup.zpow_mem _ c_mem_K _

/-- The retraction of `F₃` onto the rank-two free group, killing `a`. -/
def retract : F₃ →* Row.F₀ :=
  FreeGroup.lift (fun i : Fin 3 =>
    if i = 0 then 1 else if i = 1 then Row.b else Row.c)

@[simp] theorem retract_b : retract b = Row.b := by
  unfold retract b
  rw [FreeGroup.lift.of]
  simp

@[simp] theorem retract_c : retract c = Row.c := by
  unfold retract c
  rw [FreeGroup.lift.of]
  simp

theorem retract_rowElt (i : ℤ) : retract (rowElt i) = Row.row i := by
  unfold rowElt Row.row
  rw [map_mul, map_mul, map_zpow, map_zpow, retract_b, retract_c]

/-- The homomorphism carrying the free group on `ℤ` to the row elements. -/
def rowHom : FreeGroup ℤ →* F₃ := FreeGroup.lift rowElt

@[simp] theorem rowHom_of (i : ℤ) : rowHom (FreeGroup.of i) = rowElt i := by
  unfold rowHom
  rw [FreeGroup.lift.of]

theorem retract_comp_rowHom : retract.comp rowHom = Row.basisHom := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  show retract (rowHom (FreeGroup.of i)) = Row.basisHom (FreeGroup.of i)
  rw [rowHom_of, Row.basisHom_of, retract_rowElt]

/-- **The row elements of `F₃` are a free basis.** -/
theorem rowHom_injective : Function.Injective rowHom := by
  intro x y hxy
  have h : Row.basisHom x = Row.basisHom y := by
    have hx := congrArg (fun f : FreeGroup ℤ →* Row.F₀ => f x) retract_comp_rowHom
    have hy := congrArg (fun f : FreeGroup ℤ →* Row.F₀ => f y) retract_comp_rowHom
    calc Row.basisHom x = retract (rowHom x) := hx.symm
      _ = retract (rowHom y) := by rw [hxy]
      _ = Row.basisHom y := hy
  exact Row.basisHom_injective h

theorem rowHom_mem_K (x : FreeGroup ℤ) : rowHom x ∈ K := by
  refine FreeGroup.induction_on x ?_ ?_ ?_ ?_
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro i
    rw [rowHom_of]
    exact rowElt_mem_K i
  · intro i hmem
    rw [map_inv]
    exact Subgroup.inv_mem _ hmem
  · intro u v hu hv
    rw [map_mul]
    exact Subgroup.mul_mem _ hu hv

/-! ## 3.  The coding -/

/-- The element of `F₃` attached to a sequence. -/
noncomputable def bElt (f : E) : F₃ := rowHom (elt f)

theorem bElt_mem_K (f : E) : bElt f ∈ K := rowHom_mem_K _

theorem bElt_injective : Function.Injective bElt := by
  intro f g hfg
  exact elt_injective (rowHom_injective hfg)

/-- The conjugate attached to a sequence. -/
noncomputable def aElt (f : E) : F₃ := (bElt f)⁻¹ * a * bElt f

theorem aElt_eq_cbHom (f : E) :
    aElt f = Conj.cbHom (FreeGroup.of ⟨bElt f, bElt_mem_K f⟩) := by
  rw [Conj.cbHom_of]
  rfl

theorem aElt_injective : Function.Injective aElt := by
  intro f g hfg
  rw [aElt_eq_cbHom, aElt_eq_cbHom] at hfg
  have h := Conj.cbHom_injective hfg
  have h2 : (⟨bElt f, bElt_mem_K f⟩ : ↥K) = ⟨bElt g, bElt_mem_K g⟩ :=
    FreeGroup.of_injective h
  exact bElt_injective (congrArg Subtype.val h2)

/-- The subgroup attached to a set of sequences. -/
noncomputable def ASub (B : Set E) : Subgroup F₃ := Subgroup.closure (aElt '' B)

/-! ## 4.  Unions -/

/-- **The subgroup of a union is the join.** -/
theorem ASub_union (B B' : Set E) : ASub (B ∪ B') = ASub B ⊔ ASub B' := by
  unfold ASub
  rw [Set.image_union, Subgroup.closure_union]

/-- **Higman's operation `υ`.** -/
theorem benign_ASub_union {B B' : Set E} (h : Benign (ASub B))
    (h' : Benign (ASub B')) : Benign (ASub (B ∪ B')) := by
  rw [ASub_union]
  exact Benign.sup h h'

/-! ## 5.  Intersections -/

/-- Mapping a meet along an injective homomorphism. -/
theorem map_inf_of_injective {G H : Type} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) (A B : Subgroup G) :
    (A ⊓ B).map f = A.map f ⊓ B.map f := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, ⟨hxA, hxB⟩, rfl⟩
    exact ⟨⟨x, hxA, rfl⟩, ⟨x, hxB, rfl⟩⟩
  · rintro y ⟨⟨x, hxA, rfl⟩, ⟨z, hzB, hz⟩⟩
    have hzx : z = x := hf hz
    subst hzx
    exact ⟨z, ⟨hxA, hzB⟩, rfl⟩

/-- Killing the generators outside a set of indices. -/
noncomputable def killOutside (S : Set ↥K) : FreeGroup ↥K →* FreeGroup ↥K := by
  classical
  exact FreeGroup.lift (fun h => if h ∈ S then FreeGroup.of h else 1)

theorem killOutside_of_mem {S : Set ↥K} {h : ↥K} (hh : h ∈ S) :
    killOutside S (FreeGroup.of h) = FreeGroup.of h := by
  classical
  unfold killOutside
  rw [FreeGroup.lift.of]
  simp [hh]

theorem killOutside_of_notMem {S : Set ↥K} {h : ↥K} (hh : h ∉ S) :
    killOutside S (FreeGroup.of h) = 1 := by
  classical
  unfold killOutside
  rw [FreeGroup.lift.of]
  simp [hh]

theorem killOutside_fixes {S : Set ↥K} {w : FreeGroup ↥K}
    (hw : w ∈ Subgroup.closure (FreeGroup.of '' S)) : killOutside S w = w := by
  refine Subgroup.closure_induction (p := fun z _ => killOutside S z = z) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨h, hh, rfl⟩
    exact killOutside_of_mem hh
  · exact map_one _
  · intro x y _ _ hx hy
    rw [map_mul, hx, hy]
  · intro x _ hx
    rw [map_inv, hx]

theorem killOutside_lands {S T : Set ↥K} {w : FreeGroup ↥K}
    (hw : w ∈ Subgroup.closure (FreeGroup.of '' T)) :
    killOutside S w ∈ Subgroup.closure (FreeGroup.of '' (S ∩ T)) := by
  classical
  refine Subgroup.closure_induction
    (p := fun z _ => killOutside S z ∈ Subgroup.closure (FreeGroup.of '' (S ∩ T)))
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨h, hh, rfl⟩
    by_cases hS : h ∈ S
    · rw [killOutside_of_mem hS]
      exact Subgroup.subset_closure ⟨h, ⟨hS, hh⟩, rfl⟩
    · rw [killOutside_of_notMem hS]
      exact Subgroup.one_mem _
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

/-- **Coordinate subgroups of a free group meet as their index sets do.** -/
theorem closure_inter_le (S T : Set ↥K) :
    Subgroup.closure (FreeGroup.of '' S) ⊓ Subgroup.closure (FreeGroup.of '' T)
      ≤ Subgroup.closure (FreeGroup.of '' (S ∩ T)) := by
  rintro w ⟨hwS, hwT⟩
  have hfix := killOutside_fixes (S := S) hwS
  have hland := killOutside_lands (S := S) hwT
  rw [hfix] at hland
  exact hland

/-! ## 6.  The subgroup of an intersection -/

/-- The index of a sequence, inside the conjugating subgroup. -/
noncomputable def bK (f : E) : ↥K := ⟨bElt f, bElt_mem_K f⟩

theorem bK_injective : Function.Injective bK := by
  intro f g hfg
  exact bElt_injective (congrArg Subtype.val hfg)

theorem aElt_eq (f : E) : aElt f = Conj.cbHom (FreeGroup.of (bK f)) :=
  aElt_eq_cbHom f

theorem ASub_eq_map (B : Set E) :
    ASub B = (Subgroup.closure (FreeGroup.of '' (bK '' B))).map Conj.cbHom := by
  unfold ASub
  rw [MonoidHom.map_closure]
  congr 1
  refine Set.ext fun x => ?_
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨FreeGroup.of (bK f), ⟨bK f, ⟨f, hf, rfl⟩, rfl⟩, (aElt_eq f).symm⟩
  · rintro ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩
    exact ⟨f, hf, (aElt_eq f).symm⟩

/-- **The subgroup of an intersection is the meet.** -/
theorem ASub_inter (B B' : Set E) : ASub (B ∩ B') = ASub B ⊓ ASub B' := by
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · unfold ASub
      refine Subgroup.closure_mono ?_
      exact Set.image_mono Set.inter_subset_left
    · unfold ASub
      refine Subgroup.closure_mono ?_
      exact Set.image_mono Set.inter_subset_right
  · rw [ASub_eq_map, ASub_eq_map, ASub_eq_map,
      ← map_inf_of_injective Conj.cbHom_injective]
    refine Subgroup.map_mono ?_
    have himg : FreeGroup.of '' (bK '' (B ∩ B'))
        = (FreeGroup.of '' (bK '' B)) ∩ (FreeGroup.of '' (bK '' B')) := by
      rw [Set.image_inter bK_injective, Set.image_inter FreeGroup.of_injective]
    rw [himg]
    exact closure_inter_le _ _

/-- **Higman's operation `ι`.** -/
theorem benign_ASub_inter {B B' : Set E} (h : Benign (ASub B))
    (h' : Benign (ASub B')) : Benign (ASub (B ∩ B')) := by
  rw [ASub_inter]
  exact Benign.inf h h'

end Seq
end Higman
end GroupApproximation
