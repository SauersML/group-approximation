import GroupApproximation.GGT.VanKampen.PermOrbitTransport

/-!
# Orbits of a sum of two permutations

`Equiv.sumCongr a b` acts on `α ⊕ β` by `a` on the left summand and `b` on the
right one, so it never moves a left element to a right one.  Its orbits are
then the orbits of `a` together with the orbits of `b`.

This is the second half of the face description for a reclosed map, whose face
permutation is an equivalence conjugating such a sum: one summand is the old
face rotation restricted to the darts outside the replaced region, the other is
the cyclic successor on the region's boundary darts.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u

/-! ## Powers of a sum -/

/-- A power of a sum of permutations is the sum of the powers. -/
theorem sumCongr_zpow {α β : Type u} (a : Equiv.Perm α) (b : Equiv.Perm β)
    (i : ℤ) :
    (Equiv.sumCongr a b) ^ i = Equiv.sumCongr (a ^ i) (b ^ i) := by
  have hprod : ((a, b) : Equiv.Perm α × Equiv.Perm β) ^ i = (a ^ i, b ^ i) := rfl
  have hmap := map_zpow (Equiv.Perm.sumCongrHom α β) (a, b) i
  rw [hprod] at hmap
  rw [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongrHom_apply] at hmap
  exact hmap.symm

/-! ## The same-cycle relation on a sum -/

/-- Two left elements are in the same cycle of the sum exactly when they are in
the same cycle of the left permutation. -/
theorem sameCycle_sumCongr_inl {α β : Type u} (a : Equiv.Perm α)
    (b : Equiv.Perm β) (x y : α) :
    Equiv.Perm.SameCycle a x y ↔
      Equiv.Perm.SameCycle (Equiv.sumCongr a b) (Sum.inl x) (Sum.inl y) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [sumCongr_zpow, Equiv.sumCongr_apply, Sum.map_inl, hi]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [sumCongr_zpow, Equiv.sumCongr_apply, Sum.map_inl] at hi
    exact Sum.inl_injective hi

/-- Two right elements are in the same cycle of the sum exactly when they are
in the same cycle of the right permutation. -/
theorem sameCycle_sumCongr_inr {α β : Type u} (a : Equiv.Perm α)
    (b : Equiv.Perm β) (x y : β) :
    Equiv.Perm.SameCycle b x y ↔
      Equiv.Perm.SameCycle (Equiv.sumCongr a b) (Sum.inr x) (Sum.inr y) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [sumCongr_zpow, Equiv.sumCongr_apply, Sum.map_inr, hi]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [sumCongr_zpow, Equiv.sumCongr_apply, Sum.map_inr] at hi
    exact Sum.inr_injective hi

/-- A left element and a right element are never in the same cycle of the
sum. -/
theorem not_sameCycle_sumCongr_inl_inr {α β : Type u} (a : Equiv.Perm α)
    (b : Equiv.Perm β) (x : α) (y : β) :
    ¬ Equiv.Perm.SameCycle (Equiv.sumCongr a b) (Sum.inl x) (Sum.inr y) := by
  rintro ⟨i, hi⟩
  rw [sumCongr_zpow, Equiv.sumCongr_apply, Sum.map_inl] at hi
  exact Sum.inl_ne_inr hi

/-- A right element and a left element are never in the same cycle of the
sum. -/
theorem not_sameCycle_sumCongr_inr_inl {α β : Type u} (a : Equiv.Perm α)
    (b : Equiv.Perm β) (x : β) (y : α) :
    ¬ Equiv.Perm.SameCycle (Equiv.sumCongr a b) (Sum.inr x) (Sum.inl y) := by
  intro h
  exact not_sameCycle_sumCongr_inl_inr a b y x h.symm

/-! ## The orbit decomposition -/

private noncomputable def orbitSumToFun {α β : Type u} (a : Equiv.Perm α)
    (b : Equiv.Perm β) :
    CombMap.Orbit (Equiv.sumCongr a b) →
      CombMap.Orbit a ⊕ CombMap.Orbit b := by
  refine Quotient.lift
    (fun z : α ⊕ β =>
      match z with
      | Sum.inl x => Sum.inl (Quotient.mk'' x)
      | Sum.inr y => Sum.inr (Quotient.mk'' y)) ?_
  intro z w hzw
  match z, w with
  | Sum.inl x, Sum.inl y =>
      have hxy : Equiv.Perm.SameCycle a x y :=
        (sameCycle_sumCongr_inl a b x y).2 hzw
      exact congrArg Sum.inl (Quotient.sound hxy)
  | Sum.inl x, Sum.inr y =>
      exact absurd hzw (not_sameCycle_sumCongr_inl_inr a b x y)
  | Sum.inr x, Sum.inl y =>
      exact absurd hzw (not_sameCycle_sumCongr_inr_inl a b x y)
  | Sum.inr x, Sum.inr y =>
      have hxy : Equiv.Perm.SameCycle b x y :=
        (sameCycle_sumCongr_inr a b x y).2 hzw
      exact congrArg Sum.inr (Quotient.sound hxy)

private noncomputable def orbitSumInvFun {α β : Type u} (a : Equiv.Perm α)
    (b : Equiv.Perm β) :
    CombMap.Orbit a ⊕ CombMap.Orbit b →
      CombMap.Orbit (Equiv.sumCongr a b) :=
  Sum.elim
    (Quotient.map Sum.inl
      (fun x y hxy => (sameCycle_sumCongr_inl a b x y).1 hxy))
    (Quotient.map Sum.inr
      (fun x y hxy => (sameCycle_sumCongr_inr a b x y).1 hxy))

/-- The orbits of a sum of two permutations are the orbits of the two
summands. -/
noncomputable def orbitSumCongr {α β : Type u} (a : Equiv.Perm α)
    (b : Equiv.Perm β) :
    CombMap.Orbit (Equiv.sumCongr a b) ≃
      CombMap.Orbit a ⊕ CombMap.Orbit b where
  toFun := orbitSumToFun a b
  invFun := orbitSumInvFun a b
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    match z with
    | Sum.inl x => rfl
    | Sum.inr y => rfl
  right_inv := by
    intro s
    match s with
    | Sum.inl p =>
        refine Quotient.inductionOn p ?_
        intro x
        rfl
    | Sum.inr p =>
        refine Quotient.inductionOn p ?_
        intro y
        rfl

end VanKampen
end GGT
end GroupApproximation
