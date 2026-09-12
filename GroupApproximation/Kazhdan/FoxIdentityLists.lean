import GroupApproximation.Kazhdan.FoxMagnusKernel
import GroupApproximation.Meta.AxiomGuard

/-!
# Identity lists of a presentation

A factor `(u, r, ε)` stands for the conjugate `u · r^ε · u⁻¹` of a relator.  A list of
factors has a value in the free group (`listValue`) and a chain in `ℤG^ρ` (`listChain`):
the positive factor `(u, r, true)` contributes the basis vector `(r, ū)`, the negative one
its negative.  The pushed Fox derivative of the value is the Fox boundary of the chain
(`mapG_foxFree_listValue`).

Every normal-closure element is the value of a list (`exists_list_of_mem_normalClosure`),
every vector of `ℤG^ρ` is the chain of a list (`exists_list_chain`), and every element of
the commutator subgroup of the normal closure is the value of a list with zero chain
(`exists_list_zero_chain_of_mem_commutator`).  With the embedding of the relation module
(`Kazhdan/FoxMagnusKernel.lean`) this gives the identity lists of the kernel of `∂₂`:
every `z` with `∂₂ z = 0` is the chain of a list whose value is `1`
(`exists_identity_list_of_foxD₂_eq_zero`).
-/

namespace GroupApproximation.FoxComplex

open FreeResolutionPrimeOrder FoxBoundary PresentedGroupRelatorReplay
open scoped commutatorElement

universe v w

/-- A factor `(u, r, ε)`: the conjugate `u · r^ε · u⁻¹` of the relator `r`. -/
abbrev IdentityFactor (X : Type v) (ρ : Type w) : Type (max v w) := FreeGroup X × ρ × Bool

variable {X : Type v} {ρ : Type w} (rel : ρ → SignedWord X)

/-- The value of a factor in the free group. -/
def factorValue (a : IdentityFactor X ρ) : FreeGroup X :=
  if a.2.2 then a.1 * word (rel a.2.1) * a.1⁻¹ else a.1 * (word (rel a.2.1))⁻¹ * a.1⁻¹

/-- The value of a list of factors. -/
def listValue (L : List (IdentityFactor X ρ)) : FreeGroup X :=
  (L.map (factorValue rel)).prod

/-- The chain of a factor: `± (r, ū)`. -/
noncomputable def factorChain (a : IdentityFactor X ρ) : FreeZG (Presented rel) ρ :=
  if a.2.2 then Finsupp.single (a.2.1, PresentedGroup.mk (relSet rel) a.1) 1
  else -Finsupp.single (a.2.1, PresentedGroup.mk (relSet rel) a.1) 1

/-- The chain of a list of factors. -/
noncomputable def listChain (L : List (IdentityFactor X ρ)) : FreeZG (Presented rel) ρ :=
  (L.map (factorChain rel)).sum

/-- Reversing the sign of a factor. -/
def flipFactor (a : IdentityFactor X ρ) : IdentityFactor X ρ := (a.1, a.2.1, !a.2.2)

/-- The inverse list. -/
def invList (L : List (IdentityFactor X ρ)) : List (IdentityFactor X ρ) :=
  L.reverse.map flipFactor

theorem invList_cons (a : IdentityFactor X ρ) (L : List (IdentityFactor X ρ)) :
    invList (a :: L) = invList L ++ [flipFactor a] := by
  rw [invList, invList, List.reverse_cons, List.map_append]
  rfl

theorem factorValue_true (u : FreeGroup X) (r : ρ) :
    factorValue rel (u, r, true) = u * word (rel r) * u⁻¹ := if_pos rfl

theorem factorValue_false (u : FreeGroup X) (r : ρ) :
    factorValue rel (u, r, false) = u * (word (rel r))⁻¹ * u⁻¹ := if_neg Bool.false_ne_true

theorem factorChain_true (u : FreeGroup X) (r : ρ) :
    factorChain rel (u, r, true) = Finsupp.single (r, PresentedGroup.mk (relSet rel) u) 1 :=
  if_pos rfl

theorem factorChain_false (u : FreeGroup X) (r : ρ) :
    factorChain rel (u, r, false) = -Finsupp.single (r, PresentedGroup.mk (relSet rel) u) 1 :=
  if_neg Bool.false_ne_true

theorem factorValue_flip (a : IdentityFactor X ρ) :
    factorValue rel (flipFactor a) = (factorValue rel a)⁻¹ := by
  rcases a with ⟨u, r, _ | _⟩
  · show factorValue rel (u, r, true) = (factorValue rel (u, r, false))⁻¹
    rw [factorValue_true, factorValue_false]
    group
  · show factorValue rel (u, r, false) = (factorValue rel (u, r, true))⁻¹
    rw [factorValue_true, factorValue_false]
    group

theorem factorChain_flip (a : IdentityFactor X ρ) :
    factorChain rel (flipFactor a) = -factorChain rel a := by
  rcases a with ⟨u, r, _ | _⟩
  · show factorChain rel (u, r, true) = -factorChain rel (u, r, false)
    rw [factorChain_true, factorChain_false, neg_neg]
  · show factorChain rel (u, r, false) = -factorChain rel (u, r, true)
    rw [factorChain_true, factorChain_false]

theorem listValue_nil : listValue rel ([] : List (IdentityFactor X ρ)) = 1 := rfl

theorem listValue_cons (a : IdentityFactor X ρ) (L : List (IdentityFactor X ρ)) :
    listValue rel (a :: L) = factorValue rel a * listValue rel L := by
  rw [listValue, listValue, List.map_cons, List.prod_cons]

theorem listValue_singleton (a : IdentityFactor X ρ) : listValue rel [a] = factorValue rel a := by
  rw [listValue_cons, listValue_nil, mul_one]

theorem listValue_append (L₁ L₂ : List (IdentityFactor X ρ)) :
    listValue rel (L₁ ++ L₂) = listValue rel L₁ * listValue rel L₂ := by
  rw [listValue, listValue, listValue, List.map_append, List.prod_append]

theorem listChain_nil : listChain rel ([] : List (IdentityFactor X ρ)) = 0 := rfl

theorem listChain_cons (a : IdentityFactor X ρ) (L : List (IdentityFactor X ρ)) :
    listChain rel (a :: L) = factorChain rel a + listChain rel L := by
  rw [listChain, listChain, List.map_cons, List.sum_cons]

theorem listChain_singleton (a : IdentityFactor X ρ) : listChain rel [a] = factorChain rel a := by
  rw [listChain_cons, listChain_nil, add_zero]

theorem listChain_append (L₁ L₂ : List (IdentityFactor X ρ)) :
    listChain rel (L₁ ++ L₂) = listChain rel L₁ + listChain rel L₂ := by
  rw [listChain, listChain, listChain, List.map_append, List.sum_append]

theorem listValue_invList (L : List (IdentityFactor X ρ)) :
    listValue rel (invList L) = (listValue rel L)⁻¹ := by
  induction L with
  | nil => rw [invList, List.reverse_nil, List.map_nil, listValue_nil, inv_one]
  | cons a L ih =>
      rw [invList_cons, listValue_append, ih, listValue_singleton, factorValue_flip,
        listValue_cons, mul_inv_rev]

theorem listChain_invList (L : List (IdentityFactor X ρ)) :
    listChain rel (invList L) = -listChain rel L := by
  induction L with
  | nil => rw [invList, List.reverse_nil, List.map_nil, listChain_nil, neg_zero]
  | cons a L ih =>
      rw [invList_cons, listChain_append, ih, listChain_singleton, factorChain_flip,
        listChain_cons, neg_add_rev]

/-! ### Values lie in the normal closure, and push forward to chains -/

theorem mk_factorValue (a : IdentityFactor X ρ) :
    PresentedGroup.mk (relSet rel) (factorValue rel a) = 1 := by
  rcases a with ⟨u, r, _ | _⟩
  · rw [factorValue_false, map_mul, map_mul, map_inv, map_inv, mk_rel, inv_one, mul_one,
      mul_inv_cancel]
  · rw [factorValue_true, map_mul, map_mul, map_inv, mk_rel, mul_one, mul_inv_cancel]

theorem listValue_mem (L : List (IdentityFactor X ρ)) :
    listValue rel L ∈ Subgroup.normalClosure (relSet rel) := by
  induction L with
  | nil => exact one_mem _
  | cons a L ih =>
      rw [listValue_cons]
      exact mul_mem (mem_normalClosure_of_mk_eq_one rel (mk_factorValue rel a)) ih

theorem mapG_foxFree_factorValue (a : IdentityFactor X ρ) :
    mapG (PresentedGroup.mk (relSet rel)) (foxFree 1 (factorValue rel a)) =
      foxD₂ (PresentedGroup.of : X → Presented rel) rel (factorChain rel a) := by
  rcases a with ⟨u, r, _ | _⟩
  · have hconj : factorValue rel (u, r, false) = (u * word (rel r) * u⁻¹)⁻¹ := by
      rw [factorValue_false]
      group
    rw [hconj, foxFree_inv, map_neg, mapG_act, map_inv, map_mul, map_mul, map_inv, mk_rel,
      mul_one, mul_inv_cancel, inv_one, act_one, mapG_foxFree_conj, factorChain_false, map_neg,
      foxD₂_single, one_zsmul]
  · rw [factorValue_true, mapG_foxFree_conj, factorChain_true, foxD₂_single, one_zsmul]

/-- **The pushed Fox derivative of a list value is the Fox boundary of its chain.** -/
theorem mapG_foxFree_listValue (L : List (IdentityFactor X ρ)) :
    mapG (PresentedGroup.mk (relSet rel)) (foxFree 1 (listValue rel L)) =
      foxD₂ (PresentedGroup.of : X → Presented rel) rel (listChain rel L) := by
  induction L with
  | nil => rw [listValue_nil, foxFree_one, map_zero, listChain_nil, map_zero]
  | cons a L ih =>
      rw [listValue_cons, foxFree_mul, map_add, mapG_act, mk_factorValue, act_one, ih,
        mapG_foxFree_factorValue, listChain_cons, map_add]

/-! ### Supply of lists -/

/-- Every normal-closure element is the value of a list. -/
theorem exists_list_of_mem_normalClosure {n : FreeGroup X}
    (hn : n ∈ Subgroup.normalClosure (relSet rel)) : ∃ L, listValue rel L = n := by
  have hn' : n ∈ Subgroup.closure (Group.conjugatesOfSet (relSet rel)) := hn
  clear hn
  induction hn' using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨a, ⟨r, rfl⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
      exact ⟨[(c, r, true)], by rw [listValue_singleton, factorValue_true]⟩
  | one => exact ⟨[], rfl⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨A, hA⟩ := ihx
      obtain ⟨B, hB⟩ := ihy
      exact ⟨A ++ B, by rw [listValue_append, hA, hB]⟩
  | inv x _ ihx =>
      obtain ⟨A, hA⟩ := ihx
      exact ⟨invList A, by rw [listValue_invList, hA]⟩

/-- The chains of lists form an additive subgroup. -/
noncomputable def chainSubgroup : AddSubgroup (FreeZG (Presented rel) ρ) where
  carrier := {z | ∃ L, listChain rel L = z}
  add_mem' := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨A ++ B, listChain_append rel A B⟩
  zero_mem' := ⟨[], rfl⟩
  neg_mem' := by
    rintro _ ⟨A, rfl⟩
    exact ⟨invList A, listChain_invList rel A⟩

/-- Every vector of `ℤG^ρ` is the chain of a list. -/
theorem exists_list_chain (z : FreeZG (Presented rel) ρ) : ∃ L, listChain rel L = z := by
  have hgen : ∀ q : ρ × Presented rel, Finsupp.single q (1 : ℤ) ∈ chainSubgroup rel := by
    rintro ⟨r, g⟩
    obtain ⟨u, rfl⟩ := PresentedGroup.mk_surjective (relSet rel) g
    exact ⟨[(u, r, true)], by rw [listChain_singleton, factorChain_true]⟩
  have hall : z ∈ chainSubgroup rel := by
    refine Finsupp.induction_linear z (zero_mem _) (fun f f' hf hf' ↦ add_mem hf hf') ?_
    intro q c
    rw [← Finsupp.smul_single_one]
    exact zsmul_mem (hgen q) c
  exact hall

/-- Every element of the commutator subgroup of the normal closure is the value of a list
with zero chain. -/
theorem exists_list_zero_chain_of_mem_commutator {x : Subgroup.normalClosure (relSet rel)}
    (hx : x ∈ commutator (Subgroup.normalClosure (relSet rel))) :
    ∃ L, listValue rel L = x.1 ∧ listChain rel L = 0 := by
  have hx' : x ∈ Subgroup.closure {g : Subgroup.normalClosure (relSet rel) |
      ∃ g₁ ∈ (⊤ : Subgroup (Subgroup.normalClosure (relSet rel))),
        ∃ g₂ ∈ (⊤ : Subgroup (Subgroup.normalClosure (relSet rel))), ⁅g₁, g₂⁆ = g} := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨a, -, b, -, rfl⟩ := hy
      obtain ⟨A, hA⟩ := exists_list_of_mem_normalClosure rel a.2
      obtain ⟨B, hB⟩ := exists_list_of_mem_normalClosure rel b.2
      refine ⟨A ++ B ++ invList A ++ invList B, ?_, ?_⟩
      · rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, Subgroup.coe_inv, listValue_append, listValue_append,
          listValue_append, listValue_invList, listValue_invList, hA, hB]
      · rw [listChain_append, listChain_append, listChain_append, listChain_invList,
          listChain_invList]
        abel
  | one => exact ⟨[], rfl, rfl⟩
  | mul y y' _ _ ihy ihy' =>
      obtain ⟨A, hA, hA0⟩ := ihy
      obtain ⟨B, hB, hB0⟩ := ihy'
      exact ⟨A ++ B, by rw [Subgroup.coe_mul, listValue_append, hA, hB],
        by rw [listChain_append, hA0, hB0, add_zero]⟩
  | inv y _ ihy =>
      obtain ⟨A, hA, hA0⟩ := ihy
      exact ⟨invList A, by rw [Subgroup.coe_inv, listValue_invList, hA],
        by rw [listChain_invList, hA0, neg_zero]⟩

/-- **Identity lists of the kernel of `∂₂`**: every `z` with `∂₂ z = 0` is the chain of a
list whose value is `1`. -/
theorem exists_identity_list_of_foxD₂_eq_zero (z : FreeZG (Presented rel) ρ)
    (hz : foxD₂ (PresentedGroup.of : X → Presented rel) rel z = 0) :
    ∃ L, listValue rel L = 1 ∧ listChain rel L = z := by
  obtain ⟨L, hL⟩ := exists_list_chain rel z
  have hmem := listValue_mem rel L
  have h0 : mapG (PresentedGroup.mk (relSet rel)) (foxFree 1 (listValue rel L)) = 0 := by
    rw [mapG_foxFree_listValue, hL, hz]
  obtain ⟨L', hL', hL'0⟩ := exists_list_zero_chain_of_mem_commutator rel
    (mem_commutator_of_mapG_foxFree_eq_zero rel hmem h0)
  have hL'v : listValue rel L' = listValue rel L := hL'
  refine ⟨L ++ invList L', ?_, ?_⟩
  · rw [listValue_append, listValue_invList, hL'v, mul_inv_cancel]
  · rw [listChain_append, listChain_invList, hL'0, neg_zero, add_zero, hL]

end GroupApproximation.FoxComplex

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.FoxComplex.listValue_invList
#audit_axioms GroupApproximation.FoxComplex.listChain_invList
#audit_axioms GroupApproximation.FoxComplex.mapG_foxFree_listValue
#audit_axioms GroupApproximation.FoxComplex.exists_list_of_mem_normalClosure
#audit_axioms GroupApproximation.FoxComplex.exists_list_chain
#audit_axioms GroupApproximation.FoxComplex.exists_list_zero_chain_of_mem_commutator
#audit_axioms GroupApproximation.FoxComplex.exists_identity_list_of_foxD₂_eq_zero
