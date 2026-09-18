import Mathlib.GroupTheory.PushoutI
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# A pushout obstruction for amalgam statements (generic group theory)

Lane `bh-met-91r`, helper module.  Fix subgroups `A, P, G ≤ E`.  Let `Q` be the Mathlib pushout
`A *_{A ⊓ P} P` (`Monoid.PushoutI` of the two inclusions of `A ⊓ P`).

Main result (`k2PolyAmal_no_extension`).  Suppose `a ∈ A \ P`, `g ∈ P \ A`, `s ∈ P` and
`a g a⁻¹ = s`, with `a, g, s ∈ G`.  Then no homomorphism `Φ : G → Q` restricts to the two
canonical maps `A → Q` and `P → Q`.

Truth check (paper).  `s ∉ A`, since otherwise `g = a⁻¹ s a ∈ A`.  So `a · g · a⁻¹ · s⁻¹` is
a reduced word of length 4 in `A *_{A ⊓ P} P`: its letters alternate between the factors, and
none of them lies in `A ⊓ P`.  By Mathlib's normal form theorem
(`Monoid.PushoutI.Reduced.eq_empty_of_mem_range`) its product is not `1`.  But if `Φ` existed,
that product would be `Φ (a g a⁻¹ s⁻¹) = Φ 1 = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section PushoutObstruction

variable {E : Type} [Group E]

/-- The two factors: `true ↦ A`, `false ↦ P`. -/
def k2PolyAmal_fam (A P : Subgroup E) (b : Bool) : Subgroup E :=
  cond b A P

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_fam

/-- `A ⊓ P` lies in both factors. -/
theorem k2PolyAmal_inf_le_fam (A P : Subgroup E) : ∀ b, A ⊓ P ≤ k2PolyAmal_fam A P b
  | true => show A ⊓ P ≤ A from inf_le_left
  | false => show A ⊓ P ≤ P from inf_le_right

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_inf_le_fam

/-- The two inclusions of `A ⊓ P`. -/
def k2PolyAmal_incl (A P : Subgroup E) (b : Bool) :
    ↥(A ⊓ P) →* ↥(k2PolyAmal_fam A P b) :=
  Subgroup.inclusion (k2PolyAmal_inf_le_fam A P b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_incl

theorem k2PolyAmal_incl_injective (A P : Subgroup E) :
    ∀ b, Function.Injective (k2PolyAmal_incl A P b) :=
  fun b => Subgroup.inclusion_injective (k2PolyAmal_inf_le_fam A P b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_incl_injective

/-- The two canonical maps into the pushout agree on `A ⊓ P`. -/
theorem k2PolyAmal_compat (A P : Subgroup E) (z : E) (h₁ : z ∈ A) (h₂ : z ∈ P) :
    Monoid.PushoutI.of (φ := k2PolyAmal_incl A P) true ⟨z, h₁⟩ =
      Monoid.PushoutI.of (φ := k2PolyAmal_incl A P) false ⟨z, h₂⟩ := by
  have hz : z ∈ A ⊓ P := Subgroup.mem_inf.mpr ⟨h₁, h₂⟩
  have i₁ : k2PolyAmal_incl A P true ⟨z, hz⟩ = ⟨z, h₁⟩ :=
    Subtype.ext (Subgroup.coe_inclusion _ _)
  have i₂ : k2PolyAmal_incl A P false ⟨z, hz⟩ = ⟨z, h₂⟩ :=
    Subtype.ext (Subgroup.coe_inclusion _ _)
  exact (congrArg (Monoid.PushoutI.of (φ := k2PolyAmal_incl A P) true) i₁).symm.trans
    ((Monoid.PushoutI.of_apply_eq_base (k2PolyAmal_incl A P) true ⟨z, hz⟩).trans
      ((Monoid.PushoutI.of_apply_eq_base (k2PolyAmal_incl A P) false ⟨z, hz⟩).symm.trans
        (congrArg (Monoid.PushoutI.of (φ := k2PolyAmal_incl A P) false) i₂)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_compat

/-- An element of `S` outside a subgroup `T` is not `1`. -/
theorem k2PolyAmal_mk_ne_one {S T : Subgroup E} {y : E} (hy : y ∈ S) (hT : y ∉ T) :
    (⟨y, hy⟩ : ↥S) ≠ 1 := fun e =>
  hT (by rw [show y = 1 from congrArg Subtype.val e]; exact T.one_mem)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_mk_ne_one

/-- An element of a factor outside `A ⊓ P` is not in the image of the base. -/
theorem k2PolyAmal_not_mem_range (A P : Subgroup E) (b : Bool) (y : ↥(k2PolyAmal_fam A P b))
    (hy : (y : E) ∉ A ⊓ P) : y ∉ (k2PolyAmal_incl A P b).range := by
  rintro ⟨c, hc⟩
  apply hy
  rw [← hc]
  unfold k2PolyAmal_incl
  rw [Subgroup.coe_inclusion]
  exact c.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_not_mem_range

/-- The word `a · g · a⁻¹ · s⁻¹` in `A * P` (factor `true` is `A`, factor `false` is `P`). -/
def k2PolyAmal_word (A P : Subgroup E) {a g s : E} (ha : a ∈ A) (haP : a ∉ P) (hg : g ∈ P)
    (hgA : g ∉ A) (hs : s ∈ P) (hsA : s ∉ A) :
    Monoid.CoprodI.Word (fun b => ↥(k2PolyAmal_fam A P b)) where
  toList := [⟨true, ⟨a, ha⟩⟩, ⟨false, ⟨g, hg⟩⟩, ⟨true, ⟨a⁻¹, A.inv_mem ha⟩⟩,
    ⟨false, ⟨s⁻¹, P.inv_mem hs⟩⟩]
  ne_one := by
    intro l hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact k2PolyAmal_mk_ne_one (S := k2PolyAmal_fam A P true) (T := P) (y := a) ha haP
    · exact k2PolyAmal_mk_ne_one (S := k2PolyAmal_fam A P false) (T := A) (y := g) hg hgA
    · exact k2PolyAmal_mk_ne_one (S := k2PolyAmal_fam A P true) (T := P) (y := a⁻¹)
        (A.inv_mem ha) (fun h => haP (inv_mem_iff.mp h))
    · exact k2PolyAmal_mk_ne_one (S := k2PolyAmal_fam A P false) (T := A) (y := s⁻¹)
        (P.inv_mem hs) (fun h => hsA (inv_mem_iff.mp h))
  chain_ne := List.IsChain.cons_cons (by simp) (List.IsChain.cons_cons (by simp)
    (List.IsChain.cons_cons (by simp) (List.IsChain.singleton _)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_word

theorem k2PolyAmal_word_toList (A P : Subgroup E) {a g s : E} (ha : a ∈ A) (haP : a ∉ P)
    (hg : g ∈ P) (hgA : g ∉ A) (hs : s ∈ P) (hsA : s ∉ A) :
    (k2PolyAmal_word A P ha haP hg hgA hs hsA).toList =
      [⟨true, ⟨a, ha⟩⟩, ⟨false, ⟨g, hg⟩⟩, ⟨true, ⟨a⁻¹, A.inv_mem ha⟩⟩,
        ⟨false, ⟨s⁻¹, P.inv_mem hs⟩⟩] :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_word_toList

/-- No letter of the word lies in `A ⊓ P`. -/
theorem k2PolyAmal_word_reduced (A P : Subgroup E) {a g s : E} (ha : a ∈ A) (haP : a ∉ P)
    (hg : g ∈ P) (hgA : g ∉ A) (hs : s ∈ P) (hsA : s ∉ A) :
    Monoid.PushoutI.Reduced (k2PolyAmal_incl A P) (k2PolyAmal_word A P ha haP hg hgA hs hsA) := by
  intro l hl
  rw [k2PolyAmal_word_toList] at hl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact k2PolyAmal_not_mem_range A P true ⟨a, ha⟩
      (fun h => haP (Subgroup.mem_inf.mp h).2)
  · exact k2PolyAmal_not_mem_range A P false ⟨g, hg⟩
      (fun h => hgA (Subgroup.mem_inf.mp h).1)
  · exact k2PolyAmal_not_mem_range A P true ⟨a⁻¹, A.inv_mem ha⟩
      (fun h => haP (inv_mem_iff.mp (show a⁻¹ ∈ P from (Subgroup.mem_inf.mp h).2)))
  · exact k2PolyAmal_not_mem_range A P false ⟨s⁻¹, P.inv_mem hs⟩
      (fun h => hsA (inv_mem_iff.mp (show s⁻¹ ∈ A from (Subgroup.mem_inf.mp h).1)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_word_reduced

/-- The product of the word in the pushout. -/
theorem k2PolyAmal_word_prod (A P : Subgroup E) {a g s : E} (ha : a ∈ A) (haP : a ∉ P)
    (hg : g ∈ P) (hgA : g ∉ A) (hs : s ∈ P) (hsA : s ∉ A) :
    Monoid.PushoutI.ofCoprodI (φ := k2PolyAmal_incl A P)
        (k2PolyAmal_word A P ha haP hg hgA hs hsA).prod =
      Monoid.PushoutI.of (φ := k2PolyAmal_incl A P) true ⟨a, ha⟩ *
        (Monoid.PushoutI.of (φ := k2PolyAmal_incl A P) false ⟨g, hg⟩ *
          (Monoid.PushoutI.of (φ := k2PolyAmal_incl A P) true ⟨a⁻¹, A.inv_mem ha⟩ *
            Monoid.PushoutI.of (φ := k2PolyAmal_incl A P) false ⟨s⁻¹, P.inv_mem hs⟩)) := by
  rw [Monoid.CoprodI.Word.prod, k2PolyAmal_word_toList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul,
    Monoid.PushoutI.ofCoprodI_of]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_word_prod
