import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.DirectedUnion

/-!
# Finite witnesses for Steinberg relations in directed unions (lane LVCohnColimit)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  In the
Ara–Brustenga–Cortiñas computation of `K_*(C_2(𝔽₂))` (Münster J. Math. 2 (2009), proof of
Thm 3.6; `yaoseq6.tex` thm:skewyao, Step 3) one uses that `K₂` commutes with directed unions.
Besides lifting elements (`LVCohnK2.exists_finset_lift`), this needs the second half of
continuity: if an element `k ∈ St_I(T)` of a subring `T ⊆ S` becomes trivial in `St_I(S)`, then
it is already trivial in `St_I(T')` for every intermediate subring `T'` containing a suitable
finite set of coefficients.

The proof avoids words in free groups: the generators `x_{ij}(a)` of `St_I(S)` are sent to the
family `(x_{ij}(a))_{T'}` in the product `∏_{T' ⊇ T} St_I(T')` (with value `1` where `a ∉ T'`),
modulo the normal subgroup of families that are trivial on all `T'` containing some finite set.
Every Steinberg relator involves at most two coefficients, so this family satisfies the relations
and induces `toProd : St_I(S) → (∏ St_I(T')) / (eventually trivial)`.  On `St_I(T)` it restricts
to the diagonal, which gives `exists_finset_of_ringMap_eq_one`.
-/

namespace GroupApproximation.Full.LVCohnColimit

open SteinbergGroup
open scoped commutatorElement

section Witness

variable (I : Type*) [Fintype I] [DecidableEq I] {S : Type*} [Ring S] (T : Subring S)

/-- Subrings of `S` containing `T`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf
T1b.iii.) -/
abbrev OverRing := {T' : Subring S // T ≤ T'}

/-- The product `∏_{T' ⊇ T} St_I(T')`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf
T1b.iii.) -/
abbrev StProd := (T' : OverRing T) → SteinbergGroup I T'.1

/-- Families in `∏_{T' ⊇ T} St_I(T')` that are trivial on every `T'` containing some finite set
of coefficients.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def eventuallyOne : Subgroup (StProd I T) where
  carrier := {f | ∃ s : Finset S, ∀ T' : OverRing T, (s : Set S) ⊆ (T'.1 : Set S) → f T' = 1}
  one_mem' := ⟨∅, fun _ _ => rfl⟩
  mul_mem' := by
    classical
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, fun T' hT' => ?_⟩
    have h1 : f T' = 1 := hs T' fun c hc =>
      hT' (Finset.mem_coe.mpr (Finset.mem_union_left t (Finset.mem_coe.mp hc)))
    have h2 : g T' = 1 := ht T' fun c hc =>
      hT' (Finset.mem_coe.mpr (Finset.mem_union_right s (Finset.mem_coe.mp hc)))
    change f T' * g T' = 1
    rw [h1, h2, mul_one]
  inv_mem' := by
    rintro f ⟨s, hs⟩
    refine ⟨s, fun T' hT' => ?_⟩
    change (f T')⁻¹ = 1
    rw [hs T' hT', inv_one]

/-- Membership in `eventuallyOne`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf
T1b.iii.) -/
theorem mem_eventuallyOne (f : StProd I T) :
    f ∈ eventuallyOne I T ↔
      ∃ s : Finset S, ∀ T' : OverRing T, (s : Set S) ⊆ (T'.1 : Set S) → f T' = 1 :=
  Iff.rfl

/-- `eventuallyOne` is normal.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
instance eventuallyOne_normal : (eventuallyOne I T).Normal where
  conj_mem f hf g := by
    obtain ⟨s, hs⟩ := (mem_eventuallyOne I T f).mp hf
    refine (mem_eventuallyOne I T (g * f * g⁻¹)).mpr ⟨s, fun T' hT' => ?_⟩
    change g T' * f T' * (g T')⁻¹ = 1
    rw [hs T' hT', mul_one, mul_inv_cancel]

/-- The family `(x_{ij}(a))_{T'}` attached to a generator `x_{ij}(a)` of `St_I(S)`, with value
`1` on the subrings not containing `a`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf
T1b.iii.) -/
noncomputable def genFamily (g : SteinbergGenerator I S) : StProd I T := by
  classical
  exact fun T' => if hg : g.coefficient ∈ T'.1 then
    x g.row g.column g.row_ne_column (⟨g.coefficient, hg⟩ : T'.1) else 1

/-- `genFamily` on a subring containing the coefficient.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
theorem genFamily_of_mem (i j : I) (hij : i ≠ j) (c : S) (T' : OverRing T) (hc : c ∈ T'.1) :
    genFamily I T ⟨i, j, hij, c⟩ T' = x i j hij (⟨c, hc⟩ : T'.1) :=
  dif_pos hc

/-- The families `genFamily` satisfy the Steinberg relations up to `eventuallyOne`: each relator
involves two coefficients `a, b`, and holds on every subring containing `{a, b}`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem genFamily_relation (w : FreeGroup (SteinbergGenerator I S))
    (hw : w ∈ relations (I := I) (R := S)) :
    FreeGroup.lift (genFamily I T) w ∈ eventuallyOne I T := by
  classical
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      refine (mem_eventuallyOne I T _).mpr ⟨{a, b}, fun T' hT' => ?_⟩
      have ha : a ∈ T'.1 :=
        SetLike.mem_coe.mp (hT' (Finset.mem_coe.mpr (Finset.mem_insert_self a {b})))
      have hb : b ∈ T'.1 := SetLike.mem_coe.mp
        (hT' (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))))
      change genFamily I T ⟨i, j, hij, a⟩ T' * genFamily I T ⟨i, j, hij, b⟩ T' *
        (genFamily I T ⟨i, j, hij, a + b⟩ T')⁻¹ = 1
      rw [genFamily_of_mem I T i j hij a T' ha, genFamily_of_mem I T i j hij b T' hb,
        genFamily_of_mem I T i j hij (a + b) T' (add_mem ha hb), x_mul]
      exact mul_inv_eq_one.mpr rfl
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      refine (mem_eventuallyOne I T _).mpr ⟨{a, b}, fun T' hT' => ?_⟩
      have ha : a ∈ T'.1 :=
        SetLike.mem_coe.mp (hT' (Finset.mem_coe.mpr (Finset.mem_insert_self a {b})))
      have hb : b ∈ T'.1 := SetLike.mem_coe.mp
        (hT' (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))))
      change ⁅genFamily I T ⟨i, j, hij, a⟩ T', genFamily I T ⟨k, l, hkl, b⟩ T'⁆ = 1
      rw [genFamily_of_mem I T i j hij a T' ha, genFamily_of_mem I T k l hkl b T' hb]
      exact (x_commute_of_ne i j k l hij hkl hjk hli _ _).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      refine (mem_eventuallyOne I T _).mpr ⟨{a, b}, fun T' hT' => ?_⟩
      have ha : a ∈ T'.1 :=
        SetLike.mem_coe.mp (hT' (Finset.mem_coe.mpr (Finset.mem_insert_self a {b})))
      have hb : b ∈ T'.1 := SetLike.mem_coe.mp
        (hT' (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))))
      change ⁅genFamily I T ⟨i, j, hij, a⟩ T', genFamily I T ⟨j, k, hjk, b⟩ T'⁆ *
        (genFamily I T ⟨i, k, hik, a * b⟩ T')⁻¹ = 1
      rw [genFamily_of_mem I T i j hij a T' ha, genFamily_of_mem I T j k hjk b T' hb,
        genFamily_of_mem I T i k hik (a * b) T' (mul_mem ha hb),
        x_commutator i j k hij hjk hik]
      exact mul_inv_eq_one.mpr rfl

/-- The relators are killed in the quotient by `eventuallyOne`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem genFamily_relation_quotient (w : FreeGroup (SteinbergGenerator I S))
    (hw : w ∈ relations (I := I) (R := S)) :
    FreeGroup.lift (fun g => QuotientGroup.mk' (eventuallyOne I T) (genFamily I T g)) w = 1 := by
  have hcomp : (QuotientGroup.mk' (eventuallyOne I T)).comp (FreeGroup.lift (genFamily I T)) =
      FreeGroup.lift (fun g => QuotientGroup.mk' (eventuallyOne I T) (genFamily I T g)) :=
    FreeGroup.ext_hom _ _ fun g => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
  rw [← hcomp, MonoidHom.comp_apply]
  exact (QuotientGroup.eq_one_iff (N := eventuallyOne I T) (FreeGroup.lift (genFamily I T) w)).mpr
    (genFamily_relation I T w hw)

/-- `St_I(S) → (∏_{T' ⊇ T} St_I(T')) / (eventually trivial)`, `x_{ij}(a) ↦ [(x_{ij}(a))_{T'}]`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
noncomputable def toProd : SteinbergGroup I S →* StProd I T ⧸ eventuallyOne I T :=
  PresentedGroup.toGroup (f := fun g => QuotientGroup.mk' (eventuallyOne I T) (genFamily I T g))
    (genFamily_relation_quotient I T)

/-- `toProd` on generators.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem toProd_x (i j : I) (hij : i ≠ j) (c : S) :
    toProd I T (x i j hij c) =
      QuotientGroup.mk' (eventuallyOne I T) (genFamily I T ⟨i, j, hij, c⟩) :=
  PresentedGroup.toGroup.of _

/-- The diagonal `St_I(T) → ∏_{T' ⊇ T} St_I(T')`.  (`simple_kazhdan_sofic_group.tex`
l.733-735, leaf T1b.iii.) -/
noncomputable def diag : SteinbergGroup I T →* StProd I T :=
  MonoidHom.pi fun T' => ringMap (I := I) (Subring.inclusion T'.2)

/-- On `St_I(T)`, `toProd` is the diagonal.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf
T1b.iii.) -/
theorem toProd_comp_ringMap :
    (toProd I T).comp (ringMap (I := I) T.subtype) =
      (QuotientGroup.mk' (eventuallyOne I T)).comp (diag I T) := by
  refine PresentedGroup.ext ?_
  rintro ⟨i, j, hij, a⟩
  change toProd I T (ringMap T.subtype (x i j hij a)) =
    QuotientGroup.mk' (eventuallyOne I T) (diag I T (x i j hij a))
  rw [ringMap_x, toProd_x]
  refine congrArg (QuotientGroup.mk' (eventuallyOne I T)) (funext fun T' => ?_)
  rw [genFamily_of_mem I T i j hij (T.subtype a) T' (T'.2 a.2)]
  exact (ringMap_x (Subring.inclusion T'.2) i j hij a).symm

/-- **Finite witnesses.**  If `k ∈ St_I(T)` becomes trivial in `St_I(S)`, then it is trivial in
`St_I(T')` for every subring `T' ⊇ T` containing some finite set of coefficients.
(Ara–Brustenga–Cortiñas 2009, continuity of `K`-theory in the proof of Thm 3.6; `yaoseq6.tex`
thm:skewyao Step 3; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem exists_finset_of_ringMap_eq_one (k : SteinbergGroup I T)
    (hk : ringMap (I := I) T.subtype k = 1) :
    ∃ s : Finset S, ∀ (T' : Subring S) (hT : T ≤ T'), (s : Set S) ⊆ (T' : Set S) →
      ringMap (I := I) (Subring.inclusion hT) k = 1 := by
  have h1 : QuotientGroup.mk' (eventuallyOne I T) (diag I T k) = 1 := by
    have h2 := DFunLike.congr_fun (toProd_comp_ringMap I T) k
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hk, map_one] at h2
    exact h2.symm
  obtain ⟨s, hs⟩ := (mem_eventuallyOne I T (diag I T k)).mp
    ((QuotientGroup.eq_one_iff (N := eventuallyOne I T) (diag I T k)).mp h1)
  exact ⟨s, fun T' hT hsT => hs ⟨T', hT⟩ hsT⟩

end Witness

end GroupApproximation.Full.LVCohnColimit
