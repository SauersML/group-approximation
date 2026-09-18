import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Set.Finite.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite index of the commutator subgroup from generator data

Let `V ≤ G` be contained in the closure of a set `S`.  Suppose a finite set `T ⊆ V` generates
every element of `S` modulo `⁅V, V⁆`, and every `t ∈ T` has `t ^ m ∈ [V, V]` for one `m > 0`.
Then `[V, V]` has finite index in `V` (`commutator_finiteIndex_of_gens`).

Route: `closure T ⊔ [V, V] = ⊤` in `V` (push through `V.subtype`, `Subgroup.map_sup`,
`Subgroup.map_closure`, `Subgroup.map_subtype_commutator`); mapping to the abelianisation kills
`[V, V]` (`Abelianization.ker_of`), so the images of `T` generate it.  They lie in the kernel of
`powMonoidHom m`, hence so does everything, and `CommGroup.finite_of_fg_torsion` gives a finite
quotient.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {G : Type*} [Group G] {V : Subgroup G}

theorem closure_sup_commutator_eq_top {S : Set G} (hVS : V ≤ Subgroup.closure S) {T : Set ↥V}
    (hgen : ∀ g ∈ S, g ∈ Subgroup.closure (Subtype.val '' T) ⊔ ⁅V, V⁆) :
    Subgroup.closure T ⊔ commutator ↥V = ⊤ := by
  have hmap : (Subgroup.closure T ⊔ commutator ↥V).map V.subtype =
      Subgroup.closure (V.subtype '' T) ⊔ ⁅V, V⁆ := by
    rw [Subgroup.map_sup, Subgroup.map_closure, Subgroup.map_subtype_commutator]
  have hle : Subgroup.closure S ≤ Subgroup.closure (Subtype.val '' T) ⊔ ⁅V, V⁆ :=
    Subgroup.closure_le.mpr hgen
  refine top_le_iff.mp ?_
  intro x _
  have hx : x.1 ∈ (Subgroup.closure T ⊔ commutator ↥V).map V.subtype := by
    rw [hmap]
    exact hle (hVS x.2)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have e : y = x := Subtype.ext hyx
  subst e
  exact hy

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.closure_sup_commutator_eq_top

theorem closure_image_of_eq_top {T : Set ↥V} (htop : Subgroup.closure T ⊔ commutator ↥V = ⊤) :
    Subgroup.closure ((Abelianization.of : ↥V →* Abelianization ↥V) '' T) = ⊤ := by
  have hsurj : Function.Surjective (Abelianization.of : ↥V →* Abelianization ↥V) :=
    QuotientGroup.mk_surjective (s := commutator ↥V)
  have hbot : (commutator ↥V).map (Abelianization.of : ↥V →* Abelianization ↥V) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (Abelianization.ker_of ↥V).ge
  have h1 := congrArg (Subgroup.map (Abelianization.of : ↥V →* Abelianization ↥V)) htop
  rw [Subgroup.map_sup, hbot, sup_bot_eq, Subgroup.map_closure,
    Subgroup.map_top_of_surjective _ hsurj] at h1
  exact h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.closure_image_of_eq_top

theorem isTorsion_abelianization {T : Set ↥V}
    (h1 : Subgroup.closure ((Abelianization.of : ↥V →* Abelianization ↥V) '' T) = ⊤)
    {m : ℕ} (hm : 0 < m) (hTpow : ∀ t ∈ T, t ^ m ∈ commutator ↥V) :
    Monoid.IsTorsion (Abelianization ↥V) := by
  have hker : Subgroup.closure ((Abelianization.of : ↥V →* Abelianization ↥V) '' T) ≤
      (powMonoidHom m : Abelianization ↥V →* Abelianization ↥V).ker := by
    refine Subgroup.closure_le.mpr ?_
    rintro _ ⟨t, ht, rfl⟩
    have hk : (Abelianization.of : ↥V →* Abelianization ↥V) t ^ m = 1 :=
      (map_pow (Abelianization.of : ↥V →* Abelianization ↥V) t m).symm.trans
        (MonoidHom.mem_ker.mp ((Abelianization.ker_of ↥V).ge (hTpow t ht)))
    exact (MonoidHom.mem_ker (f := powMonoidHom m)
      (x := (Abelianization.of : ↥V →* Abelianization ↥V) t)).mpr hk
  intro a
  have ha : a ∈ Subgroup.closure ((Abelianization.of : ↥V →* Abelianization ↥V) '' T) := by
    rw [h1]
    exact Subgroup.mem_top a
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, MonoidHom.mem_ker.mp (hker ha)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.isTorsion_abelianization

/-- `[V, V]` has finite index in `V` when finitely many elements of `V`, each torsion modulo
`[V, V]` with one exponent `m`, generate every element of a generating set `S` modulo
`[V, V]`. -/
theorem commutator_finiteIndex_of_gens {S : Set G} (hVS : V ≤ Subgroup.closure S)
    {T : Set ↥V} (hT : T.Finite)
    (hgen : ∀ g ∈ S, g ∈ Subgroup.closure (Subtype.val '' T) ⊔ ⁅V, V⁆) {m : ℕ} (hm : 0 < m)
    (hTpow : ∀ t ∈ T, t ^ m ∈ commutator ↥V) : (commutator ↥V).FiniteIndex := by
  have h1 := closure_image_of_eq_top (closure_sup_commutator_eq_top hVS hgen)
  have _hfg : Group.FG (Abelianization ↥V) := Group.fg_iff.mpr ⟨_, h1, hT.image _⟩
  have _hfin : Finite (↥V ⧸ commutator ↥V) :=
    CommGroup.finite_of_fg_torsion (Abelianization ↥V) (isTorsion_abelianization h1 hm hTpow)
  exact Subgroup.finiteIndex_of_finite_quotient

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutator_finiteIndex_of_gens

end GroupApproximation.BooneHigman.Metabelian.Envelope
