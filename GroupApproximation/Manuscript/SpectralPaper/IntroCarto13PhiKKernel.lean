import GroupApproximation.Manuscript.SpectralPaper.IntroCarto13PhiKDefs
import GroupApproximation.Meta.AxiomGuard

/-!
# The kernel of `Φ_K`, as a normal closure

Notes census, `thm:notes-visible-quotient` (`non_mf_group_notes.tex` ~1966).
The lane asks for `ker Φ_K` as the normal closure of the lamp commutators and
the zero-height-sum lamps.

The zero-height-sum lamps are generated, as a normal subgroup, by the
equal-height differences `δ(y, y', k) = inl(k_y · (k_{y'})⁻¹)` with
`height y = height y'`.  We prove two kernel identities.
* `ker_heightAbelianization`: `ker Φ_K` is the normal closure of the
  equal-height differences `heightDiffs K`.
* `ker_heightAbelianization_eq_union`: the same with the one-site commutator
  lamps `inl([a, b]_y)` added.

Route.  `Φ_K` kills each generator.  For differences use `push_single` and
equal heights; for commutator lamps, `Abelianization.of [a, b] = 1`.  Since
the kernel is normal, the normal closure lies in it.  Conversely,
`NN04.ker_pushWreath_comp_le` with `R` the normal closure needs only the
generators (`h1`) and a second site in every fibre (`exists_second_site`).
-/

namespace GroupApproximation.SpectralPaper.IntroCarto13

open SemidirectProduct MarkedCompression ExplicitLinearModel LiteralDoublingWreath
open FinitePerfectLamp GroupApproximation.WreathLampPushforward GroupApproximation.Full.NN04
open scoped commutatorElement

/-- The equal-height lamp differences. -/
def heightDiffs (K : Type) [Group K] : Set (WFin K) :=
  {w | ∃ (y y' : Cosets conjD conjD_injective) (k : K), heightSite y = heightSite y' ∧
    w = inl (Lamp.single y k * (Lamp.single y' k)⁻¹)}

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightDiffs

/-- The one-site commutator lamps. -/
def commutatorLamps (K : Type) [Group K] : Set (WFin K) :=
  {w | ∃ (y : Cosets conjD conjD_injective) (a b : K), w = inl (Lamp.single y ⁅a, b⁆)}

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.commutatorLamps

/-- The left component of `Φ_K` on a lamp. -/
theorem heightAbelianization_inl_left (K : Type) [Group K]
    (f : Lamp K (Cosets conjD conjD_injective)) :
    (heightAbelianization K (inl f)).left =
      ((pushHom (K := Abelianization K) heightSite).comp
        (lampValueHom Abelianization.of)) f := rfl

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization_inl_left

/-- `Φ_K` kills a lamp whose left image vanishes. -/
theorem inl_mem_ker_of_left (K : Type) [Group K]
    {f : Lamp K (Cosets conjD conjD_injective)}
    (hf : ((pushHom (K := Abelianization K) heightSite).comp
        (lampValueHom Abelianization.of)) f = 1) :
    (inl f : WFin K) ∈ (heightAbelianization K).ker := by
  rw [MonoidHom.mem_ker]
  refine SemidirectProduct.ext ?_ rfl
  exact (heightAbelianization_inl_left K f).trans hf

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.inl_mem_ker_of_left

/-- `Φ_K` kills every equal-height difference. -/
theorem heightDiff_mem_ker (K : Type) [Group K] {y y' : Cosets conjD conjD_injective}
    (h : heightSite y = heightSite y') (k : K) :
    (inl (Lamp.single y k * (Lamp.single y' k)⁻¹) : WFin K) ∈
      (heightAbelianization K).ker := by
  classical
  refine inl_mem_ker_of_left K ?_
  have hpush : ∀ (x : Cosets conjD conjD_injective) (a : Abelianization K),
      pushHom (K := Abelianization K) heightSite (Lamp.single x a) =
        Lamp.single (heightSite x) a :=
    fun x a => push_single heightSite x a
  rw [map_mul, map_inv, MonoidHom.comp_apply, MonoidHom.comp_apply, lampValueHom_single,
    lampValueHom_single, hpush, hpush, h, mul_inv_cancel]

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightDiff_mem_ker

/-- `Φ_K` kills every one-site commutator lamp. -/
theorem commutatorLamp_mem_ker (K : Type) [Group K] (y : Cosets conjD conjD_injective)
    (a b : K) :
    (inl (Lamp.single y ⁅a, b⁆) : WFin K) ∈ (heightAbelianization K).ker := by
  refine inl_mem_ker_of_left K ?_
  have hcomm : (⁅Abelianization.of a, Abelianization.of b⁆ : Abelianization K) = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [MonoidHom.comp_apply, lampValueHom_single, map_commutatorElement, hcomm,
    Lamp.single_one, map_one]

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.commutatorLamp_mem_ker

/-- **`ker Φ_K` is the normal closure of the equal-height differences.** -/
theorem ker_heightAbelianization (K : Type) [Group K] :
    (heightAbelianization K).ker = Subgroup.normalClosure (heightDiffs K) := by
  refine le_antisymm ?_ ?_
  · exact ker_pushWreath_comp_le (Subgroup.normalClosure (heightDiffs K)) heightSite
      heightSite_smul
      (fun y y' k h =>
        Subgroup.subset_normalClosure (s := heightDiffs K) ⟨y, y', k, h, rfl⟩)
      exists_second_site
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨y, y', k, h, rfl⟩
    exact heightDiff_mem_ker K h k

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.ker_heightAbelianization

/-- **The lane's form.**  `ker Φ_K` is the normal closure of the lamp commutators
together with the equal-height differences. -/
theorem ker_heightAbelianization_eq_union (K : Type) [Group K] :
    (heightAbelianization K).ker =
      Subgroup.normalClosure (commutatorLamps K ∪ heightDiffs K) := by
  refine le_antisymm ?_ ?_
  · rw [ker_heightAbelianization]
    exact Subgroup.normalClosure_mono Set.subset_union_right
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ (⟨y, a, b, rfl⟩ | ⟨y, y', k, h, rfl⟩)
    · exact commutatorLamp_mem_ker K y a b
    · exact heightDiff_mem_ker K h k

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.ker_heightAbelianization_eq_union

end GroupApproximation.SpectralPaper.IntroCarto13
