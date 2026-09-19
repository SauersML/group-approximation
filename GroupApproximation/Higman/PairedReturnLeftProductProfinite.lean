import GroupApproximation.Higman.PairedReturnLeftProduct
import GroupApproximation.Higman.PairedReturnQProfinite

/-!
# Finite separation of the left matched-factor product

The set product `graphSub * M` is not a subgroup, so ordinary subgroup
closure cannot be applied to it directly.  We instead formulate the exact
finite-image adherence property needed by the amalgam normal-form argument
and prove that it already forces genuine membership.  The separating maps are
the finite readers from `ConjugatorGraphProfinite`, augmented by the retracted
`K` coordinate.
-/

namespace GroupApproximation
namespace Higman
namespace PairedReturnLeftProductProfinite

open Conj
open scoped Pointwise
open PairedReturnLeftProduct
open ConjugatorGraphProfinite
open PairedReturnQProfinite

abbrev P : Type := PairedReturnGraphIntersection.P
abbrev Sync : Type := ↥K

theorem retK_cbHom (w : FreeGroup Sync) : Coord.retK (cbHom w) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [Coord.ker_retK_eq_cbHom_range]
  exact ⟨w, rfl⟩

/-- The reader also handles the canonical kernel word followed by its `K`
tail, provided it starts in the inverse tail state. -/
theorem finiteReadAct_cbHom_mul (Q : Type) [Group Q] (q : F₃ →* Q)
    (w : FreeGroup Sync) (k : Sync) (u : Q) :
    finiteReadAct q (cbHom w * (k : F₃))
        (u, (q (k : F₃))⁻¹) =
      (q (Star.evalHom w) * u, 1) := by
  rw [map_mul]
  change finiteReadAct q (cbHom w)
    (finiteReadAct q (k : F₃) (u, (q (k : F₃))⁻¹)) = _
  rw [finiteReadAct_of_mem_K q k.property]
  simp only [mul_inv_cancel]
  exact finiteReadAct_cbHom q w u

theorem finiteReadAct_cbHom_mul_of_image_eq
    (Q : Type) [Group Q] (q : F₃ →* Q)
    (w : FreeGroup Sync) (k : Sync) (u s : Q)
    (hs : q (k : F₃) = s) :
    finiteReadAct q (cbHom w * (k : F₃)) (u, s⁻¹) =
      (q (Star.evalHom w) * u, 1) := by
  rw [← hs]
  exact finiteReadAct_cbHom_mul Q q w k u

/-- The finite test remembers the reader permutation, the retracted tail, and
the second coordinate. -/
def productTest (Q : Type) [Group Q] (q : F₃ →* Q) :
    P →* (Equiv.Perm (Q × Q) × Q) × Q :=
  (((finiteReadAct q).comp (MonoidHom.fst F₃ F₃)).prod
    ((q.comp Coord.retK).comp (MonoidHom.fst F₃ F₃))).prod
      (q.comp (MonoidHom.snd F₃ F₃))

/-- Membership in every special finite image of the product set.  Any point
in its actual profinite set-closure has this property. -/
def ProductAdherent (z : P) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (q : F₃ →* Q),
    ∃ g ∈
      (Star.graphSub : Set P) *
        (PairedReturnGraphIntersection.M : Set P),
      productTest Q q g = productTest Q q z

/-- A matching finite test forces the canonical kernel word and the second
coordinate to have the same image. -/
theorem finite_test_matches {x y : F₃} (w : FreeGroup Sync)
    (hw : cbHom w = x * (Coord.retK x)⁻¹)
    (Q : Type) [Group Q] [Finite Q] (q : F₃ →* Q)
    (hmatch : ∃ g ∈
      (Star.graphSub : Set P) *
        (PairedReturnGraphIntersection.M : Set P),
      productTest Q q g = productTest Q q (x, y)) :
    q (Star.evalHom w) = q y := by
  obtain ⟨g, hg, htest⟩ := hmatch
  obtain ⟨v, k, hx, hy⟩ :=
    (mem_graphSub_mul_edge_iff (x := g.1) (y := g.2)).mp hg
  have hact := congrArg (fun z : (Equiv.Perm (Q × Q) × Q) × Q ↦ z.1.1) htest
  have htail := congrArg (fun z : (Equiv.Perm (Q × Q) × Q) × Q ↦ z.1.2) htest
  have hsnd := congrArg (fun z : (Equiv.Perm (Q × Q) × Q) × Q ↦ z.2) htest
  change finiteReadAct q g.1 = finiteReadAct q x at hact
  change q (Coord.retK g.1) = q (Coord.retK x) at htail
  change q g.2 = q y at hsnd
  rw [hx, map_mul, retK_cbHom, Coord.retK_of_mem_K k.property,
    one_mul] at htail
  rw [hy] at hsnd
  have hxcanon : x = cbHom w * (Coord.retK x) := by
    rw [hw]
    group
  rw [hx, hxcanon] at hact
  have happ := congrArg
    (fun p : Equiv.Perm (Q × Q) ↦
      p ((1 : Q), (q (Coord.retK x))⁻¹)) hact
  have hretMem : Coord.retK x ∈ K := by
    rw [← subtype_comp_retKSync]
    exact (retKSync x).property
  rw [finiteReadAct_cbHom_mul_of_image_eq Q q v k 1
      (q (Coord.retK x)) htail,
    finiteReadAct_cbHom_mul Q q w ⟨Coord.retK x, hretMem⟩ 1] at happ
  have hvalues : q (Star.evalHom v) = q (Star.evalHom w) := by
    simpa only [mul_one] using congrArg Prod.fst happ
  exact hvalues.symm.trans hsnd

/-- **The product `graphSub * M` is separated by the explicit finite reader
tests.** -/
theorem mem_graphSub_mul_edge_of_productAdherent {z : P}
    (hz : ProductAdherent z) :
    z ∈ (Star.graphSub : Set P) *
      (PairedReturnGraphIntersection.M : Set P) := by
  let n : F₃ := z.1 * (Coord.retK z.1)⁻¹
  have hretMem : Coord.retK z.1 ∈ K := by
    rw [← subtype_comp_retKSync]
    exact (retKSync z.1).property
  have hnker : n ∈ MonoidHom.ker Coord.retK := by
    apply MonoidHom.mem_ker.mpr
    simp only [n, map_mul, map_inv]
    rw [Coord.retK_of_mem_K hretMem]
    group
  rw [Coord.ker_retK_eq_cbHom_range] at hnker
  obtain ⟨w, hw⟩ := hnker
  have heval : Star.evalHom w = z.2 := by
    have hdiff : (Star.evalHom w)⁻¹ * z.2 = 1 := by
      apply eq_one_of_all_finite_images_one
      intro Q _ _ q
      have hq := finite_test_matches w hw Q q (hz Q q)
      rw [map_mul, map_inv, hq, inv_mul_cancel]
    exact inv_mul_eq_one.mp hdiff
  apply mem_graphSub_mul_edge_iff.mpr
  refine ⟨w, retKSync z.1, ?_, heval.symm⟩
  have hret : ((retKSync z.1 : Sync) : F₃) = Coord.retK z.1 := by
    exact DFunLike.congr_fun subtype_comp_retKSync z.1
  rw [hret, hw]
  dsimp [n]
  group

end PairedReturnLeftProductProfinite
end Higman
end GroupApproximation
