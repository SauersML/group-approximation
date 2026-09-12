import GroupApproximation.Higman.OmegaFatSelectedCutter

/-!
# A finite benign realization of the noncommuting Omega link

The stage-two relation needs the words `g_beta * b_beta^-1`.  Multiplication
from a direct product is not a homomorphism, so one must not obtain this
subgroup by multiplying the coordinates of `fatSelectedGraph`.

Instead we change the first coordinate of the fixed conjugator graph by the
free-group automorphism which inverts `a` and fixes `b,c`.  A graph generator
then becomes `(g_beta^-1,b_beta)`; its inverse is exactly
`(g_beta,b_beta^-1)`.  Thus the desired noncommuting link is represented as a
genuine subgroup of a direct product, where the finite paired-return cutter
applies without losing word order.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- Invert `a` and fix the two row generators. -/
def flipAHom : F₃ →* F₃ :=
  FreeGroup.lift fun i : Fin 3 => if i = 0 then (FreeGroup.of i)⁻¹ else FreeGroup.of i

@[simp] theorem flipAHom_a : flipAHom a = a⁻¹ := by
  simp [flipAHom, a]

@[simp] theorem flipAHom_b : flipAHom b = b := by
  simp [flipAHom, b]

@[simp] theorem flipAHom_c : flipAHom c = c := by
  simp [flipAHom, c]

theorem flipAHom_comp_self : flipAHom.comp flipAHom = MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i <;> simp [flipAHom]

theorem flipAHom_injective : Function.Injective flipAHom := by
  intro x y hxy
  have h := congrArg flipAHom hxy
  rwa [← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
    flipAHom_comp_self, MonoidHom.id_apply, MonoidHom.id_apply] at h

theorem flipAHom_rowElt (i : ℤ) : flipAHom (rowElt i) = rowElt i := by
  unfold rowElt
  simp

theorem flipAHom_comp_rowHom : flipAHom.comp rowHom = rowHom := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp [flipAHom_rowElt]

theorem flipAHom_bElt (f : E) : flipAHom (bElt f) = bElt f := by
  unfold bElt
  rw [← MonoidHom.comp_apply, flipAHom_comp_rowHom]

theorem flipAHom_aElt (f : E) : flipAHom (aElt f) = (aElt f)⁻¹ := by
  unfold aElt
  rw [map_mul, map_mul, map_inv, flipAHom_bElt, flipAHom_a]
  group

/-- The finite-rank graph embedding with the conjugate coordinate inverted. -/
noncomputable def fatInverseGraphBaseEmb (m : ℕ) :
    F₃ × F₃ →* FatCent3 m × F₃ :=
  ((genHom (fatOutside m)).comp flipAHom).prodMap (MonoidHom.id F₃)

@[simp] theorem fatInverseGraphBaseEmb_apply (m : ℕ) (p : F₃ × F₃) :
    fatInverseGraphBaseEmb m p =
      (genHom (fatOutside m) (flipAHom p.1), p.2) := rfl

theorem fatInverseGraphBaseEmb_injective (m : ℕ) :
    Function.Injective (fatInverseGraphBaseEmb m) := by
  intro p q hpq
  apply Prod.ext
  · apply flipAHom_injective
    apply genHom_injective_generic (fatOutside m)
    exact congrArg (fun z : FatCent3 m × F₃ => z.1) hpq
  · exact congrArg (fun z : FatCent3 m × F₃ => z.2) hpq

/-- The selected link graph.  Its literal generators, after inversion, are
`(g_beta,b_beta^-1)`; no multiplication of product coordinates occurs. -/
noncomputable def fatLinkGraph (m : ℕ) (B : Set E) :
    Subgroup (FatCent3 m × F₃) :=
  (Star.graphSub ⊓
    (ASub (B ∩ blockSet m)).prod (⊤ : Subgroup F₃)).map
      (fatInverseGraphBaseEmb m)

/-- The selected link graph is torsion-free benign in its finite semantic
base. -/
theorem benignTF_fatLinkGraph {m : ℕ} {B : Set E}
    (hB : BenignTF (ASub B)) : BenignTF (fatLinkGraph m B) := by
  letI : Group.IsFinitelyPresented (FatCent3 m) :=
    isFinitelyPresented_fatCent3 m
  letI : Group.IsFinitelyPresented (FatCent3 m × F₃) := inferInstance
  have hselected : BenignTF (ASub (B ∩ blockSet m)) := by
    rw [ASub_inter]
    exact BenignTF.inf hB (benignTF_ASub_blockSet m)
  have hprod : BenignTF
      ((ASub (B ∩ blockSet m)).prod (⊤ : Subgroup F₃)) := by
    rw [Star.prod_top_eq_comap_fst]
    exact BenignTF.comap Star.doubleOvergroup (MonoidHom.fst F₃ F₃) hselected
  have hgate : BenignTF
      (Star.graphSub ⊓
        (ASub (B ∩ blockSet m)).prod (⊤ : Subgroup F₃)) :=
    BenignTF.inf PairedReturnCutter.graph_benignTF hprod
  unfold fatLinkGraph
  exact BenignTF.mapEmb
    (IsPowerTorsionFree.prod (isPowerTorsionFree_fatCent3 m)
      IsPowerTorsionFree.of_isMulTorsionFree)
    hgate (fatInverseGraphBaseEmb m) (fatInverseGraphBaseEmb_injective m)

/-- Every selected block contributes the exact link pair needed by the
stage-two central HNN relation. -/
theorem fat_link_pair_mem {m : ℕ} {B : Set E} {beta : E}
    (hbeta : beta ∈ B ∩ blockSet m) :
    (fatGenCode m beta, (bElt beta)⁻¹) ∈ fatLinkGraph m B := by
  let p : F₃ × F₃ := ((aElt beta)⁻¹, (bElt beta)⁻¹)
  refine ⟨p, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hgen : (aElt beta, bElt beta) ∈ Star.graphSub := by
        apply Star.mem_graphSub.mpr
        refine ⟨FreeGroup.of (bK beta), ?_⟩
        rw [Star.graphHom_of]
        rfl
      simpa [p] using Star.graphSub.inv_mem hgen
    · refine Subgroup.mem_prod.mpr ⟨?_, Subgroup.mem_top _⟩
      exact (ASub (B ∩ blockSet m)).inv_mem
        (Subgroup.subset_closure ⟨beta, hbeta, rfl⟩)
  · apply Prod.ext
    · simp [p, fatGenCode, flipAHom_aElt]
    · rfl

/-- The block link itself is a finite benign edge, independent of the input
set `B`. -/
noncomputable def fatBlockLink (m : ℕ) : Subgroup (FatCent3 m × F₃) :=
  fatLinkGraph m (blockSet m)

theorem benignTF_fatBlockLink (m : ℕ) : BenignTF (fatBlockLink m) := by
  unfold fatBlockLink
  exact benignTF_fatLinkGraph (benignTF_ASub_blockSet m)

/-- A chosen finite cutter for the exact noncommuting block link. -/
noncomputable def fatBlockLinkWitness (m : ℕ) :
    TorsionFreeBenignWitness (fatBlockLink m) :=
  Classical.choice (benignTF_fatBlockLink m)

end Omega
end Higman
end GroupApproximation
