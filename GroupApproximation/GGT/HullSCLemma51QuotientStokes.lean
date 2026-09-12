import GroupApproximation.GGT.HullSCLemma51QuasiGeodesicTransfer
import GroupApproximation.GGT.HullSCLemma44BoundedInput
import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.CayleyFourPointConverse
import GroupApproximation.Algebra.QuotientLinearStokes
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's two moves, and hyperbolicity of the quotient relative Cayley graph

Osin's proof of Lemma 5.1 (arXiv:math/0411039v3, (18)--(21)) takes a word over the
relative alphabet that dies in the quotient and either applies a relator along it,
when it is quasi-geodesic, or replaces a stretch of it by a shorter one.  This module
supplies both moves in the shape `DiscreteStokes.linearStokes_image_of_steps` needs.

* **The relator cut** (`exists_quotientMove_of_leastAreaCertificates`, first branch)
  is the cut of `exists_relativeDehnCut_of_quasiGeodesicKernelWord`.  The boundary arc
  has the value of `leftSide⁻¹ · exterior · rightSide⁻¹` in `G`, and the replacement
  that of `leftSide⁻¹ · remainder⁻¹ · rightSide⁻¹`.  These agree in the quotient because
  `exterior ++ remainder` is a relator, and together they have at most `4 ε + 2 L`
  letters.
* **The local shortening** (second branch): a word that is not
  `(1/4, 1)`-quasi-geodesic has a stretch whose endpoints are closer than a quarter of
  its length minus one, and a geodesic word replaces it.

With the linear Stokes inequality for the source relative alphabet, which is
four-point hyperbolic because the family is hyperbolically embedded, this gives the
linear Stokes inequality for the quotient relative alphabet
(`exists_linearStokes_mapSurjective_of_leastAreaCertificates`).  Bowditch's criterion
(`Algebra/BowditchSlim.lean`) then makes the quotient relative Cayley graph
hyperbolic, which is clause (a) of hyperbolic embeddedness of the image family
(`hyperbolic_mapSurjective_of_leastAreaCertificates`).
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric
open GroupApproximation.DiscreteStokes

universe u v w

/-- The vertex of a relative path after `i` letters. -/
theorem vertex_eq_mul_listVal_take {G : Type u} [Group G] {Lambda : Type w} (a : G) :
    ∀ (word : List (GGT.RelLetter G Lambda)) (i : ℕ),
      GGT.OsinComponents.vertex a word i = a * GGT.RelLetter.listVal (word.take i)
  | [], i => by
      rw [GGT.OsinComponents.vertex_nil, List.take_nil, GGT.RelLetter.listVal_nil, mul_one]
  | b :: t, 0 => by
      rw [GGT.OsinComponents.vertex_zero, List.take_zero, GGT.RelLetter.listVal_nil, mul_one]
  | b :: t, i + 1 => by
      rw [GGT.OsinComponents.vertex_cons_succ, vertex_eq_mul_listVal_take (a * b.val) t i,
        List.take_succ_cons]
      unfold GGT.RelLetter.listVal
      rw [List.map_cons, List.prod_cons, mul_assoc]

/-- Values of the formally inverted letters of an admissible word are letters. -/
theorem val_mem_alphabet_of_revInv {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {v : List (GGT.RelLetter G Lambda)}
    (hv : RelWord.IsAdmissible D v) :
    ∀ x ∈ (RelWord.revInv v).map GGT.RelLetter.val, x ∈ D.alphabet.carrier := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  rw [RelWord.revInv, List.mem_reverse, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  rw [RelWord.val_inv]
  exact D.alphabet.symmetricGenerating.inv_mem _
    (RelativeBoundaryContiguity.val_mem_alphabet_of_isLetter D (hv b hb))

/-- **Osin's two moves on a quotient-null word.**  A word over the relative alphabet
that dies in the quotient but not in `G` admits a relator cut through an exterior
word, with at most `4 ε + 2 L` letters in the exterior and the replacement, or a local
shortening by a geodesic word. -/
theorem exists_quotientMove_of_leastAreaCertificates
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho L : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho) (hL : ∀ word ∈ W, word.length ≤ L)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeLeastAreaDiagram D W R),
      Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram))
    (w : List G) (hw : ∀ x ∈ w, x ∈ D.alphabet.carrier) (hqw : q w.prod = 1)
    (hne : w.prod ≠ 1) :
    (∃ (r : ℕ) (before arc after ext repl : List G),
        w.rotate r = before ++ arc ++ after ∧ (∀ x ∈ ext, x ∈ D.alphabet.carrier) ∧
          (∀ x ∈ repl, x ∈ D.alphabet.carrier) ∧ ext.prod = arc.prod ∧
            q repl.prod = q ext.prod ∧ repl.length < arc.length ∧
              ext.length + repl.length ≤ 4 * eps + 2 * L) ∨
      (∃ (α sub β geo : List G), w = α ++ sub ++ β ∧ (∀ x ∈ geo, x ∈ D.alphabet.carrier) ∧
        geo.prod = sub.prod ∧ 4 * geo.length + 4 ≤ sub.length) := by
  obtain ⟨outer, hadm, houter⟩ := exists_letterwise_spelling D w hw
  have hword : IsWord D.alphabet.carrier w w.prod := ⟨hw, rfl⟩
  by_cases hqg : GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / 4) 1 outer
  · -- a relator cut
    left
    obtain ⟨C⟩ := exists_relativeDehnCut_of_quasiGeodesicKernelWord D hsc hmu hrho q hker
      hcert w hword hne hqw hadm houter hqg
    have hrelAdm : RelWord.IsAdmissible D C.relator := hsc.admissible C.relator C.relator_mem
    have hextAdm : RelWord.IsAdmissible D C.contiguity.exterior := by
      intro a ha
      apply hrelAdm
      rw [C.contiguity.relator_decomposition]
      exact List.mem_append_left _ ha
    have hrel : q (GGT.RelLetter.listVal C.relator) = 1 := by
      have hmem : GGT.RelLetter.listVal C.relator ∈ q.ker := by
        rw [hker]
        exact Subgroup.subset_normalClosure ⟨C.relator, C.relator_mem, rfl⟩
      exact MonoidHom.mem_ker.mp hmem
    have hext_rem : q (GGT.RelLetter.listVal C.contiguity.exterior) =
        (q (GGT.RelLetter.listVal C.contiguity.remainder))⁻¹ := by
      rw [C.contiguity.relator_decomposition, RelWord.listVal_append, map_mul] at hrel
      exact eq_inv_of_mul_eq_one_left hrel
    refine ⟨C.contiguity.rotation, C.contiguity.boundaryBefore, C.contiguity.boundaryArc,
      C.contiguity.boundaryAfter,
      (RelWord.revInv C.contiguity.leftSide).map GGT.RelLetter.val ++
        C.contiguity.exterior.map GGT.RelLetter.val ++
          (RelWord.revInv C.contiguity.rightSide).map GGT.RelLetter.val,
      C.contiguity.replacementWord, C.contiguity.boundary_decomposition, ?_, ?_, ?_, ?_,
      C.replacement_length_lt, ?_⟩
    · intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact val_mem_alphabet_of_revInv D C.contiguity.leftSide_admissible x hx
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        exact RelativeBoundaryContiguity.val_mem_alphabet_of_isLetter D (hextAdm a ha)
      · exact val_mem_alphabet_of_revInv D C.contiguity.rightSide_admissible x hx
    · intro x hx
      have hremAdm : RelWord.IsAdmissible D C.contiguity.remainder := by
        intro a ha
        apply hrelAdm
        rw [C.contiguity.relator_decomposition]
        exact List.mem_append_right _ ha
      unfold RelativeBoundaryContiguity.replacementWord at hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact val_mem_alphabet_of_revInv D C.contiguity.leftSide_admissible x hx
      · exact val_mem_alphabet_of_revInv D hremAdm x hx
      · exact val_mem_alphabet_of_revInv D C.contiguity.rightSide_admissible x hx
    · have e : ((RelWord.revInv C.contiguity.leftSide).map GGT.RelLetter.val ++
          C.contiguity.exterior.map GGT.RelLetter.val ++
            (RelWord.revInv C.contiguity.rightSide).map GGT.RelLetter.val).prod =
          GGT.RelLetter.listVal (RelWord.revInv C.contiguity.leftSide) *
            GGT.RelLetter.listVal C.contiguity.exterior *
            GGT.RelLetter.listVal (RelWord.revInv C.contiguity.rightSide) := by
        simp only [List.prod_append, GGT.RelLetter.listVal]
      rw [e, RelWord.listVal_revInv, RelWord.listVal_revInv, C.contiguity.exterior_value]
      group
    · have e : ((RelWord.revInv C.contiguity.leftSide).map GGT.RelLetter.val ++
          C.contiguity.exterior.map GGT.RelLetter.val ++
            (RelWord.revInv C.contiguity.rightSide).map GGT.RelLetter.val).prod =
          GGT.RelLetter.listVal (RelWord.revInv C.contiguity.leftSide) *
            GGT.RelLetter.listVal C.contiguity.exterior *
            GGT.RelLetter.listVal (RelWord.revInv C.contiguity.rightSide) := by
        simp only [List.prod_append, GGT.RelLetter.listVal]
      rw [e, C.contiguity.replacementWord_prod]
      simp only [RelWord.listVal_revInv, map_mul, map_inv, hext_rem]
    · have hrl : C.contiguity.exterior.length + C.contiguity.remainder.length ≤ L := by
        have h := hL C.relator C.relator_mem
        rw [C.contiguity.relator_decomposition, List.length_append] at h
        exact h
      have hl := C.contiguity.leftSide_short
      have hr := C.contiguity.rightSide_short
      simp only [RelativeBoundaryContiguity.replacementWord, RelWord.revInv, List.length_append,
        List.length_map, List.length_reverse]
      omega
  · -- a local shortening
    right
    have hlenouter : outer.length = w.length := length_of_letterwise_spelling houter
    have hex : ∃ i j : ℕ, i ≤ j ∧ j ≤ outer.length ∧
        ((wordDist D.alphabet.carrier (GGT.OsinComponents.vertex 1 outer i)
          (GGT.OsinComponents.vertex 1 outer j) : ℕ) : ℝ) <
          (1 / 4 : ℝ) * ((j - i : ℕ) : ℝ) - 1 := by
      by_contra hno
      exact hqg ⟨hadm, fun i j hij hj => not_lt.mp (fun h => hno ⟨i, j, hij, hj, h⟩)⟩
    obtain ⟨i, j, hij, hj, hlt⟩ := hex
    have hvert : ∀ k, GGT.OsinComponents.vertex 1 outer k = (w.take k).prod := by
      intro k
      rw [vertex_eq_mul_listVal_take, one_mul]
      unfold GGT.RelLetter.listVal
      rw [List.map_take, houter]
    rw [hvert i, hvert j] at hlt
    obtain ⟨geo, hgeo⟩ := exists_isGeodesicWord D.alphabet.symmetricGenerating
      ((w.take i).prod⁻¹ * (w.take j).prod)
    have e : i + (j - i) = j := by omega
    have hsplit : w.take j = w.take i ++ (w.drop i).take (j - i) := by
      rw [← List.take_add, e]
    refine ⟨w.take i, (w.drop i).take (j - i), w.drop j, geo, ?_, hgeo.isWord.letters, ?_, ?_⟩
    · rw [← List.take_add, e, List.take_append_drop]
    · rw [hgeo.isWord.prod_eq, hsplit, List.prod_append]
      group
    · have hd : (4 * (wordDist D.alphabet.carrier (w.take i).prod (w.take j).prod : ℝ) + 4) <
          ((j - i : ℕ) : ℝ) := by
        linarith
      have hd' : 4 * wordDist D.alphabet.carrier (w.take i).prod (w.take j).prod + 4 < j - i := by
        exact_mod_cast hd
      rw [List.length_take, List.length_drop, hgeo.length_eq]
      change 4 * wordDist D.alphabet.carrier (w.take i).prod (w.take j).prod + 4 ≤
        min (j - i) (w.length - i)
      omega

/-- **The linear Stokes inequality for the quotient relative alphabet**, from the
least-area certificates over a strongly bounded family. -/
theorem exists_linearStokes_mapSurjective_of_leastAreaCertificates
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    {W : Set (List (GGT.RelLetter G Lambda))} {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsBoundedLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeLeastAreaDiagram D W R),
      Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram)) :
    ∃ C : ℕ, LinearStokes (D.mapSurjective q hq).alphabet.carrier C := by
  obtain ⟨δ, hδ⟩ := GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hD
  obtain ⟨L, hL⟩ := hsc.lengthBounded
  have hG := linearStokes_of_isFourPointHyperbolic D.alphabet.symmetricGenerating hδ
  have h := linearStokes_image_of_steps D.alphabet.symmetricGenerating q hq hG
    (exists_quotientMove_of_leastAreaCertificates D hsc.toIsLemma44Input hL hmu hrho q hker
      hcert)
  rw [← GGT.RelGenSet.alphabet_carrier_mapSurjective D q hq] at h
  exact ⟨_, h⟩

/-- **Clause (a) of hyperbolic embeddedness for the image family**: the quotient
relative Cayley graph is hyperbolic. -/
theorem hyperbolic_mapSurjective_of_leastAreaCertificates
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    {W : Set (List (GGT.RelLetter G Lambda))} {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsBoundedLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeLeastAreaDiagram D W R),
      Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram)) :
    ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley (D.mapSurjective q hq).alphabet) := by
  obtain ⟨C, hC⟩ := exists_linearStokes_mapSurjective_of_leastAreaCertificates D hD hsc hmu
    hrho q hq hker hcert
  have hS := (D.mapSurjective q hq).alphabet.symmetricGenerating
  have hslim := isSlimTriangles_of_bowditchH4 hS (Nat.succ_pos _)
    (bowditchH4_of_linearStokes hS hC)
  exact ⟨_, GGT.isHyperbolicSpace_cayley_of_fourPoint _
    (Hyperbolic.isFourPointHyperbolic_of_isSlimTriangles hS hslim)⟩

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.vertex_eq_mul_listVal_take
#audit_axioms GroupApproximation.HullSC.exists_quotientMove_of_leastAreaCertificates
#audit_axioms GroupApproximation.HullSC.exists_linearStokes_mapSurjective_of_leastAreaCertificates
#audit_axioms GroupApproximation.HullSC.hyperbolic_mapSurjective_of_leastAreaCertificates
