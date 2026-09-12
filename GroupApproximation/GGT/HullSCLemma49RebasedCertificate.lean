import GroupApproximation.GGT.HullSCLemma49Rebase

/-!
# Rebasing the algebraic Greendlinger certificate for Hull's Lemma 4.9

A boundary contiguity may cross the cut of the chosen power word.  Extract
its letterwise arc, rotate to the arc's start, and apply the existing rebasing
theorem.  The shortest representative changes by conjugation and its period
length is preserved.  No universal zero-rotation premise is needed.
-/

namespace GroupApproximation.HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- A cyclic algebraic contiguity gives the word data used by the power
rebasing theorem.  Its source relator is already correctly based. -/
theorem exists_lemma49ExteriorArc_of_certificate
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    (Z : Lemma49GeodesicPowerDiagram D v g n)
    (K : RelativeDiagramCertificate D (RelWord.symmetrized v) eps mu
      Z.toRelativeReducedDiagram) :
    Nonempty (Lemma49EmbeddedExteriorArc D v g n eps mu Z) := by
  obtain ⟨i, C, _, hlarge⟩ := K.largeCell
  let Cpower : RelativeBoundaryContiguity D eps
      ((lemma49BoundaryPower Z.boundaryWord n).map GGT.RelLetter.val)
      (K.cellLabel i) := by
    change RelativeBoundaryContiguity D eps
      Z.toRelativeReducedDiagram.boundaryWord (K.cellLabel i)
    exact K.boundaryWord_eq ▸ C
  have hlargePower : (1 - 23 * mu) * ((K.cellLabel i).length : ℝ) ≤
      (Cpower.exterior.length : ℝ) := by
    have heq : Cpower.exterior = C.exterior :=
      RelativeBoundaryContiguity.exterior_eq_boundaryCast K.boundaryWord_eq C
    rw [heq]
    exact hlarge
  obtain ⟨pre, arc, suf, hsplit, _, _, _, harcValue⟩ :=
    exists_boundaryArc_source Cpower
  let power := lemma49BoundaryPower Z.boundaryWord n
  have hpowerPos : 0 < power.length := by
    have hval : GGT.RelLetter.listVal power = g ^ n := by
      have hg := Z.boundary_geodesic.2.1
      simp only [one_mul] at hg
      exact (listVal_lemma49BoundaryPower Z.boundaryWord n).trans (congrArg (· ^ n) hg)
    apply List.length_pos_iff.mpr
    intro hnil
    exact Z.power_ne_one (by rw [← hval, hnil, GGT.RelLetter.listVal_nil])
  let start := (Cpower.rotation + pre.length) % power.length
  have hrotation : power.rotate start = arc ++ (suf ++ pre) := by
    dsimp only [start]
    rw [List.rotate_mod, ← List.rotate_rotate, hsplit, List.append_assoc,
      List.rotate_append_length_eq, List.append_assoc]
  exact ⟨{
    relator := K.cellLabel i
    exterior := Cpower.exterior
    remainder := Cpower.remainder
    relator_decomposition := Cpower.relator_decomposition
    relator_mem := K.cellLabel_mem i
    boundaryStart := start
    boundaryStart_le := (Nat.mod_lt _ hpowerPos).le
    boundaryArc := arc
    boundaryAfter := suf ++ pre
    boundary_rotation_decomposition := hrotation
    leftSide := Cpower.leftSide
    rightSide := Cpower.rightSide
    leftSide_admissible := Cpower.leftSide_admissible
    rightSide_admissible := Cpower.rightSide_admissible
    leftSide_short := Cpower.leftSide_short
    rightSide_short := Cpower.rightSide_short
    exterior_value := by rw [harcValue]; exact Cpower.exterior_value
    exterior_large := hlargePower }⟩

/-- The shared Greendlinger proposition supplies a based cell after rotating
a shortest power period.  This replaces the impossible blanket requirement
that every boundary contiguity have rotation zero. -/
theorem exists_rebasedLemma49Cell_of_relativeGreendlinger
    (hgeom : RelativeGreendlingerStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (mu : ℝ) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) :
    ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
      ∀ (v : List (GGT.RelLetter G Lambda)) (g : G) (n : ℕ),
        RelWord.IsLemma49Input D (RelWord.symmetrized v) eps mu rho →
        ∀ Z : Lemma49GeodesicPowerDiagram D v g n,
          IsShortestModuloConjugacy D.alphabet.carrier
            (Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)) g →
          ∃ rotated : G, ∃ Zrot : Lemma49GeodesicPowerDiagram D v rotated n,
            ∃ conjugator : G,
              rotated = conjugator⁻¹ * g * conjugator ∧
              Zrot.boundaryWord.length = Z.boundaryWord.length ∧
              IsShortestModuloConjugacy D.alphabet.carrier
                (Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)) rotated ∧
              Nonempty (Lemma49RelativeGreendlingerCell D v rotated n eps mu Zrot) := by
  obtain ⟨eps, rho0, hgood⟩ := hgeom D hemb mu hmu hmuUpper
  refine ⟨eps, rho0, ?_⟩
  intro rho hrho v g n hinput Z hshort
  obtain ⟨K⟩ := hgood rho hrho (RelWord.symmetrized v)
    (lemma49BoundaryPower Z.boundaryWord n).length
    hinput.toIsLemma44Input Z.toRelativeReducedDiagram
  obtain ⟨E⟩ := exists_lemma49ExteriorArc_of_certificate Z K
  obtain ⟨rotated, Zrot, conjugator, hconjugate, _, hword, hshortRot, C⟩ :=
    E.exists_rebasedGreendlingerCell hshort
  refine ⟨rotated, Zrot, conjugator, hconjugate, ?_, hshortRot, C⟩
  rw [hword, List.length_rotate]

end GroupApproximation.HullSC
