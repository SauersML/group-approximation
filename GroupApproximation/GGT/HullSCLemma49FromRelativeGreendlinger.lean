import GroupApproximation.GGT.HullSCLemma49Correction
import GroupApproximation.GGT.VanKampen.ContiguityCount

/-!
# Hull's Lemma 4.9 from the shared relative Greendlinger certificate

This module is the adapter between a reduced geodesic power diagram and the
single `RelativeGreendlingerStatement` shared with Hull's Lemma 4.4.  It does
not introduce a second geometric proposition.  The repeated geodesic word is
turned into the common reduced-diagram input, the selected boundary arc is
lifted back from group values to relative letters, and the two quantitative
consequences of a `(1 - 23 * mu)` exterior arc are proved.

The correction and periodic bookkeeping consumed below live in
`HullSCLemma49Correction`.  Thus the only diagrammatic object crossing this
module boundary is `RelativeDiagramCertificate`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-! ## A power diagram is a common reduced diagram -/

/-- A geodesic power diagram supplies the exact common reduced-diagram input
used by the relative Greendlinger statement.  Its radius parameter is chosen
to be the literal boundary length, so the interface's harmless `2 * R` bound
is automatic. -/
def Lemma49GeodesicPowerDiagram.toRelativeReducedDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : Lemma49GeodesicPowerDiagram D v g n) :
    RelativeReducedDiagram D (RelWord.symmetrized v)
      (lemma49BoundaryPower Z.boundaryWord n).length where
  boundaryWord :=
    (lemma49BoundaryPower Z.boundaryWord n).map GGT.RelLetter.val
  boundary := g ^ n
  boundary_ne_one := Z.power_ne_one
  boundaryWord_isWord := by
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact GGT.OsinComponents.val_mem_alphabet D
        (isAdmissible_lemma49BoundaryPower Z.boundary_geodesic.1 n a ha)
    · show GGT.RelLetter.listVal
          (lemma49BoundaryPower Z.boundaryWord n) = g ^ n
      have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
        simpa using Z.boundary_geodesic.2.1
      rw [listVal_lemma49BoundaryPower, hvalue]
  boundary_length_le := by
    rw [List.length_map]
    omega
  area := Z.area
  area_pos := Z.area_pos
  cells := Z.cells
  cells_length := by
    calc
      Z.cells.length = Z.factors.length := by
        have h := congrArg List.length Z.cell_values
        simpa only [List.length_map] using h
      _ = Z.area := Z.factors_length
  cell_values_prod := by
    rw [Z.cell_values, Z.factors_prod]
  no_cancelling_pair := Z.noCancellingCellPair

/-! ## The selected cell, with its boundary arc lifted to relative letters -/

/-- All concrete data extracted from the large cell of the shared
Greendlinger certificate.  This is data, not a new geometric hypothesis.
In particular `boundaryArc` is now a literal factor of the relative power
word, rather than merely a list of group values. -/
structure Lemma49RelativeGreendlingerCell
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (v : List (GGT.RelLetter G Lambda))
    (g : G) (n eps : ℕ) (mu : ℝ)
    (Z : Lemma49GeodesicPowerDiagram D v g n) where
  index : Fin Z.cells.length
  relator : List (GGT.RelLetter G Lambda)
  relator_eq : relator = (Z.cells.get index).relator
  relator_mem : relator ∈ RelWord.symmetrized v
  contiguity : RelativeBoundaryContiguity D eps
    ((lemma49BoundaryPower Z.boundaryWord n).map GGT.RelLetter.val) relator
  boundaryBefore : List (GGT.RelLetter G Lambda)
  boundaryArc : List (GGT.RelLetter G Lambda)
  boundaryAfter : List (GGT.RelLetter G Lambda)
  boundary_decomposition : lemma49BoundaryPower Z.boundaryWord n =
    boundaryBefore ++ boundaryArc ++ boundaryAfter
  boundaryArc_value : GGT.RelLetter.listVal boundaryArc =
    contiguity.boundaryArc.prod
  exterior_large :
    (1 - 23 * mu) * (relator.length : ℝ) ≤
      (contiguity.exterior.length : ℝ)

/-- A certificate on the common reduced diagram yields the preceding literal
power-word cell data. -/
theorem exists_lemma49RelativeGreendlingerCell
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    (Z : Lemma49GeodesicPowerDiagram D v g n)
    (K : RelativeDiagramCertificate D (RelWord.symmetrized v) eps mu
      Z.toRelativeReducedDiagram) :
    Nonempty (Lemma49RelativeGreendlingerCell D v g n eps mu Z) := by
  obtain ⟨i, C, _, hlarge⟩ := K.largeCell
  let Cpower : RelativeBoundaryContiguity D eps
      ((lemma49BoundaryPower Z.boundaryWord n).map GGT.RelLetter.val)
      (K.cellLabel i) := by
    simpa only [K.boundaryWord_eq] using C
  obtain ⟨pre, arc, suf, hsplit, _, _, _, harcValue⟩ :=
    exists_boundaryArc_source Cpower
  exact ⟨{
    index := i
    relator := K.cellLabel i
    relator_eq := K.cellLabel_eq i
    relator_mem := K.cellLabel_mem i
    contiguity := Cpower
    boundaryBefore := pre
    boundaryArc := arc
    boundaryAfter := suf
    boundary_decomposition := hsplit
    boundaryArc_value := harcValue
    exterior_large := hlarge }⟩

/-! ## Quantitative consequences of the large exterior arc -/

/-- The complement of a `(1 - 23 * mu)` exterior arc occupies at most
`23 * mu` of the relator perimeter. -/
theorem Lemma49RelativeGreendlingerCell.remainder_small
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z) :
    (C.contiguity.remainder.length : ℝ) ≤
      23 * mu * (C.relator.length : ℝ) := by
  have hlength := congrArg List.length C.contiguity.relator_decomposition
  simp only [List.length_append] at hlength
  exact GGT.VanKampen.complement_le_of_exterior_fraction hlength
    C.exterior_large

/-- The relator's `(4,1)` quasi-geodesicity and the two short connectors give
the lower bound on the opposite power-boundary arc used as equation (19) in
Osin's proof.  In the present convention `(4,1)` means
`length / 4 - 1 ≤ distance`. -/
theorem Lemma49RelativeGreendlingerCell.boundaryArc_lower
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v) eps mu rho) :
    (C.contiguity.exterior.length : ℝ) / 4 - 1 - 2 * eps ≤
      (C.boundaryArc.length : ℝ) := by
  have hrelatorAdmissible := hinput.admissible C.relator C.relator_mem
  have hexteriorAdmissible :
      RelWord.IsAdmissible D C.contiguity.exterior := by
    intro a ha
    apply hrelatorAdmissible a
    rw [C.contiguity.relator_decomposition]
    exact List.mem_append_left _ ha
  have hexteriorLe := C.contiguity.exterior_length_le_relator
  have htake : C.relator.take C.contiguity.exterior.length =
      C.contiguity.exterior := by
    rw [C.contiguity.relator_decomposition]
    exact List.take_left
  have hqg := hinput.quasiGeodesic C.relator C.relator_mem
  have hlowerRaw :=
    (hqg 0 C.contiguity.exterior.length (Nat.zero_le _) hexteriorLe).1
  have hzero : GGT.RelLetter.listVal (C.relator.take 0) = 1 := by
    simp [GGT.RelLetter.listVal]
  dsimp only at hlowerRaw
  rw [hzero, htake, wordDist_one_left] at hlowerRaw
  have hlower : (C.contiguity.exterior.length : ℝ) / 4 - 1 ≤
      (wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal C.contiguity.exterior) : ℝ) := by
    norm_num at hlowerRaw ⊢
    exact hlowerRaw
  have hleft : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.contiguity.leftSide) ≤ eps :=
    le_trans (GGT.OsinComponents.wordNorm_listVal_le D _
      C.contiguity.leftSide_admissible) C.contiguity.leftSide_short
  have hright : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.contiguity.rightSide) ≤ eps :=
    le_trans (GGT.OsinComponents.wordNorm_listVal_le D _
      C.contiguity.rightSide_admissible) C.contiguity.rightSide_short
  have harcAdmissible : RelWord.IsAdmissible D C.boundaryArc := by
    intro a ha
    apply isAdmissible_lemma49BoundaryPower Z.boundary_geodesic.1 n a
    rw [C.boundary_decomposition]
    exact List.mem_append_right _ (List.mem_append_left _ ha)
  have harc : wordNorm D.alphabet.carrier
      C.contiguity.boundaryArc.prod ≤ C.boundaryArc.length := by
    rw [← C.boundaryArc_value]
    exact GGT.OsinComponents.wordNorm_listVal_le D C.boundaryArc
      harcAdmissible
  have hmul₁ := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal C.contiguity.leftSide)
    C.contiguity.boundaryArc.prod
  have hmul₂ := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal C.contiguity.leftSide *
      C.contiguity.boundaryArc.prod)
    (GGT.RelLetter.listVal C.contiguity.rightSide)
  have hupper : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.contiguity.exterior) ≤
        2 * eps + C.boundaryArc.length := by
    rw [C.contiguity.exterior_value]
    omega
  have hupperReal :
      (wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal C.contiguity.exterior) : ℝ) ≤
      ((2 * eps + C.boundaryArc.length : ℕ) : ℝ) := by
    exact_mod_cast hupper
  push_cast at hupperReal
  linarith

/-! ## The two shortening cases at Hull's fixed constant -/

/-- At `mu = 1/1000`, taking the relator threshold one hundred times larger
than the connector scale makes the cell detour less than one third of the
opposite boundary arc.  The generous numeral keeps all later arithmetic
integral. -/
theorem Lemma49RelativeGreendlingerCell.three_mul_detourLength_lt_boundaryArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hscale : 100 * (2 * eps + 1) ≤ rho) :
    3 * (2 * eps + C.contiguity.remainder.length) < C.boundaryArc.length := by
  have hrho := hinput.long C.relator C.relator_mem
  have hrelatorScaleNat : 100 * (2 * eps + 1) ≤ C.relator.length :=
    le_trans hscale hrho
  have hrelatorScale :
      (100 : ℝ) * (2 * (eps : ℝ) + 1) ≤ (C.relator.length : ℝ) := by
    exact_mod_cast hrelatorScaleNat
  have hremainder := C.remainder_small
  have harcLower := C.boundaryArc_lower hinput
  have hexterior := C.exterior_large
  have htargetReal :
      (3 : ℝ) *
          (2 * (eps : ℝ) + (C.contiguity.remainder.length : ℝ)) <
        (C.boundaryArc.length : ℝ) := by
    norm_num at hremainder hexterior
    linarith
  exact_mod_cast htargetReal

/-- Consequently, unless the selected power arc is at least four thirds of
one period, one of the two correction lemmas contradicts quotient-conjugacy
minimality.  This packages Cases 2 and 3 of Osin's Lemma 6.3; the returned
inequality is exactly the entrance condition for the remaining prime-piece
case. -/
theorem four_mul_period_le_three_mul_arc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hscale : 100 * (2 * eps + 1) ≤ rho)
    (hshort : IsShortestModuloConjugacy D.alphabet.carrier
      (Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)) g) :
    4 * Z.boundaryWord.length ≤ 3 * C.boundaryArc.length := by
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  have hwordNe : Z.boundaryWord ≠ [] := by
    intro hnil
    have hg : g = 1 := by
      have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
        simpa using Z.boundary_geodesic.2.1
      rw [hnil] at hvalue
      simpa using hvalue.symm
    exact Z.power_ne_one (by simp [hg])
  have harcInfix : C.boundaryArc <:+:
      lemma49BoundaryPower Z.boundaryWord n :=
    ⟨C.boundaryBefore, C.boundaryAfter, C.boundary_decomposition.symm⟩
  have hrelatorAdmissible : RelWord.IsAdmissible D C.relator :=
    hinput.admissible C.relator C.relator_mem
  have hrelatorMem : GGT.RelLetter.listVal C.relator ∈ N :=
    listVal_mem_normalClosure_of_mem_symmetrized C.relator_mem
  have hdetourThird :=
    C.three_mul_detourLength_lt_boundaryArc hinput hscale
  by_contra hlong
  have harcFour : 3 * C.boundaryArc.length < 4 * Z.boundaryWord.length := by
    omega
  rcases le_total C.boundaryArc.length Z.boundaryWord.length with hshortArc | hperiod
  · exact false_of_contiguity_arc_le_period D N hshort Z.boundary_geodesic
      Z.exponent_pos harcInfix hshortArc C.contiguity hrelatorAdmissible
      hrelatorMem C.boundaryArc_value (by omega)
  · apply false_of_contiguity_period_le_arc D N hshort Z.boundary_geodesic
      Z.exponent_pos hwordNe harcInfix hperiod C.contiguity
      hrelatorAdmissible hrelatorMem C.boundaryArc_value
    omega

/-! ## Applying the one shared Greendlinger proposition -/

/-- The shared relative Greendlinger proposition supplies a large literal
cell on every nontrivial geodesic power diagram. -/
theorem exists_lemma49RelativeGreendlingerCell_of_relativeGreendlinger
    (hgeom : RelativeGreendlingerStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (mu : ℝ) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) :
    ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
      ∀ (v : List (GGT.RelLetter G Lambda))
        (g : G) (n : ℕ),
        RelWord.IsLemma49Input D (RelWord.symmetrized v) eps mu rho →
        ∀ Z : Lemma49GeodesicPowerDiagram D v g n,
          Nonempty (Lemma49RelativeGreendlingerCell D v g n eps mu Z) := by
  obtain ⟨eps, rho0, hgood⟩ := hgeom D hemb mu hmu hmuUpper
  refine ⟨eps, rho0, ?_⟩
  intro rho hrho v g n hinput Z
  obtain ⟨K⟩ := hgood rho hrho (RelWord.symmetrized v)
    (lemma49BoundaryPower Z.boundaryWord n).length
    hinput.toIsLemma44Input Z.toRelativeReducedDiagram
  exact exists_lemma49RelativeGreendlingerCell Z K

/-! ## Model check -/

/-- The selected-cell output is empty in the trivial-group nontrivial-power
branch, because such a power diagram cannot exist. -/
theorem no_lemma49PowerDiagram_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (v : List (GGT.RelLetter PUnit Lambda)) (n : ℕ) :
    IsEmpty (Lemma49GeodesicPowerDiagram D v 1 n) := by
  refine ⟨fun Z => ?_⟩
  exact Z.power_ne_one (Subsingleton.elim _ _)

end HullSC
end GroupApproximation
