import GroupApproximation.GGT.HullSCLemma44NormalSubword
import GroupApproximation.GGT.HullSCLemma44PrefixCut
import GroupApproximation.GGT.HullSCLemma44RelativeBoundary

/-!
# Greendlinger cuts on shortest-lift triangles

For three quotient vertices, concatenate shortest source spellings of the
three oriented differences.  The resulting source word maps to a quotient
loop.  If its source value is nontrivial, a reduced relative diagram and a
Greendlinger certificate give a strictly shorter replacement of one exterior
arc.

Shortestness of every normal subword rules out an exterior arc contained in a
single side.  The selected arc must cross a triangle corner, while its image
has prefix-quotient norm at most `2 * eps + 1`.  This is the corner-crossing
dichotomy in the normal-path proof of quotient hyperbolicity.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

/-! ## The shortest-lift triangle -/

/-- The source boundary made from shortest spellings of the three oriented
quotient differences. -/
noncomputable def quotientNormalTriangleWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y z : Q) : List G :=
  (quotientNormalWord D q hq (x⁻¹ * y) ++
    quotientNormalWord D q hq (y⁻¹ * z)) ++
      quotientNormalWord D q hq (z⁻¹ * x)

/-- Every letter of the shortest-lift triangle belongs to the source
relative alphabet. -/
theorem quotientNormalTriangleWord_isWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y z : Q) :
    IsWord D.alphabet.carrier (quotientNormalTriangleWord D q hq x y z)
      (quotientNormalTriangleWord D q hq x y z).prod := by
  have hxy := quotientNormalWord.isWord D q hq (x⁻¹ * y)
  have hyz := quotientNormalWord.isWord D q hq (y⁻¹ * z)
  have hzx := quotientNormalWord.isWord D q hq (z⁻¹ * x)
  have hlegal := isWord_append (isWord_append hxy hyz) hzx
  exact ⟨hlegal.letters, rfl⟩

/-- The shortest-lift triangle closes after mapping to the quotient. -/
theorem map_prod_quotientNormalTriangleWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y z : Q) :
    q (quotientNormalTriangleWord D q hq x y z).prod = 1 := by
  simp only [quotientNormalTriangleWord, List.prod_append, map_mul]
  rw [quotientNormalWord.map_prod, quotientNormalWord.map_prod,
    quotientNormalWord.map_prod]
  group

/-! ## Arcs contained in one side -/

/-- A word occurs contiguously inside one of the three chosen normal sides. -/
def IsInsideQuotientNormalTriangleSide
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y z : Q) (arc : List G) : Prop :=
  (∃ pre suffix,
    quotientNormalWord D q hq (x⁻¹ * y) = pre ++ arc ++ suffix) ∨
  (∃ pre suffix,
    quotientNormalWord D q hq (y⁻¹ * z) = pre ++ arc ++ suffix) ∨
  (∃ pre suffix,
    quotientNormalWord D q hq (z⁻¹ * x) = pre ++ arc ++ suffix)

/-- A strictly shorter quotient-equivalent legal replacement is impossible
for an arc contained in one shortest-lift side. -/
theorem not_inside_normalTriangleSide_of_short_replacement
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y z : Q)
    {arc replacement : List G}
    (hreplacement :
      IsWord D.alphabet.carrier replacement replacement.prod)
    (hmap : q replacement.prod = q arc.prod)
    (hshort : replacement.length < arc.length) :
    ¬ IsInsideQuotientNormalTriangleSide D q hq x y z arc := by
  intro hinside
  rcases hinside with hxy | hyz | hzx
  · obtain ⟨pre, suffix, hsplit⟩ := hxy
    exact (not_length_lt_of_map_prod_eq_normalSublist
      D q hq (x⁻¹ * y) hsplit hreplacement hmap) hshort
  · obtain ⟨pre, suffix, hsplit⟩ := hyz
    exact (not_length_lt_of_map_prod_eq_normalSublist
      D q hq (y⁻¹ * z) hsplit hreplacement hmap) hshort
  · obtain ⟨pre, suffix, hsplit⟩ := hzx
    exact (not_length_lt_of_map_prod_eq_normalSublist
      D q hq (z⁻¹ * x) hsplit hreplacement hmap) hshort

/-! ## The stripped corner-cut output -/

/-- The consumer-level output of a Greendlinger certificate on a normal
triangle.  It contains no combinatorial-map data. -/
structure NormalTriangleCornerCut
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (x y z : Q) where
  boundaryBefore : List G
  boundaryArc : List G
  boundaryAfter : List G
  replacement : List G
  boundary_decomposition :
    quotientNormalTriangleWord D q hq x y z =
      boundaryBefore ++ boundaryArc ++ boundaryAfter
  replacement_isWord :
    IsWord D.alphabet.carrier replacement replacement.prod
  replacement_map : q replacement.prod = q boundaryArc.prod
  replacement_short : replacement.length < boundaryArc.length
  arc_crosses_corner :
    ¬ IsInsideQuotientNormalTriangleSide D q hq x y z boundaryArc
  shortcut :
    wordNorm
      (D.prefixQuotient W hsc.toIsSmallCancellation q hq).alphabet.carrier
      (q boundaryArc.prod) ≤ 2 * eps + 1

/-! ## Producing the corner cut -/

/-- A nontrivial source value for the shortest-lift triangle produces a
corner-crossing Greendlinger shortcut. -/
theorem exists_normalTriangleCornerCut_of_prod_ne_one
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z))
    (hrot : ∀ {boundaryWord' : List G}
      {relator' : List (GGT.RelLetter G Lambda)}
      (C : RelativeBoundaryContiguity D eps boundaryWord' relator'),
      C.rotation = 0)
    (x y z : Q)
    (hne : (quotientNormalTriangleWord D q hq x y z).prod ≠ 1) :
    Nonempty (NormalTriangleCornerCut D W hsc q hq x y z) := by
  let boundaryWord := quotientNormalTriangleWord D q hq x y z
  have hword : IsWord D.alphabet.carrier boundaryWord boundaryWord.prod :=
    quotientNormalTriangleWord_isWord D q hq x y z
  have hmap : q boundaryWord.prod = 1 :=
    map_prod_quotientNormalTriangleWord D q hq x y z
  have hnormal : boundaryWord.prod ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) :=
    mem_normalClosure_of_map_eq_one q hker hmap
  obtain ⟨Z, hZboundary⟩ := exists_relativeReducedDiagram_of_boundaryWord
    D W hsc.toIsSmallCancellation boundaryWord boundaryWord.prod hword hne
      hnormal
  obtain ⟨K⟩ := hcert boundaryWord.length Z
  obtain ⟨i, C, _hcontiguity, hshort, hshortcut⟩ :=
    RelativeBoundaryContiguity.exists_short_prefixQuotient_arc_of_certificate
      D hsc hmu hrho K q hq hker
  have hKboundary : K.boundaryWord = boundaryWord :=
    K.boundaryWord_eq.trans hZboundary
  have hboundaryDecomposition : boundaryWord =
      C.boundaryBefore ++ C.boundaryArc ++ C.boundaryAfter :=
    hKboundary.symm.trans (C.boundary_decomposition_of_rotation_zero (hrot C))
  have hrelatorAdmissible : RelWord.IsAdmissible D (K.cellLabel i) :=
    hsc.admissible (K.cellLabel i) (K.cellLabel_mem i)
  have hreplacement :
      IsWord D.alphabet.carrier C.replacementWord C.replacementWord.prod :=
    C.replacementWord_isWord hrelatorAdmissible
  have hkill : q (GGT.RelLetter.listVal (K.cellLabel i)) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact Subgroup.subset_normalClosure
      ⟨K.cellLabel i, K.cellLabel_mem i, rfl⟩
  have hreplacementMap :
      q C.replacementWord.prod = q C.boundaryArc.prod :=
    C.map_replacementWord_prod_eq_boundaryArc_prod q hkill
  have hcrosses :
      ¬ IsInsideQuotientNormalTriangleSide D q hq x y z C.boundaryArc :=
    not_inside_normalTriangleSide_of_short_replacement D q hq x y z
      hreplacement hreplacementMap hshort
  exact ⟨{
    boundaryBefore := C.boundaryBefore
    boundaryArc := C.boundaryArc
    boundaryAfter := C.boundaryAfter
    replacement := C.replacementWord
    boundary_decomposition := hboundaryDecomposition
    replacement_isWord := hreplacement
    replacement_map := hreplacementMap
    replacement_short := hshort
    arc_crosses_corner := hcrosses
    shortcut := hshortcut }⟩

/-- Every shortest-lift triangle either already closes in the source group or
admits a bounded corner-crossing shortcut. -/
theorem source_eq_one_or_normalTriangleCornerCut
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z))
    (hrot : ∀ {boundaryWord' : List G}
      {relator' : List (GGT.RelLetter G Lambda)}
      (C : RelativeBoundaryContiguity D eps boundaryWord' relator'),
      C.rotation = 0)
    (x y z : Q) :
    (quotientNormalTriangleWord D q hq x y z).prod = 1 ∨
      Nonempty (NormalTriangleCornerCut D W hsc q hq x y z) := by
  by_cases hsource :
      (quotientNormalTriangleWord D q hq x y z).prod = 1
  · exact Or.inl hsource
  · exact Or.inr (exists_normalTriangleCornerCut_of_prod_ne_one
      D hsc hmu hrho q hq hker hcert hrot x y z hsource)

end HullSC
end GroupApproximation
