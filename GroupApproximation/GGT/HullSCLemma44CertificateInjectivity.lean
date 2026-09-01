import GroupApproximation.GGT.HullSCRelativeGreendlingerStatement
import GroupApproximation.GGT.HullSCLemma44BoundaryTransfer
import GroupApproximation.GGT.OsinTheorem54SepPolygon

/-!
# Ball injectivity from the relative Greendlinger certificate

Osin's Lemma 4.4 gives a relator cell with exterior contiguity degree at least
`1 - 23 * mu`.  This file proves the quotient consequence used in Hull's
Lemma 4.4.  The designated outer boundary is geodesic in the full relative
alphabet.  Its short boundary arc and two `eps`-side words give an upper bound
for the exposed relator prefix, while the relator's `(4,1)` quasi-geodesicity
and length floor give a conflicting lower bound.

The constants are chosen in the source order.  Fix `mu = 1/100`, obtain `eps`
and Osin's initial `rho`, and then enlarge `rho` to dominate the requested
relative radius.  Applying the result at `max R 1` gives both injection on the
original radius-`R` ball and injection on the entire peripheral union.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-- A relative Greendlinger certificate with degree at least `1 - 23 * mu`
contradicts a sufficiently short designated outer boundary.  This is the
numerical conclusion of Osin's Lemma 4.4 at quasi-geodesic constants `(4,1)`. -/
theorem false_of_relativeDiagramCertificate
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (Z : Lemma44OrientedRelatorDiagram D.alphabet W R)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    (K : RelativeDiagramCertificate D W eps mu Z) : False := by
  obtain ⟨i, C, _, hlarge⟩ := K.largeCell
  have hrelatorMem : K.cellLabel i ∈ W := K.cellLabel_mem i
  have hlongNat : rho ≤ (K.cellLabel i).length :=
    hsc.long (K.cellLabel i) hrelatorMem
  have hcoeff : (3 / 4 : ℝ) ≤ 1 - 23 * mu := by linarith
  have hrelatorNonneg : (0 : ℝ) ≤ (K.cellLabel i).length :=
    Nat.cast_nonneg _
  have hexteriorFraction :
      (3 / 4 : ℝ) * (K.cellLabel i).length ≤ C.exterior.length := by
    have hcoeffMul :
        (3 / 4 : ℝ) * (K.cellLabel i).length ≤
          (1 - 23 * mu) * (K.cellLabel i).length :=
      mul_le_mul_of_nonneg_right hcoeff hrelatorNonneg
    exact le_trans hcoeffMul hlarge
  have hlong : (rho : ℝ) ≤ (K.cellLabel i).length := by
    exact_mod_cast hlongNat
  have hexteriorLong :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) < C.exterior.length := by
    have hscale : (3 / 4 : ℝ) * (rho : ℝ) ≤
        (3 / 4 : ℝ) * (K.cellLabel i).length :=
      mul_le_mul_of_nonneg_left hlong (by norm_num)
    exact lt_of_lt_of_le hthreshold (le_trans hscale hexteriorFraction)
  have hexteriorLe : C.exterior.length ≤ (K.cellLabel i).length :=
    C.exterior_length_le_relator
  have htake : (K.cellLabel i).take C.exterior.length = C.exterior := by
    rw [C.relator_decomposition]
    simp
  have hqg := hsc.quasiGeodesic (K.cellLabel i) hrelatorMem
  have hlowerRaw := (hqg 0 C.exterior.length (Nat.zero_le _)
    hexteriorLe).1
  have hzero :
      GGT.RelLetter.listVal ((K.cellLabel i).take 0) = 1 := by
    simp [GGT.RelLetter.listVal]
  dsimp only at hlowerRaw
  rw [hzero, htake, wordDist_one_left] at hlowerRaw
  have hlower : (C.exterior.length : ℝ) / 4 - 1 ≤
      (wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal C.exterior) : ℝ) := by
    norm_num at hlowerRaw ⊢
    exact hlowerRaw
  have hleftRel : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.leftSide) ≤ eps := by
    exact le_trans
      (GGT.OsinComponents.wordNorm_listVal_le D C.leftSide
        C.leftSide_admissible) C.leftSide_short
  have hrightRel : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.rightSide) ≤ eps := by
    exact le_trans
      (GGT.OsinComponents.wordNorm_listVal_le D C.rightSide
        C.rightSide_admissible) C.rightSide_short
  have hboundaryDecomposition : Z.boundaryWord =
      C.boundaryBefore ++ C.boundaryArc ++ C.boundaryAfter := by
    rw [← K.boundaryWord_eq]
    exact C.boundary_decomposition
  have harcWord : IsWord D.alphabet.carrier
      C.boundaryArc C.boundaryArc.prod := by
    refine ⟨?_, rfl⟩
    intro x hx
    apply Z.boundaryWord_isWord.letters x
    rw [hboundaryDecomposition]
    simp only [List.mem_append]
    exact Or.inl (Or.inr hx)
  have harcLength : C.boundaryArc.length ≤ 2 * R := by
    calc
      C.boundaryArc.length ≤ Z.boundaryWord.length := by
        have hlength := congrArg List.length hboundaryDecomposition
        simp only [List.length_append] at hlength
        omega
      _ = wordNorm D.alphabet.carrier Z.boundary :=
        Z.boundaryWord_geodesic
      _ ≤ 2 * R := Z.boundary_length_le
  have harcRel : wordNorm D.alphabet.carrier C.boundaryArc.prod ≤ 2 * R :=
    le_trans (wordNorm_le_length harcWord) harcLength
  have hmulOne := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal C.leftSide) C.boundaryArc.prod
  have hmulTwo := wordNorm_mul_le D.alphabet.symmetricGenerating
    (GGT.RelLetter.listVal C.leftSide * C.boundaryArc.prod)
    (GGT.RelLetter.listVal C.rightSide)
  have hupper : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal C.exterior) ≤ 2 * R + 2 * eps := by
    rw [C.exterior_value]
    omega
  have hupperReal :
      (wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal C.exterior) : ℝ) ≤
          ((2 * R + 2 * eps : ℕ) : ℝ) := by
    exact_mod_cast hupper
  have hlowerStrict :
      ((2 * R + 2 * eps : ℕ) : ℝ) < C.exterior.length / 4 - 1 := by
    have hcast : ((2 * R + 2 * eps + 1 : ℕ) : ℝ) =
        ((2 * R + 2 * eps : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast] at hexteriorLong
    linarith
  linarith

/-- A proof of the relative Greendlinger statement supplies constants for
injectivity on an arbitrary ball of the full relative Cayley graph. -/
theorem exists_relativeBallInjectivityParameters_of_greendlinger
    (hgeom : RelativeGreendlingerStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (R : ℕ) :
    ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        {Q : Type*} [Group Q] (q : G →* Q),
        RelWord.IsLemma44Input D W eps mu rho →
        q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
          Set.InjOn q (cayleyBall D.alphabet R) := by
  let mu : ℝ := 1 / 100
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuNinetyTwo : mu ≤ 1 / 92 := by
    dsimp [mu]
    norm_num
  obtain ⟨eps, rho0, hgood⟩ := hgeom D hemb mu hmuPos hmuSixteen
  let boundaryScale : ℕ := 2 * R + 2 * eps + 1
  let rho : ℕ := max rho0 (8 * boundaryScale)
  have hrho0 : rho0 ≤ rho := Nat.le_max_left _ _
  have hrhoScale : 8 * boundaryScale ≤ rho := Nat.le_max_right _ _
  have hscalePos : (0 : ℝ) < (boundaryScale : ℝ) := by
    dsimp [boundaryScale]
    positivity
  have hrhoScaleReal : (8 : ℝ) * (boundaryScale : ℝ) ≤ (rho : ℝ) := by
    exact_mod_cast hrhoScale
  have hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ) := by
    change 4 * (boundaryScale : ℝ) < (3 / 4 : ℝ) * (rho : ℝ)
    nlinarith
  refine ⟨eps, rho, mu, hmuPos, ?_⟩
  intro W Q _ q hsc hker
  by_contra hnot
  obtain ⟨Z0⟩ := exists_lemma44ReducedRelatorDiagram_of_not_injOn
    D.alphabet W R q hker hnot
  obtain ⟨Z⟩ := Z0.exists_oriented hsc.toIsSmallCancellation
  obtain ⟨K⟩ := hgood rho hrho0 W R hsc Z
  exact false_of_relativeDiagramCertificate D Z hsc hmuNinetyTwo
    hthreshold K

/-- Relative-ball injectivity at radius `max R 1` restricts simultaneously to
the requested original ball and to the union of all peripheral subgroups. -/
theorem exists_ball_and_peripheralUnion_injectivity_of_greendlinger
    (hgeom : RelativeGreendlingerStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (A : Alphabet G) (hA : A.carrier ⊆ D.alphabet.carrier) (R : ℕ) :
    ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        {Q : Type*} [Group Q] (q : G →* Q),
        RelWord.IsLemma44Input D W eps mu rho →
        q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
          Set.InjOn q (cayleyBall A R) ∧
            Set.InjOn q (⋃ i : Lambda, (D.fam i : Set G)) := by
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    exists_relativeBallInjectivityParameters_of_greendlinger
      hgeom D hemb (max R 1)
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hsc hker
  have hinj : Set.InjOn q (cayleyBall D.alphabet (max R 1)) :=
    hgood W q hsc hker
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    apply hinj
    · apply cayleyBall_subset_of_le_radius D.alphabet (Nat.le_max_left _ _)
      exact cayleyBall_subset_of_alphabet_subset A D.alphabet hA R hx
    · apply cayleyBall_subset_of_le_radius D.alphabet (Nat.le_max_left _ _)
      exact cayleyBall_subset_of_alphabet_subset A D.alphabet hA R hy
    · exact hxy
  · apply injOn_peripheralUnion_of_injOn_cayleyBall_one D q
    intro x hx y hy hxy
    apply hinj
    · apply cayleyBall_subset_of_le_radius D.alphabet (Nat.le_max_right _ _)
      exact hx
    · apply cayleyBall_subset_of_le_radius D.alphabet (Nat.le_max_right _ _)
      exact hy
    · exact hxy

end HullSC
end GroupApproximation
