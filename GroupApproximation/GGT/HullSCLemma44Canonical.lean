import GroupApproximation.GGT.HullSCLemma44CertificateInjectivity
import GroupApproximation.GGT.HullSCLemma44RelativeIsoperimetric
import GroupApproximation.GGT.HullSCCanonicalQuotientPublished

/-!
# Hull Lemma 4.4 from relative Greendlinger and isoperimetry

This file combines the two diagram consequences used in Hull's Lemma 4.4.
The relative Greendlinger certificate rules out a nonidentity kernel element
with short relative length.  The relative-isoperimetric induction gives
hyperbolic embeddedness of the image peripheral family.  Applying the short
kernel argument at radius `max R 1` gives both injectivity on the requested
original Cayley ball and injectivity on the whole peripheral union.

The parameter order follows Hull's Lemma 4.4 and Osin's Lemma 5.1.  We fix
`mu = 1/1000`, obtain `eps` and the initial `rho` from relative Greendlinger,
and then enlarge `rho` after the requested radius is known.  This value of
`mu` is below both `1/92`, used by the exterior-arc contradiction, and the
`1/1000` range of the relative-isoperimetric bridge.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- Fixed-parameter relative-ball injectivity from a certificate for every
least-area reduced diagram at the selected radius. -/
theorem injOn_relativeBall_of_relativeDiagramCertificates
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ Z : RelativeReducedDiagram D W R,
      Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    Set.InjOn q (cayleyBall D.alphabet R) := by
  by_contra hnot
  obtain ⟨Z₀⟩ := exists_lemma44ReducedRelatorDiagram_of_not_injOn
    D.alphabet W R q hker hnot
  obtain ⟨Z⟩ := Z₀.exists_oriented hsc.toIsSmallCancellation
  obtain ⟨K⟩ := hcert (Z.toRelativeReducedDiagram D)
  exact false_of_relativeDiagramCertificate D Z hsc hmu hthreshold K

/-- Injectivity on one full-relative ball restricts to an original-alphabet
ball and, at radius at least one, to the complete peripheral union. -/
theorem injOn_ball_and_peripheralUnion_of_relativeDiagramCertificates
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (A : Alphabet G)
    (hA : A.carrier ⊆ D.alphabet.carrier)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ Z : RelativeReducedDiagram D W (max R 1),
      Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    Set.InjOn q (cayleyBall A R) ∧
      Set.InjOn q (⋃ i : Lambda, (D.fam i : Set G)) := by
  have hinj : Set.InjOn q (cayleyBall D.alphabet (max R 1)) :=
    injOn_relativeBall_of_relativeDiagramCertificates D hsc hmu
      hthreshold q hker hcert
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    apply hinj
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_left R 1)
      exact cayleyBall_subset_of_alphabet_subset A D.alphabet hA R hx
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_left R 1)
      exact cayleyBall_subset_of_alphabet_subset A D.alphabet hA R hy
    · exact hxy
  · apply injOn_peripheralUnion_of_injOn_cayleyBall_one D q
    intro x hx y hy hxy
    apply hinj
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_right R 1)
      exact hx
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_right R 1)
      exact hy
    · exact hxy

/-- At fixed parameters, the isoperimetric bridge turns the all-diagram
certificate into Hull's peripheral-preservation object.  The union-injectivity
hypothesis is supplied independently by the radius-one part of the short
kernel argument. -/
theorem quotientPeripheralPreservation_of_relativeDiagramCertificates
    (hbridge : RelativeIsoperimetricBridgeStatement.{u, u, w})
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S)
    {eps rho : ℕ} {mu : ℝ}
    {W : Set (List
      (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho)
    (hsc : RelWord.IsLemma44Input D.rel W eps mu rho)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (r : ℕ) (Z : RelativeReducedDiagram D.rel W r),
      Nonempty (RelativeDiagramCertificate D.rel W eps mu Z))
    (hinj : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G))) :
    Nonempty (QuotientPeripheralPreservation q D) := by
  obtain ⟨C⟩ := hbridge D.rel D.embedded eps rho mu W q hq
    hmu hmuUpper hrho hsc hker hcert
  exact quotientPeripheralPreservation_of_isoperimetricControl D q hq C hinj

/-- The certificate theorem and Osin's relative-isoperimetric bridge imply
Hull's exact canonical quotient statement. -/
theorem hullLemma44CanonicalQuotientStatement_of_greendlinger_of_isoperimetric
    (hgeom : RelativeGreendlingerStatement.{u, w})
    (hbridge : RelativeIsoperimetricBridgeStatement.{u, u, w}) :
    HullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S D R
  let mu : ℝ := 1 / 1000
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuNinetyTwo : mu ≤ 1 / 92 := by
    dsimp [mu]
    norm_num
  have hmuThousand : mu ≤ 1 / 1000 := by
    exact le_rfl
  obtain ⟨eps, rho₀, hcertificate⟩ :=
    hgeom D.rel D.embedded mu hmuPos hmuSixteen
  let fullRadius : ℕ := max R 1
  let boundaryScale : ℕ := 2 * fullRadius + 2 * eps + 1
  let rho : ℕ := max rho₀ (max (8 * boundaryScale) (20 * (eps + 1)))
  have hrho₀ : rho₀ ≤ rho := Nat.le_max_left _ _
  have hrhoScale : 8 * boundaryScale ≤ rho :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrhoDehn : 20 * (eps + 1) ≤ rho :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hscalePos : (0 : ℝ) < (boundaryScale : ℝ) := by
    dsimp [boundaryScale, fullRadius]
    positivity
  have hrhoScaleReal :
      (8 : ℝ) * (boundaryScale : ℝ) ≤ (rho : ℝ) := by
    exact_mod_cast hrhoScale
  have hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ) := by
    change 4 * (boundaryScale : ℝ) < (3 / 4 : ℝ) * (rho : ℝ)
    nlinarith
  refine ⟨eps, rho, mu, hmuPos, ?_⟩
  intro W Q _ q hsc hsurj hker
  have hcert : ∀ (r : ℕ) (Z : RelativeReducedDiagram D.rel W r),
      Nonempty (RelativeDiagramCertificate D.rel W eps mu Z) := by
    intro r Z
    exact hcertificate rho hrho₀ W r hsc Z
  have hAlphabet : A.alphabet.carrier ⊆ D.rel.alphabet.carrier := by
    intro x hx
    exact Set.mem_union_left _ (D.base_le hx)
  have hinject :=
    injOn_ball_and_peripheralUnion_of_relativeDiagramCertificates
      D.rel A.alphabet hAlphabet hsc hmuNinetyTwo hthreshold q hker
        (hcert (max R 1))
  have hinjectCores : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G)) := by
    intro x hx y hy hxy
    apply hinject.2
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [D.fam_eq i]
      exact hi
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [D.fam_eq i]
      exact hi
    · exact hxy
  refine ⟨hinject.1, ?_⟩
  exact quotientPeripheralPreservation_of_relativeDiagramCertificates
    hbridge D q hsurj hmuPos hmuThousand hrhoDehn hsc hker hcert
      hinjectCores

/-- The same two geometric inputs also imply the older
peripheral-preservation-only formulation of Hull Lemma 4.4. -/
theorem hullLemma44PreservedPeripheralFamily_of_greendlinger_of_isoperimetric
    (hgeom : RelativeGreendlingerStatement.{u, w})
    (hbridge : RelativeIsoperimetricBridgeStatement.{u, u, w}) :
    HullLemma44PreservedPeripheralFamily.{u} := by
  have hcanonical : HullLemma44CanonicalQuotientStatement.{u} :=
    hullLemma44CanonicalQuotientStatement_of_greendlinger_of_isoperimetric
      hgeom hbridge
  intro G _ A N k S D
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hcanonical D 0
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hsc hsurj hker
  exact (hgood W q hsc hsurj hker).2

/-- Universe-zero specialization used by the manuscript's
`hullLemma44Canonical` declaration. -/
theorem hullLemma44CanonicalQuotientStatement_zero
    (hgeom : RelativeGreendlingerStatement.{0, 0})
    (hbridge : RelativeIsoperimetricBridgeStatement.{0, 0, 0}) :
    HullLemma44CanonicalQuotientStatement.{0} :=
  hullLemma44CanonicalQuotientStatement_of_greendlinger_of_isoperimetric
    hgeom hbridge

/-- Form using Osin Lemma 5.1's local Dehn transfer directly. -/
theorem hullLemma44CanonicalQuotientStatement_of_greendlinger_of_dehnTransfer
    (hgeom : RelativeGreendlingerStatement.{u, w})
    (htransfer : RelativeDehnTransferStatement.{u, u, w}) :
    HullLemma44CanonicalQuotientStatement.{u} :=
  hullLemma44CanonicalQuotientStatement_of_greendlinger_of_isoperimetric
    hgeom (relativeIsoperimetricBridgeStatement_of_dehnTransfer htransfer)

/-- Universe-zero form with the two source lemmas separated. -/
theorem hullLemma44CanonicalQuotientStatement_zero_of_dehnTransfer
    (hgeom : RelativeGreendlingerStatement.{0, 0})
    (htransfer : RelativeDehnTransferStatement.{0, 0, 0}) :
    HullLemma44CanonicalQuotientStatement.{0} :=
  hullLemma44CanonicalQuotientStatement_of_greendlinger_of_dehnTransfer
    hgeom htransfer

end HullSC
end GroupApproximation
