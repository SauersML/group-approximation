import GroupApproximation.GGT.HullSCLemma44Canonical
import GroupApproximation.GGT.HullSCLemma44KernelGeodesic

/-!
# Canonical Hull assembly from the kernel-cone estimates

Osin's relative-presentation argument has two geometric outputs after the
certificate cut: old geodesics ending in the filling kernel are bounded in the
kernel-cone metric, and every kernel-cone relative ball is finite.  The first
output feeds the proved enlargement Lemma 5.5; the second is the properness
clause.  This file plugs those two estimates into the already proved
Greendlinger and ball-injectivity arguments.

The resulting theorem has no presentation-level placeholder.  Its two
hypotheses are pointwise estimates for the actual prefix family, with the
certificate supplied as an input to the first estimate.  A Van Kampen proof
can instantiate them independently and then use the theorem as the final
canonical quotient assembly.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u

/-! ## Pointwise estimate interfaces -/

/-- The old-geodesic estimate used by Osin Lemma 5.5, specialized to Hull's
prefix family. -/
def KernelGeodesicEstimateAt
    {G : Type u} [Group G] {Lambda : Type u}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type u} [Group Q] (q : G →* Q) : Prop :=
  ∃ M : ℕ, ∀ k ∈ q.ker,
    ∀ word : List G,
      (∀ x ∈ word,
        x ∈ (D.adjoinRelatorPrefixes W
          hsc.toIsSmallCancellation).alphabet.carrier) →
      word.prod = k →
      word.length = wordDist
        (D.adjoinRelatorPrefixes W
          hsc.toIsSmallCancellation).alphabet.carrier 1 k →
      ∀ i ≤ word.length,
        wordDist
          ((D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).adjoinKernel q).alphabet.carrier
          1 (word.take i).prod ≤ M

/-- Finiteness of every relative ball in the prefix kernel cone. -/
def KernelConeLocalFinitenessAt
    {G : Type u} [Group G] {Lambda : Type u}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type u} [Group Q] (q : G →* Q) : Prop :=
  ∀ (lam : Lambda) (n : ℕ),
    (((D.adjoinRelatorPrefixes W
      hsc.toIsSmallCancellation).adjoinKernel q).relBall lam n).Finite

/-! ## Canonical quotient assembly -/

/-- Greendlinger certificates together with the two exact kernel-cone
estimates imply Hull's canonical quotient statement. -/
theorem hullLemma44CanonicalQuotientStatement_of_greendlinger_of_kernelBounds
    (hgeom : RelativeGreendlingerStatement.{u, 0})
    (hkernel : ∀ {G : Type u} [Group G]
      {Lambda : Type u} (D : GGT.RelGenSet G Lambda)
      (W : Set (List (GGT.RelLetter G Lambda)))
      (eps rho : ℕ) (mu : ℝ)
      (hsc : RelWord.IsLemma44Input D W eps mu rho)
      {Q : Type u} [Group Q] (q : G →* Q)
      (hq : Function.Surjective q)
      (hker : q.ker =
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
      (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
        Nonempty (RelativeDiagramCertificate D W eps mu Z)),
      KernelGeodesicEstimateAt D W eps rho mu hsc q)
    (hloc : ∀ {G : Type u} [Group G]
      {Lambda : Type u} (D : GGT.RelGenSet G Lambda)
      (W : Set (List (GGT.RelLetter G Lambda)))
      (eps rho : ℕ) (mu : ℝ)
      (hsc : RelWord.IsLemma44Input D W eps mu rho)
      {Q : Type u} [Group Q] (q : G →* Q)
      (hq : Function.Surjective q)
      (hker : q.ker =
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
      (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
        Nonempty (RelativeDiagramCertificate D W eps mu Z)),
      KernelConeLocalFinitenessAt D W eps rho mu hsc q) :
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
    dsimp [mu]
    norm_num
  obtain ⟨eps, rho₀, hcertificate⟩ :=
    hgeom D.rel D.embedded mu hmuPos hmuSixteen
  let fullRadius : ℕ := max R 1
  let boundaryScale : ℕ := 2 * fullRadius + 2 * eps + 1
  let rho : ℕ := max rho₀
    (max (8 * boundaryScale) (20 * (eps + 1)))
  have hrho₀ : rho₀ ≤ rho := Nat.le_max_left _ _
  have hrhoScale : 8 * boundaryScale ≤ rho :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrhoDehn : 20 * (eps + 1) ≤ rho :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ) := by
    have hrhoScaleReal : (8 : ℝ) * (boundaryScale : ℝ) ≤
        (rho : ℝ) := by
      exact_mod_cast hrhoScale
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
  obtain ⟨M, hM⟩ := hkernel D.rel W eps rho mu hsc q hsurj hker hcert
  have hcone :
      (D.rel.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).adjoinKernel q |>.IsHyperbolicallyEmbedded :=
    isHyperbolicallyEmbedded_prefixKernelCone_of_bounds D.rel D.embedded W
      hsc q M hM (hloc D.rel W eps rho mu hsc q hsurj hker hcert)
  have hprefix :
      (D.rel.prefixQuotient W hsc.toIsSmallCancellation q hsurj).
        IsHyperbolicallyEmbedded :=
    isHyperbolicallyEmbedded_prefixQuotient_of_kernelConeTransfer
      D.rel W hsc q hsurj hcone
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
  have hpres : Nonempty (QuotientPeripheralPreservation q D) := by
    exact quotientPeripheralPreservation_of_prefixKernelCone D hsc q hsurj
      hcone hinjectCores
  exact ⟨hinject.1, hpres⟩

/-! ## Empty-family model of the two estimate interfaces -/

/-- If the source and quotient are one-point groups, the kernel-geodesic
estimate is witnessed by zero. -/
theorem kernelGeodesicEstimateAt_trivialModel
    {Lambda : Type u} (D : GGT.RelGenSet PUnit Lambda)
    (W : Set (List (GGT.RelLetter PUnit Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type u} [Group Q] (q : PUnit →* Q)
    (hq : Function.Surjective q) :
    KernelGeodesicEstimateAt D W eps rho mu hsc q := by
  haveI : Subsingleton Q :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hq x
      obtain ⟨b, rfl⟩ := hq y
      exact congrArg q (Subsingleton.elim a b)
    ⟩
  refine ⟨0, ?_⟩
  intro k hk word hword hprod hlength i hi
  have hkone : k = 1 := Subsingleton.elim _ _
  have hone : word.prod = 1 := by
    exact Subsingleton.elim _ _
  have hdist : wordDist
      (D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation).alphabet.carrier
      1 k = 0 := by
    rw [hkone, wordDist_self]
  have hlen : word.length = 0 := by
    rw [hdist] at hlength
    exact hlength
  have hi0 : i = 0 := by omega
  subst hi0
  have hwordnil : word = [] := List.length_eq_zero.mp hlen
  subst word
  simp only [List.take_zero, List.prod_nil, wordDist_self]

/-- If the source is one-point, every kernel-cone relative ball is finite. -/
theorem kernelConeLocalFinitenessAt_trivialModel
    {Lambda : Type u} (D : GGT.RelGenSet PUnit Lambda)
    (W : Set (List (GGT.RelLetter PUnit Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type u} [Group Q] (q : PUnit →* Q) :
    KernelConeLocalFinitenessAt D W eps rho mu hsc q := by
  intro lam n
  exact Set.toFinite _

end HullSC
end GroupApproximation
