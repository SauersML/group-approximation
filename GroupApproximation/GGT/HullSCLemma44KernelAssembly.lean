import GroupApproximation.GGT.HullSCLemma44KernelGeodesic
import GroupApproximation.GGT.HullSCLemma44CertificateInjectivity

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

universe u v w

/-! ## Pointwise estimate interfaces -/

/-- The old-geodesic estimate used by Osin Lemma 5.5, specialized to Hull's
prefix family. -/
def KernelGeodesicEstimateAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : G →* Q) : Prop :=
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
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : G →* Q) : Prop :=
  ∀ (lam : Lambda) (n : ℕ),
    (((D.adjoinRelatorPrefixes W
      hsc.toIsSmallCancellation).adjoinKernel q).relBall lam n).Finite

/-- Uniform form of the old-geodesic estimate, with the exact quantifier
order used by the canonical assembly. -/
structure KernelGeodesicEstimateStatement : Prop where
  bound : ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : G →* Q)
    (_hq : Function.Surjective q)
    (_hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (_hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z)),
    KernelGeodesicEstimateAt D W eps rho mu hsc q

/-- Uniform form of the finite relative-ball estimate for the prefix kernel
cone. -/
structure KernelConeLocalFinitenessStatement : Prop where
  finite : ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : G →* Q)
    (_hq : Function.Surjective q)
    (_hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (_hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z)),
    KernelConeLocalFinitenessAt D W eps rho mu hsc q

/-! ## Fixed-parameter quotient assembly -/

/-- Certificates at one radius give injectivity on the full relative ball. -/
theorem relativeBallInjectivity_of_certificate
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type v} [Group Q] (q : G →* Q)
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

/-- The nontrivial fixed-parameter assembly. -/
theorem quotientPeripheralPreservation_of_kernelBounds_at
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D.rel W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (r : ℕ) (Z : RelativeReducedDiagram D.rel W r),
      Nonempty (RelativeDiagramCertificate D.rel W eps mu Z))
    (hkernel : KernelGeodesicEstimateStatement.{u, u, 0})
    (hloc : KernelConeLocalFinitenessStatement.{u, u, 0}) :
    Set.InjOn q (cayleyBall A.alphabet R) ∧
      Nonempty (QuotientPeripheralPreservation q D) := by
  have hAlphabet : A.alphabet.carrier ⊆ D.rel.alphabet.carrier := by
    intro x hx
    exact Set.mem_union_left _ (D.base_le hx)
  have hinject :=
    relativeBallInjectivity_of_certificate D.rel hsc hmu hthreshold q hker
      (hcert (max R 1))
  obtain ⟨M, hM⟩ := hkernel.bound D.rel W eps rho mu hsc q hq hker hcert
  have hcone :
      (D.rel.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).adjoinKernel q |>.IsHyperbolicallyEmbedded :=
    isHyperbolicallyEmbedded_prefixKernelCone_of_bounds D.rel D.embedded W
      hsc q M hM (hloc.finite D.rel W eps rho mu hsc q hq hker hcert)
  have hinjectPeripheral : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G)) := by
    intro x hx y hy hxy
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
    have hxi' : x ∈ D.rel.fam i := by
      rw [D.fam_eq i]
      exact hxi
    have hyj' : y ∈ D.rel.fam j := by
      rw [D.fam_eq j]
      exact hyj
    apply hinject
    · exact cayleyBall_subset_of_le_radius D.rel.alphabet
        (Nat.le_max_right _ _)
        (peripheralUnion_subset_cayleyBall_one D.rel
          (Set.mem_iUnion.mpr ⟨i, hxi'⟩))
    · exact cayleyBall_subset_of_le_radius D.rel.alphabet
        (Nat.le_max_right _ _)
        (peripheralUnion_subset_cayleyBall_one D.rel
          (Set.mem_iUnion.mpr ⟨j, hyj'⟩))
    · exact hxy
  have hinjectA : Set.InjOn q (cayleyBall A.alphabet R) := by
    intro x hx y hy hxy
    apply hinject
    · apply cayleyBall_subset_of_le_radius D.rel.alphabet
        (Nat.le_max_left _ _)
      exact cayleyBall_subset_of_alphabet_subset A.alphabet D.rel.alphabet
        hAlphabet R hx
    · apply cayleyBall_subset_of_le_radius D.rel.alphabet
        (Nat.le_max_left _ _)
      exact cayleyBall_subset_of_alphabet_subset A.alphabet D.rel.alphabet
        hAlphabet R hy
    · exact hxy
  have hpres : Nonempty (QuotientPeripheralPreservation q D) := by
    exact quotientPeripheralPreservation_of_prefixKernelCone D hsc q hq
      hcone hinjectPeripheral
  exact ⟨hinjectA, hpres⟩

/-! ## Empty-family model of the two estimate interfaces -/

/-- If the source and quotient are one-point groups, the kernel-geodesic
estimate is witnessed by zero. -/
theorem kernelGeodesicEstimateAt_trivialModel
    {Lambda : Type u} (D : GGT.RelGenSet PUnit Lambda)
    (W : Set (List (GGT.RelLetter PUnit Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type u} [Group Q] (q : PUnit →* Q)
    (_hq : Function.Surjective q) :
    KernelGeodesicEstimateAt D W eps rho mu hsc q := by
  haveI : Subsingleton Q :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := _hq x
      obtain ⟨b, rfl⟩ := _hq y
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
  have hwordnil : word = [] := List.length_eq_zero_iff.mp hlen
  subst word
  simp only [List.take_zero, List.prod_nil, wordDist_self]
  exact le_rfl

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

/-! The universal interfaces specialize without changing the estimate when all
types are at the base universe. -/

/-- The geodesic interface can be consumed at the one-point source model. -/
theorem kernelGeodesicEstimateStatement_at_trivialModel
    (H : KernelGeodesicEstimateStatement.{0, 0, 0})
    {Lambda : Type} (D : GGT.RelGenSet PUnit.{1} Lambda)
    (W : Set (List (GGT.RelLetter PUnit.{1} Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type} [Group Q] (q : PUnit.{1} →* Q)
    (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    KernelGeodesicEstimateAt D W eps rho mu hsc q := by
  exact H.bound D W eps rho mu hsc q hq hker hcert

/-- The local-finiteness interface can be consumed at the one-point source
model. -/
theorem kernelConeLocalFinitenessStatement_at_trivialModel
    (H : KernelConeLocalFinitenessStatement.{0, 0, 0})
    {Lambda : Type} (D : GGT.RelGenSet PUnit.{1} Lambda)
    (W : Set (List (GGT.RelLetter PUnit.{1} Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type} [Group Q] (q : PUnit.{1} →* Q)
    (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    KernelConeLocalFinitenessAt D W eps rho mu hsc q := by
  exact H.finite D W eps rho mu hsc q hq hker hcert

end HullSC
end GroupApproximation
