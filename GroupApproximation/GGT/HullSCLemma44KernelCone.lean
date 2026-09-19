import GroupApproximation.GGT.HullSCFreeProductFactor
import GroupApproximation.GGT.HullSCLemma44PrefixGeometry
import GroupApproximation.GGT.HullSCLemma44RelativeArea
import GroupApproximation.GGT.HyperbolicAdditiveTransfer
import GroupApproximation.GGT.OsinTheorem54SeparatingCosets

/-!
# The kernel-cone transfer in Hull's Lemma 4.4

Osin's proof of Theorem 4.1 first adds the filling kernel to the source base.
The resulting Cayley graph is the source-side model for the quotient relative
Cayley graph.  A choice of lifts from the quotient changes distances by at
most one: a shortest quotient word lifts letter by letter, and one kernel
letter corrects its endpoint.

This file proves that metric comparison and its relative-metric counterpart.
An avoiding quotient path of length `n` lifts to an avoiding source path; one
final base letter in the kernel reaches a chosen peripheral lift.  Thus the
quotient relative ball is contained in the image of the kernel-cone ball of
radius `n + 1`.  Hyperbolicity and local finiteness both pass from the
kernel-coned source relative generating set to the quotient.

For Hull's unbounded relator family the source set is first enlarged by all
relator-prefix values.  The remaining geometric step is precisely
`PrefixKernelConeTransferStatement`: Osin's relative-area induction proves
that this kernel-coned prefix family is hyperbolically embedded.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

namespace RelGenSet

/-! ## Adding the kernel to the source base -/

/-- Add the kernel of a homomorphism to the base, leaving every labelled
peripheral subgroup unchanged. -/
def adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) : RelGenSet G Lambda :=
  D.adjoinSymmetricBase (q.ker : Set G)
    (fun _ hx => q.ker.inv_mem hx)

@[simp] theorem base_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) :
    (D.adjoinKernel q).base = D.base ∪ (q.ker : Set G) := rfl

@[simp] theorem fam_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (lam : Lambda) :
    (D.adjoinKernel q).fam lam = D.fam lam := rfl

/-- Every old alphabet letter remains a letter after adjoining the kernel. -/
theorem alphabet_subset_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) :
    D.alphabet.carrier ⊆ (D.adjoinKernel q).alphabet.carrier := by
  rintro x (hx | hx)
  · exact Set.mem_union_left _ (Set.mem_union_left _ hx)
  · exact Set.mem_union_right _ hx

/-! ## Group-word lifting -/

/-- A word in the image alphabet lifts letter by letter to a source word of
the same length. -/
theorem exists_sourceGroupWord_of_mapSurjective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) :
    ∀ word : List Q,
      (∀ y ∈ word, y ∈ (D.mapSurjective q hq).alphabet.carrier) →
        ∃ source : List G,
          (∀ x ∈ source, x ∈ D.alphabet.carrier) ∧
          source.map q = word ∧ source.length = word.length
  | [], _ => ⟨[], by simp, rfl, rfl⟩
  | y :: tail, hword => by
      have hy : y ∈ (D.mapSurjective q hq).alphabet.carrier :=
        hword y (by simp)
      rw [alphabet_carrier_mapSurjective] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨source, hsource, hmap, hlength⟩ :=
        exists_sourceGroupWord_of_mapSurjective D q hq tail
          (fun z hz => hword z (by simp [hz]))
      refine ⟨x :: source, ?_, ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hx
        · exact hsource z hz
      · simp only [List.map_cons, hmap]
      · simp only [List.length_cons, hlength]

/-! ## Word-metric comparison -/

/-- Mapping a kernel-cone word to the quotient never increases its word
length.  Kernel letters disappear, while all other letters map into the image
alphabet. -/
theorem wordNorm_map_le_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (g : G) :
    wordNorm (D.mapSurjective q hq).alphabet.carrier (q g) ≤
      wordNorm (D.adjoinKernel q).alphabet.carrier g := by
  obtain ⟨word, hword, hlength⟩ :=
    exists_isWord_length_eq (D.adjoinKernel q).alphabet.symmetricGenerating g
  have hletter : ∀ x ∈ (D.adjoinKernel q).alphabet.carrier,
      q x ∈ (D.mapSurjective q hq).alphabet.carrier ∨ q x = 1 := by
    intro x hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact Or.inl (Set.mem_union_left _ ⟨x, hx, rfl⟩)
      · exact Or.inr (MonoidHom.mem_ker.mp hx)
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hx
      exact Or.inl (Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨lam, ⟨x, hlam, rfl⟩⟩))
  have hle := HullSC.wordNorm_map_le_length
    (D.mapSurjective q hq).alphabet.symmetricGenerating q hletter word g hword
  rwa [hlength] at hle

/-- A shortest quotient word lifts to the source and one kernel letter fixes
its endpoint. -/
theorem wordNorm_adjoinKernel_le_map_add_one
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (g : G) :
    wordNorm (D.adjoinKernel q).alphabet.carrier g ≤
      wordNorm (D.mapSurjective q hq).alphabet.carrier (q g) + 1 := by
  obtain ⟨word, hword, hlength⟩ :=
    exists_isWord_length_eq
      (D.mapSurjective q hq).alphabet.symmetricGenerating (q g)
  obtain ⟨source, hsource, hmap, hsourceLength⟩ :=
    exists_sourceGroupWord_of_mapSurjective D q hq word hword.letters
  let k : G := g * source.prod⁻¹
  have hsourceMap : q source.prod = q g := by
    calc
      q source.prod = (source.map q).prod := map_list_prod q source
      _ = word.prod := by rw [hmap]
      _ = q g := hword.prod_eq
  have hk : k ∈ q.ker := by
    rw [MonoidHom.mem_ker]
    dsimp only [k]
    rw [map_mul, map_inv, hsourceMap]
    exact mul_inv_cancel (q g)
  have hcand : IsWord (D.adjoinKernel q).alphabet.carrier
      (k :: source) g := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Set.mem_union_left _ (Set.mem_union_right _ hk)
      · exact alphabet_subset_adjoinKernel D q (hsource x hx)
    · rw [List.prod_cons]
      dsimp only [k]
      group
  have hle := wordNorm_le_length hcand
  rw [List.length_cons, hsourceLength, hlength] at hle
  omega

/-- The quotient distance is bounded above by the kernel-cone distance. -/
theorem wordDist_map_le_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y : G) :
    wordDist (D.mapSurjective q hq).alphabet.carrier (q x) (q y) ≤
      wordDist (D.adjoinKernel q).alphabet.carrier x y := by
  unfold wordDist
  simpa only [map_mul, map_inv] using
    wordNorm_map_le_adjoinKernel D q hq (x⁻¹ * y)

/-- The kernel-cone distance is at most one more than the quotient distance. -/
theorem wordDist_adjoinKernel_le_map_add_one
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y : G) :
    wordDist (D.adjoinKernel q).alphabet.carrier x y ≤
      wordDist (D.mapSurjective q hq).alphabet.carrier (q x) (q y) + 1 := by
  unfold wordDist
  simpa only [map_mul, map_inv] using
    wordNorm_adjoinKernel_le_map_add_one D q hq (x⁻¹ * y)

/-! ## A coarse section of the quotient -/

/-- A chosen lift of each quotient element. -/
noncomputable def quotientSection
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) (y : Q) : G :=
  Classical.choose (hq y)

@[simp] theorem map_quotientSection
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) (y : Q) :
    q (quotientSection q hq y) = y :=
  Classical.choose_spec (hq y)

/-- The chosen lift map between the two Cayley spaces. -/
noncomputable def quotientSectionCayley
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) :
    Cayley (D.mapSurjective q hq).alphabet →
      Cayley (D.adjoinKernel q).alphabet :=
  fun x => Cayley.of (D.adjoinKernel q).alphabet
    (quotientSection q hq (Cayley.val x))

/-- The chosen lift changes every distance by at most one. -/
theorem quotientSectionCayley_additiveDistortion
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) :
    HasAdditiveDistortion (1 : ℝ) (quotientSectionCayley D q hq) := by
  intro x y
  let sx := quotientSection q hq (Cayley.val x)
  let sy := quotientSection q hq (Cayley.val y)
  have hlow : wordDist (D.mapSurjective q hq).alphabet.carrier
      (Cayley.val x) (Cayley.val y) ≤
      wordDist (D.adjoinKernel q).alphabet.carrier sx sy := by
    have h := wordDist_map_le_adjoinKernel D q hq sx sy
    simpa only [sx, sy, map_quotientSection] using h
  have hupp : wordDist (D.adjoinKernel q).alphabet.carrier sx sy ≤
      wordDist (D.mapSurjective q hq).alphabet.carrier
        (Cayley.val x) (Cayley.val y) + 1 := by
    have h := wordDist_adjoinKernel_le_map_add_one D q hq sx sy
    simpa only [sx, sy, map_quotientSection] using h
  have hlowReal :
      (wordDist (D.mapSurjective q hq).alphabet.carrier
        (Cayley.val x) (Cayley.val y) : ℝ) ≤
      (wordDist (D.adjoinKernel q).alphabet.carrier sx sy : ℝ) := by
    exact_mod_cast hlow
  have huppReal :
      (wordDist (D.adjoinKernel q).alphabet.carrier sx sy : ℝ) ≤
      (wordDist (D.mapSurjective q hq).alphabet.carrier
        (Cayley.val x) (Cayley.val y) : ℝ) + 1 := by
    exact_mod_cast hupp
  simp only [quotientSectionCayley, Cayley.dist_eq, Cayley.val_of]
  change |(wordDist (D.adjoinKernel q).alphabet.carrier sx sy : ℝ) -
      (wordDist (D.mapSurjective q hq).alphabet.carrier
        (Cayley.val x) (Cayley.val y) : ℝ)| ≤ 1
  rw [abs_of_nonneg (sub_nonneg.mpr hlowReal)]
  linarith

/-! ## Avoiding paths and relative balls -/

/-- If the mapped source word avoids a quotient peripheral copy, then the
source word avoids the corresponding source copy. -/
theorem avoidsFrom_mapHom_imp
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (lam : Lambda) :
    ∀ (word : List (RelLetter G Lambda)) (v : G),
      AvoidsFrom (fun i => (D.fam i).map q) lam
        (word.map (RelLetter.mapHom q)) (q v) →
      AvoidsFrom D.fam lam word v := by
  intro word
  induction word with
  | nil => intro v h; exact h
  | cons a tail ih =>
      intro v h
      simp only [List.map_cons, AvoidsFrom, RelLetter.isCompOf_mapHom,
        RelLetter.val_mapHom] at h ⊢
      refine ⟨?_, ?_⟩
      · rintro ⟨ha, hv⟩
        exact h.1 ⟨ha, ⟨v, hv, rfl⟩⟩
      · have ht := h.2
        rw [← map_mul] at ht
        exact ih (v * a.val) ht

/-- Every quotient relative ball is contained in the image of a radius-one
larger relative ball for the kernel-coned source family. -/
theorem relBall_mapSurjective_subset_image_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (lam : Lambda) (n : ℕ) :
    (D.mapSurjective q hq).relBall lam n ⊆
      q '' (D.adjoinKernel q).relBall lam (n + 1) := by
  rintro y ⟨hyFam, word, hword, hvalue, havoid, hlength⟩
  obtain ⟨h, hhFam, hqh⟩ := hyFam
  obtain ⟨source, hsource, hmap, hsourceLength⟩ :=
    exists_sourceWord_of_admissible_mapSurjective D q hq word hword
  have hqSource : q (RelLetter.listVal source) = y := by
    calc
      q (RelLetter.listVal source) = RelLetter.listVal word :=
        map_listVal_sourceWord q hmap
      _ = y := hvalue
  have havoidMapped : AvoidsFrom (fun i => (D.fam i).map q) lam
      (source.map (RelLetter.mapHom q)) (q 1) := by
    rw [map_one, hmap]
    exact havoid
  have havoidSource : AvoidsFrom D.fam lam source 1 :=
    avoidsFrom_mapHom_imp D q lam source 1 havoidMapped
  let k : G := (RelLetter.listVal source)⁻¹ * h
  have hk : k ∈ q.ker := by
    rw [MonoidHom.mem_ker]
    dsimp only [k]
    rw [map_mul, map_inv, hqSource, hqh]
    exact inv_mul_cancel y
  refine ⟨h, ?_, hqh⟩
  refine ⟨hhFam, source ++ [RelLetter.base k], ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · cases a with
      | base x => exact Set.mem_union_left _ (hsource _ ha)
      | comp i x => exact hsource _ ha
    · have haeq : a = RelLetter.base k := List.eq_of_mem_singleton ha
      rw [haeq]
      exact Set.mem_union_right _ hk
  · rw [GGT.OsinComponents.listVal_append,
      GGT.OsinComponents.listVal_singleton]
    simp only [RelLetter.val]
    dsimp only [k]
    group
  · rw [GGT.OsinComponents.avoidsFrom_append]
    refine ⟨havoidSource, ?_⟩
    simp [AvoidsFrom, RelLetter.IsCompOf]
  · rw [List.length_append, List.length_singleton, hsourceLength]
    omega

/-! ## Transfer of hyperbolically embeddedness -/

/-- Hyperbolicity passes from the kernel-coned source Cayley graph to the
quotient Cayley graph. -/
theorem exists_hyperbolic_mapSurjective_of_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q)
    (hhyper : ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (D.adjoinKernel q).alphabet)) :
    ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (D.mapSurjective q hq).alphabet) := by
  obtain ⟨delta, hdelta⟩ := hhyper
  refine ⟨delta + 3, ?_⟩
  simpa only [mul_one] using
    (isHyperbolicSpace_of_additiveDistortion
      (quotientSectionCayley_additiveDistortion D q hq) hdelta)

/-- Local finiteness passes from kernel-cone relative balls to quotient
relative balls. -/
theorem locallyFinite_mapSurjective_of_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q)
    (hloc : ∀ (lam : Lambda) (n : ℕ),
      ((D.adjoinKernel q).relBall lam n).Finite) :
    ∀ (lam : Lambda) (n : ℕ),
      ((D.mapSurjective q hq).relBall lam n).Finite := by
  intro lam n
  exact ((hloc lam (n + 1)).image q).subset
    (relBall_mapSurjective_subset_image_adjoinKernel D q hq lam n)

/-- Hyperbolically embeddedness of the kernel-coned source family implies
hyperbolically embeddedness of its quotient image family. -/
theorem isHyperbolicallyEmbedded_mapSurjective_of_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q)
    (hcone : (D.adjoinKernel q).IsHyperbolicallyEmbedded) :
    (D.mapSurjective q hq).IsHyperbolicallyEmbedded :=
  ⟨exists_hyperbolic_mapSurjective_of_adjoinKernel D q hq
      hcone.hyperbolic,
    locallyFinite_mapSurjective_of_adjoinKernel D q hq
      hcone.locallyFinite⟩

end RelGenSet
end GGT

namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## The prefix-kernel geometric input -/

/-- The pointwise geometric conclusion of Osin's relative-area induction for
the triangular prefix presentation. -/
def PrefixKernelConeTransferAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) : Prop :=
  ∀ (W : Set (List (GGT.RelLetter G Lambda))) (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : G →* Q) (_ : Function.Surjective q),
      RelativeLinearKernelArea D W q →
        GGT.RelGenSet.IsHyperbolicallyEmbedded
          ((D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).adjoinKernel q)

/-- Uniform prefix-kernel transfer over every hyperbolically embedded source
family.  This is the kernel-coned form of Osin's Theorem 4.1 and Lemma 5.1. -/
def PrefixKernelConeTransferStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded → PrefixKernelConeTransferAt.{u, v, w} D

/-- A prefix-kernel transfer gives hyperbolically embeddedness of the concrete
prefix quotient family. -/
theorem isHyperbolicallyEmbedded_prefixQuotient_of_kernelConeTransfer
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (hcone : GGT.RelGenSet.IsHyperbolicallyEmbedded
      ((D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).adjoinKernel q)) :
    GGT.RelGenSet.IsHyperbolicallyEmbedded
      (D.prefixQuotient W hsc.toIsSmallCancellation q hq) := by
  exact GGT.RelGenSet.isHyperbolicallyEmbedded_mapSurjective_of_adjoinKernel
    (D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation) q hq hcone

/-- A hyperbolically embedded prefix kernel cone and injectivity on the
selected peripheral union give Hull's preservation object. -/
theorem quotientPeripheralPreservation_of_prefixKernelCone
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S)
    {W : Set (List
      (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D.rel W eps mu rho)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hcone : GGT.RelGenSet.IsHyperbolicallyEmbedded
      ((D.rel.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).adjoinKernel q))
    (hinj : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G))) :
    Nonempty (QuotientPeripheralPreservation q D) := by
  refine ⟨{
    rel := D.rel.prefixQuotient W hsc.toIsSmallCancellation q hq
    base_image := ?_
    fam_map := ?_
    embedded := isHyperbolicallyEmbedded_prefixQuotient_of_kernelConeTransfer
      D.rel W hsc q hq hcone
    injOn_peripheralUnion := hinj }⟩
  · intro a ha
    exact D.rel.map_mem_prefixQuotient_base W hsc.toIsSmallCancellation
      q hq ha
  · intro i
    rw [GGT.RelGenSet.fam_prefixQuotient, D.fam_eq i]

/-! ## Model test -/

/-- Every relative generating set on the one-point group is hyperbolically
embedded. -/
theorem isHyperbolicallyEmbedded_trivialGroup
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    D.IsHyperbolicallyEmbedded := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · intro base x y z
    have hxy : x = y := by
      change Cayley.val x = Cayley.val y
      exact Subsingleton.elim _ _
    have hyz : y = z := by
      change Cayley.val y = Cayley.val z
      exact Subsingleton.elim _ _
    have hbase : base = z := by
      change Cayley.val base = Cayley.val z
      exact Subsingleton.elim _ _
    subst x
    subst y
    subst base
    simp only [gromovProduct, dist_self, zero_add, sub_zero, min_self]
    norm_num
  · intro lam n
    exact Set.toFinite _

/-- The prefix-kernel transfer has its full quantifier order on the one-point
source group, including arbitrary relator families and quotient universes. -/
theorem prefixKernelConeTransferAt_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    PrefixKernelConeTransferAt.{0, v, w} D := by
  intro W eps rho mu hsc Q _ q _ harea
  exact isHyperbolicallyEmbedded_trivialGroup
    ((D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation).adjoinKernel q)

end HullSC
end GroupApproximation
