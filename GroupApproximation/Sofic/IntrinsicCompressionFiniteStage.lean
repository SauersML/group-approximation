import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Sofic.MarkedCompressionRootCapture

/-!
# Intrinsic compression by finite-stage Kazhdan corners

This file proves the choice-free compression--centralizer obstruction by the
same finite-stage spectral argument used for the marked obstruction.  For a
fixed operator-norm almost representation, the elements whose adjoint
microstates asymptotically preserve the Kazhdan spectral projection form a
subgroup.  The equal-rank two-projection argument puts every one-sided
compressor in that subgroup, hence also the group they generate.
-/

namespace GroupApproximation
namespace IntrinsicCompressionFiniteStage

open Filter Matrix KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator commutatorElement

variable {H : Type} [Group H]

/-- The canonical compression core attached to a one-sided compressor of
`L`.  The root is the identity; only the spectral projection and its
equal-rank translate are used. -/
def compressorCore (L : Subgroup H) (hT : HasKazhdanPropertyT.{0, 0} L)
    (s : H) (hs : s ∈ compressionSet L) : KazhdanCompressionCore L H where
  iota := L.subtype
  t := s
  c := 1
  kazhdan := hT
  compresses := by
    intro ell
    exact ⟨⟨s * ell * s⁻¹, hs ell ell.property⟩, rfl⟩
  comm_c := fun _ ↦ Commute.one_left _

@[simp]
theorem compressorCore_iota (L : Subgroup H)
    (hT : HasKazhdanPropertyT.{0, 0} L) (s : H)
    (hs : s ∈ compressionSet L) (ell : L) :
    (compressorCore L hT s hs).iota ell = ell :=
  rfl

@[simp]
theorem compressorCore_t (L : Subgroup H)
    (hT : HasKazhdanPropertyT.{0, 0} L) (s : H)
    (hs : s ∈ compressionSet L) :
    (compressorCore L hT s hs).t = s :=
  rfl

/-- The compression core used to capture a centralizer element.  Its
compressor is the identity; later transport by an arbitrary generated
compressor is handled separately by the common spectral projection. -/
def centralizerCore (L : Subgroup H)
    (hT : HasKazhdanPropertyT.{0, 0} L) (z : H)
    (hz : ∀ ell ∈ L, Commute z ell) : KazhdanCompressionCore L H where
  iota := L.subtype
  t := 1
  c := z
  kazhdan := hT
  compresses := fun ell ↦ ⟨ell, by simp⟩
  comm_c := fun ell ↦ hz ell ell.property

@[simp]
theorem centralizerCore_iota (L : Subgroup H)
    (hT : HasKazhdanPropertyT.{0, 0} L) (z : H)
    (hz : ∀ ell ∈ L, Commute z ell) (ell : L) :
    (centralizerCore L hT z hz).iota ell = ell :=
  rfl

/-- The finite Kazhdan data used for every compressor of `L`. -/
structure SpectralData (L : Subgroup H)
    (hT : HasKazhdanPropertyT.{0, 0} L) where
  S : Finset L
  kappa : ℝ
  one_mem : 1 ∈ S
  symmetric : ∀ g ∈ S, g⁻¹ ∈ S
  generates : Subgroup.closure (S : Set L) = ⊤
  kappa_pos : 0 < kappa
  kappa_le_one : kappa ≤ 1
  kazhdan : IsKazhdanPair.{0, 0} L S kappa
  theta : ℝ
  gap_lt_theta : 1 - kappa ^ 2 / (4 * S.card) < theta
  theta_lt_one : theta < 1

/-- Property `(T)` supplies one spectral cutoff, shared by all compressors. -/
theorem exists_spectralData (L : Subgroup H)
    (hT : HasKazhdanPropertyT.{0, 0} L) : Nonempty (SpectralData L hT) := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, hkappa, hkappaOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hgap : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) :=
    div_pos (sq_pos_of_pos hkappa) (mul_pos (by norm_num) hcard)
  let c0 : ℝ := 1 - kappa ^ 2 / (4 * S.card)
  let theta : ℝ := (c0 + 1) / 2
  exact ⟨{
    S := S
    kappa := kappa
    one_mem := hone
    symmetric := hsymm
    generates := hgen
    kappa_pos := hkappa
    kappa_le_one := hkappaOne
    kazhdan := hpair
    theta := theta
    gap_lt_theta := by dsimp [c0, theta]; linarith
    theta_lt_one := by dsimp [c0, theta]; linarith }⟩

/-- The Kazhdan spectral projection, independent of the chosen compressor. -/
noncomputable def spectralProjection (B : OpAlmostRepresentation H)
    {L : Subgroup H} {hT : HasKazhdanPropertyT.{0, 0} L}
    (D : SpectralData L hT) (n : ℕ) :
    Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
  spectralAbove
    (hermitianAverage (B.adjoint.comap L.subtype) D.S n)
    (hermitianAverage_conjTranspose (B.adjoint.comap L.subtype) D.S n)
    D.theta

/-- An ambient element asymptotically preserves the finite-stage Kazhdan
projection under adjoint conjugation. -/
def PreservesSpectralProjection (B : OpAlmostRepresentation H)
    {L : Subgroup H} {hT : HasKazhdanPropertyT.{0, 0} L}
    (D : SpectralData L hT) (g : H) : Prop :=
  OpNormVanishing B.adjoint (fun n ↦
    (B.adjoint.map n g : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
      spectralProjection B D n *
      (B.adjoint.map n g : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ -
    spectralProjection B D n)

/-- Every one-sided compressor preserves the common Kazhdan spectral
projection.  This is exactly the finite-stage equal-rank reversal. -/
theorem compressor_preservesSpectralProjection
    (B : OpAlmostRepresentation H)
    {L : Subgroup H} (hT : HasKazhdanPropertyT.{0, 0} L)
    (D : SpectralData L hT) {s : H} (hs : s ∈ compressionSet L) :
    PreservesSpectralProjection B D s := by
  let C := compressorCore L hT s hs
  have hleft := one_sub_moved_mul_corner_vanishing
    B C D.theta D.kazhdan D.one_mem D.kappa_le_one D.symmetric D.generates
      D.gap_lt_theta D.theta_lt_one
  have hright := one_sub_corner_mul_moved_vanishing
    B C D.theta D.kazhdan D.one_mem D.kappa_le_one D.symmetric D.generates
      D.gap_lt_theta D.theta_lt_one
  intro epsilon hepsilon
  obtain ⟨Nleft, hNleft⟩ := hleft (epsilon / 2) (by linarith)
  obtain ⟨Nright, hNright⟩ := hright (epsilon / 2) (by linarith)
  refine ⟨max Nleft Nright, fun n hn ↦ ?_⟩
  have hproj := norm_proj_sub_le
    (movedProjection_isOrthogonalProjection B C D.S D.theta n)
    (cornerProjection_isOrthogonalProjection B C D.S D.theta n)
  change ‖movedProjection B C D.S D.theta n -
    cornerProjection B C D.S D.theta n‖ ≤ epsilon
  calc
    _ ≤ ‖(1 - cornerProjection B C D.S D.theta n) *
          movedProjection B C D.S D.theta n‖ +
        ‖(1 - movedProjection B C D.S D.theta n) *
          cornerProjection B C D.S D.theta n‖ := hproj
    _ ≤ epsilon / 2 + epsilon / 2 := add_le_add
      (hNright n ((le_max_right _ _).trans hn))
      (hNleft n ((le_max_left _ _).trans hn))
    _ = epsilon := by ring

/-- Preservation of the common spectral projection gives the reverse
off-diagonal estimate consumed by the transported-vector bound. -/
theorem one_sub_spectralProjection_mul_conjugate_vanishing
    (B : OpAlmostRepresentation H)
    {L : Subgroup H} {hT : HasKazhdanPropertyT.{0, 0} L}
    (D : SpectralData L hT) {g : H}
    (hg : PreservesSpectralProjection B D g) :
    OpNormVanishing B.adjoint (fun n ↦
      (1 - spectralProjection B D n) *
        ((B.adjoint.map n g :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
          spectralProjection B D n *
          (B.adjoint.map n g :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ)) := by
  have hmul : OpNormVanishing B.adjoint (fun n ↦
      (1 - spectralProjection B D n) *
        ((B.adjoint.map n g :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
          spectralProjection B D n *
          (B.adjoint.map n g :
            Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ -
          spectralProjection B D n)) := by
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := hg (epsilon / 2) (by linarith)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hP : ‖spectralProjection B D n‖ ≤ 1 :=
      norm_spectralAbove_le_one _ _ _
    calc
      ‖(1 - spectralProjection B D n) * _‖ ≤
          ‖1 - spectralProjection B D n‖ * ‖_‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ 2 * (epsilon / 2) := by
        gcongr
        · calc
            ‖1 - spectralProjection B D n‖ ≤
                ‖(1 : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)‖ +
                  ‖spectralProjection B D n‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := add_le_add (by
                  -- the identity is the permutation matrix of `1`, and a
                  -- permutation matrix has l2-operator norm at most one; the
                  -- bound holds on an empty index type too, where it is zero
                  have h1 : (1 : Matrix (B.adjoint.model n).carrier
                        (B.adjoint.model n).carrier ℂ)
                      = (1 : Equiv.Perm (B.adjoint.model n).carrier).permMatrix ℂ :=
                    Matrix.permMatrix_one.symm
                  rw [h1]
                  exact Matrix.permMatrix_l2_opNorm_le _) hP
            _ = 2 := by norm_num
        · exact hN n hn
      _ = epsilon := by ring
  exact hmul.congr fun n ↦ by
    have hP := (spectralAbove_isOrthogonalProjection
      (hermitianAverage (B.adjoint.comap L.subtype) D.S n)
      (hermitianAverage_conjTranspose
        (B.adjoint.comap L.subtype) D.S n) D.theta).2
    change spectralProjection B D n * spectralProjection B D n =
      spectralProjection B D n at hP
    rw [Matrix.mul_sub]
    change (1 - spectralProjection B D n) * _ -
      (1 - spectralProjection B D n) * spectralProjection B D n = _
    rw [show (1 - spectralProjection B D n) * spectralProjection B D n = 0 by
      rw [Matrix.sub_mul, one_mul, hP, sub_self]]
    rw [sub_zero]

/-- Spectral-projection preservation is stable under replacing the adjoint
microstate of a word by another operator-norm asymptotic lift. -/
theorem preservesSpectralProjection_of_map_sub_vanishing
    (B : OpAlmostRepresentation H)
    {L : Subgroup H} {hT : HasKazhdanPropertyT.{0, 0} L}
    (D : SpectralData L hT) {g : H}
    (W : ∀ n, Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)
    (hWunitary : ∀ n, W n ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ)
    (hW : OpNormVanishing B.adjoint (fun n ↦
      W n - (B.adjoint.map n g :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)))
    (hpres : OpNormVanishing B.adjoint (fun n ↦
      W n * spectralProjection B D n * (W n)ᴴ -
        spectralProjection B D n)) :
    PreservesSpectralProjection B D g := by
  have hWstar : OpNormVanishing B.adjoint (fun n ↦
      (W n)ᴴ -
        (B.adjoint.map n g :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ) := by
    exact (KazhdanCompressorCorner.OpNormVanishing.conjT hW).congr fun n ↦ by
      rw [Matrix.conjTranspose_sub]
  have hnormP : ∀ n, ‖spectralProjection B D n‖ ≤ 1 := fun n ↦
    norm_spectralAbove_le_one _ _ _
  have hnormW : ∀ n, ‖W n‖ ≤ 1 := fun n ↦
    norm_le_one_of_mem_unitary (hWunitary n)
  have hnormMap : ∀ n,
      ‖(B.adjoint.map n g :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)‖ ≤ 1 := fun n ↦
    norm_le_one_of_mem_unitary (B.adjoint.map n g).2
  have hleft := (hW.mul_right_of_norm_le_one _ hnormP).mul_right_of_norm_le_one
    (fun n ↦ (W n)ᴴ)
    (fun n ↦ by rw [← Matrix.star_eq_conjTranspose, norm_star]; exact hnormW n)
  have hright := hWstar.mul_left_of_norm_le_one
    (fun n ↦ (B.adjoint.map n g :
      Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        spectralProjection B D n)
    (fun n ↦ (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_one₀ (hnormMap n) (norm_nonneg _) (hnormP n)))
  exact ((hleft.add hright).neg.add hpres).congr fun n ↦ by
    noncomm_ring

/-- The elements preserving the finite-stage Kazhdan projection form a
subgroup.  This is the finite-stage replacement for a stabilizer of an exact
fixed-vector space. -/
noncomputable def spectralProjectionStabilizer (B : OpAlmostRepresentation H)
    {L : Subgroup H} {hT : HasKazhdanPropertyT.{0, 0} L}
    (D : SpectralData L hT) : Subgroup H where
  carrier := {g | PreservesSpectralProjection B D g}
  one_mem' := by
    apply preservesSpectralProjection_of_map_sub_vanishing B D
      (fun _ ↦ (1 : Matrix (B.adjoint.model _) (B.adjoint.model _) ℂ))
      (fun _ ↦ one_mem _)
    · exact (map_one_vanishing B.adjoint).neg.congr fun n ↦ by abel
    · exact (opNormVanishing_zero B.adjoint).congr fun n ↦ by
        simp only [Matrix.one_mul, Matrix.mul_one,
          Matrix.conjTranspose_one, sub_self]
  mul_mem' := by
    intro g h hg hh
    let W : ∀ n, Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ := fun n ↦
      (B.adjoint.map n g : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ) *
        B.adjoint.map n h
    have hWunitary : ∀ n, W n ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ :=
      fun n ↦ mul_mem (B.adjoint.map n g).2 (B.adjoint.map n h).2
    have hW : OpNormVanishing B.adjoint (fun n ↦
        W n - (B.adjoint.map n (g * h) :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)) :=
      (multiplicativeDefect_vanishing B.adjoint g h).neg.congr fun n ↦ by
        rw [neg_sub]
    apply preservesSpectralProjection_of_map_sub_vanishing B D W hWunitary hW
    have hnormMapG : ∀ n,
        ‖(B.adjoint.map n g :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)‖ ≤ 1 := fun n ↦
      norm_le_one_of_mem_unitary (B.adjoint.map n g).2
    have hconj := hh.mul_left_of_norm_le_one
      (fun n ↦ (B.adjoint.map n g :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)) hnormMapG
    have hconj' := hconj.mul_right_of_norm_le_one
      (fun n ↦ (B.adjoint.map n g :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ)
      (fun n ↦ by
        rw [← Matrix.star_eq_conjTranspose, norm_star]
        exact hnormMapG n)
    exact (hconj'.add hg).congr fun n ↦ by
      simp only [W, Matrix.conjTranspose_mul]
      noncomm_ring
  inv_mem' := by
    intro g hg
    let W : ∀ n, Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ := fun n ↦
      (B.adjoint.map n g : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)ᴴ
    have hWunitary : ∀ n, W n ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ := by
      intro n
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact Unitary.star_mul_self_of_mem (B.adjoint.map n g).2
    have hW : OpNormVanishing B.adjoint (fun n ↦
        W n - (B.adjoint.map n g⁻¹ :
          Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ)) :=
      (map_inv_vanishing B.adjoint g).neg.congr fun n ↦ by rw [neg_sub]
    apply preservesSpectralProjection_of_map_sub_vanishing B D W hWunitary hW
    have hnormW : ∀ n, ‖W n‖ ≤ 1 := fun n ↦
      norm_le_one_of_mem_unitary (hWunitary n)
    have hconj := hg.mul_left_of_norm_le_one W hnormW
    have hconj' := hconj.mul_right_of_norm_le_one
      (fun n ↦ (B.adjoint.map n g :
        Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ))
      (fun n ↦ norm_le_one_of_mem_unitary (B.adjoint.map n g).2)
    exact hconj'.neg.congr fun n ↦ by
      let U : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
        B.adjoint.map n g
      let P : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
        spectralProjection B D n
      have hUstarU : Uᴴ * U = 1 :=
        Unitary.star_mul_self_of_mem (B.adjoint.map n g).2
      have hfirst : Uᴴ * (U * P * Uᴴ) * U = P := by
        calc
          Uᴴ * (U * P * Uᴴ) * U = (Uᴴ * U) * P * (Uᴴ * U) := by
            noncomm_ring
          _ = P := by rw [hUstarU, Matrix.one_mul, Matrix.mul_one]
      simp only [W]
      rw [Matrix.conjTranspose_conjTranspose]
      change -(Uᴴ * (U * P * Uᴴ - P) * U) = Uᴴ * P * U - P
      rw [Matrix.mul_sub, Matrix.sub_mul, hfirst]
      abel

/-- Every element generated by one-sided compressors preserves the common
finite-stage Kazhdan projection. -/
theorem compressionGroup_preservesSpectralProjection
    (B : OpAlmostRepresentation H)
    {L : Subgroup H} (hT : HasKazhdanPropertyT.{0, 0} L)
    (D : SpectralData L hT) :
    compressionGroup L ≤ spectralProjectionStabilizer B D := by
  rw [compressionGroup, Subgroup.closure_le]
  intro s hs
  exact compressor_preservesSpectralProjection B hT D hs

/-! ## Functoriality of the intrinsic defect -/

variable {K : Type} [Group K]

/-- Homomorphisms carry one-sided compressors to one-sided compressors of
the mapped subgroup. -/
theorem map_mem_compressionSet (f : H →* K) (L : Subgroup H)
    {s : H} (hs : s ∈ compressionSet L) :
    f s ∈ compressionSet (L.map f) := by
  intro ell hell
  rcases hell with ⟨delta, hdelta, rfl⟩
  rw [← map_mul, ← map_inv, ← map_mul]
  exact ⟨s * delta * s⁻¹, hs delta hdelta, rfl⟩

/-- The subgroup generated by compressors maps into the compressor subgroup
of the image. -/
theorem map_mem_compressionGroup (f : H →* K) (L : Subgroup H)
    {g : H} (hg : g ∈ compressionGroup L) :
    f g ∈ compressionGroup (L.map f) := by
  apply (show compressionGroup L ≤
      (compressionGroup (L.map f)).comap f from ?_) hg
  rw [compressionGroup, Subgroup.closure_le]
  intro s hs
  exact Subgroup.subset_closure (map_mem_compressionSet f L hs)

/-- The intrinsic compression--centralizer defect is covariant under group
homomorphisms. -/
theorem map_compressionCentralizerDefect_le (f : H →* K)
    (L : Subgroup H) :
    (compressionCentralizerDefect L).map f ≤
      compressionCentralizerDefect (L.map f) := by
  rintro _ ⟨x, hx, rfl⟩
  apply (show compressionCentralizerDefect L ≤
      (compressionCentralizerDefect (L.map f)).comap f from ?_) hx
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨g, hg, z, hz, ell, hell, rfl⟩
  change f ⁅g * z * g⁻¹, ell⁆ ∈ compressionCentralizerDefect (L.map f)
  rw [map_commutatorElement, map_mul, map_mul, map_inv]
  apply compressionCentralizerDefect_generator_mem (L.map f)
    (map_mem_compressionGroup f L hg)
  · intro delta hdelta
    rcases hdelta with ⟨d, hd, rfl⟩
    exact (hz d hd).map f
  · exact ⟨ell, hell, rfl⟩

end IntrinsicCompressionFiniteStage
end GroupApproximation
