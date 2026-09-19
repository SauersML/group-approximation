import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaClass
import GroupApproximation.Analysis.NormalKazhdanUltraproduct
import GroupApproximation.Analysis.MaximalCStarKazhdanProjection

/-!
# Provenance for the corrected complementary corner

`PrintedCornerData` deliberately starts after the passage to coordinates.  In
particular, it does not remember the ambient corona representation, the
Kazhdan projection whose complement was cut out, or the exact corona equation
satisfied by the corrected corner maps.  This file retains precisely those
data.

The property-(T) group is a normal subgroup `K` of the ambient group `G`.
Accordingly, the corrected corner is first constructed for `G` and is then
precomposed with `K.subtype`; no property-(T) hypothesis is imposed on `G`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open PrintedCornerCompression
open KazhdanCornerMatrices
open MaximalCStarKazhdanProjection
open UltraproductKazhdanProjection

noncomputable section

/-! ## Restriction of printed corner data -/

variable {G H : Type} [Group G] [Group H]
variable {model : ℕ → FiniteModel}

/-- Precompose an ambient printed corner family with a group homomorphism.
The projection coordinates, hence also the finite corner models, are left
unchanged. -/
def printedCornerDataPrecomp (D : PrintedCornerData G model) (f : H →* G) :
    PrintedCornerData H model where
  V n h := D.V n (f h)
  q := D.q
  q_projection := D.q_projection
  q_ne_zero := D.q_ne_zero
  mul_vanishing := by
    intro g h
    simpa only [map_mul] using D.mul_vanishing (f g) (f h)
  commutator_vanishing := by
    intro g
    exact D.commutator_vanishing (f g)

@[simp] theorem printedCornerDataPrecomp_V
    (D : PrintedCornerData G model) (f : H →* G)
    (n : ℕ) (h : H) : (printedCornerDataPrecomp D f).V n h = D.V n (f h) :=
  rfl

@[simp] theorem printedCornerDataPrecomp_q
    (D : PrintedCornerData G model) (f : H →* G)
    (n : ℕ) : (printedCornerDataPrecomp D f).q n = D.q n :=
  rfl

@[simp] theorem printedCornerDataPrecomp_cornerMap
    (D : PrintedCornerData G model) (f : H →* G) (n : ℕ) (h : H) :
    (printedCornerDataPrecomp D f).cornerMap n h = D.cornerMap n (f h) :=
  rfl

@[simp] theorem ambientCornerSeq_printedCornerDataPrecomp
    (D : PrintedCornerData G model) (f : H →* G) (h : H) :
    ambientCornerSeq (printedCornerDataPrecomp D f) h =
      ambientCornerSeq D (f h) :=
  rfl

/-! ## The normal-subgroup Kazhdan projection in the ambient corona -/

variable {G : Type} [Group G]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The spectral Kazhdan data for the restriction of an ambient corona
representation to a subgroup.  The compressing element is chosen to be the
identity; `proj` depends only on the restricted representation and the
Kazhdan datum, not on this auxiliary field. -/
def normalSubgroupKazhdanCompressionData
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (K : Subgroup G) (KD : KazhdanData K) :
    KazhdanCompressionRep K G
      (NormMatrixCStarCorona (fun n ↦ X n)) where
  pi := rho
  iota := K.subtype
  s := 1
  Q := KD.S
  kappa := KD.kappa
  kazhdan := KD.kazhdan.lowerUniverse
  S := KD.S
  QS := Finset.Subset.rfl
  one_mem := KD.one_mem
  symm := KD.symm
  generates := KD.generates
  compresses := by
    intro k
    exact ⟨k, by simp⟩

/-- The smallest package that remembers where a corrected corner came from.

`cornerClass` is the exact compatibility forgotten by `PrintedCornerData`:
after restriction to the retained coordinates, the embedded polar-corrected
corner maps represent `q * rho(g)` on the nose in the corona. -/
structure CorrectedCornerProvenanceData
    (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (K : Subgroup G) where
  /-- The original ambient corona representation. -/
  rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n))
  /-- The property-(T) datum belongs to the subgroup, not the ambient group. -/
  kazhdan : KazhdanData K
  /-- The image-side spectral Kazhdan projection for `rho|K`. -/
  p : NormMatrixCStarCorona (fun n ↦ X n)
  /-- The complementary central projection used to form the corner. -/
  q : NormMatrixCStarCorona (fun n ↦ X n)
  /-- Exact provenance of `p`. -/
  p_eq : p = (normalSubgroupKazhdanCompressionData rho K kazhdan).proj
  /-- The corner projection is literally the complement of `p`. -/
  q_eq : q = 1 - p
  /-- A projection lift of `q` before coordinates are discarded. -/
  Q : BoundedMatrixSequence (fun n ↦ X n)
  /-- The retained infinite coordinate subsequence. -/
  phi : ℕ → ℕ
  phi_strictMono : StrictMono phi
  /-- The ambient corrected corner representation on the retained models. -/
  corner : PrintedCornerData G (fun n ↦ X (phi n))
  Q_projection : ∀ n, IsOrthogonalProjectionMatrix
    ((Q : ∀ n, Matrix (X n) (X n) ℂ) n)
  Q_class : normMatrixCStarCoronaMk (fun n ↦ X n) Q = q
  corner_q : ∀ n, corner.q n =
    (Q : ∀ n, Matrix (X n) (X n) ℂ) (phi n)
  /-- Exact corrected q-compression compatibility in the retained corona. -/
  cornerClass : ∀ g : G,
    normMatrixCStarCoronaMk (fun n ↦ X (phi n))
        (ambientCornerSeq corner g) =
      coronaRestrict X phi phi_strictMono
        (q * ((rho g : unitary
          (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)))

namespace CorrectedCornerProvenanceData

variable [Countable G] (K : Subgroup G)

/-- The exact corner representation on the normal property-(T) subgroup.  It
is definitionally precomposition of the ambient corner by `K.subtype`. -/
def subgroupCorner (P : CorrectedCornerProvenanceData G X K) :
    PrintedCornerData K (fun n ↦ X (P.phi n)) :=
  printedCornerDataPrecomp P.corner K.subtype

/-- The q-compression identity restricted to the property-(T) subgroup.  This
is the compatibility needed by a subgroup-level Kazhdan argument; it does not
replace `K` by the ambient group. -/
theorem subgroupCornerClass (P : CorrectedCornerProvenanceData G X K)
    (k : K) :
    normMatrixCStarCoronaMk (fun n ↦ X (P.phi n))
        (ambientCornerSeq (P.subgroupCorner K) k) =
      coronaRestrict X P.phi P.phi_strictMono
        (P.q * ((P.rho (k : G) : unitary
          (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n))) := by
  simpa [subgroupCorner] using P.cornerClass (k : G)

end CorrectedCornerProvenanceData

/-! ## Construction from the existing manuscript pipeline -/

/-- The unchanged normal-Kazhdan and central-corner pipeline constructs the
provenance-rich package.  Nonvanishing is supplied by the same represented
subgroup element used in `NK.06`; projection-zero is neither assumed nor
asserted. -/
theorem exists_correctedCornerProvenanceData
    [Countable G] (K : Subgroup G) [K.Normal]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData K) (k : K)
    (hk : ((rho (k : G) : unitary
      (NormMatrixCStarCorona (fun n ↦ X n))) :
      NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1) :
    Nonempty (CorrectedCornerProvenanceData G X K) := by
  let C : KazhdanCompressionRep K G
      (NormMatrixCStarCorona (fun n ↦ X n)) :=
    normalSubgroupKazhdanCompressionData rho K KD
  let p : NormMatrixCStarCorona (fun n ↦ X n) := C.proj
  let q : NormMatrixCStarCorona (fun n ↦ X n) := 1 - p
  have hpstar : star p = p := by
    exact C.kt_08_isSelfAdjoint_proj.star_eq
  have hpid : p * p = p := by
    exact C.kt_08_proj_mul_proj
  have hqstar : star q = q := by
    change star (1 - p) = 1 - p
    rw [star_sub, star_one, hpstar]
  have hqid : q * q = q := by
    change (1 - p) * (1 - p) = 1 - p
    rw [sub_mul, one_mul, mul_sub, mul_one, hpid, sub_self, sub_zero]
  have hCk : ((C.pi (C.iota k) : unitary
      (NormMatrixCStarCorona (fun n ↦ X n))) :
      NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1 := by
    exact hk
  have hqne : q ≠ 0 := by
    exact NormalKazhdanUltraproduct.nk_06_q_ne_zero C hCk
  have hcentral : ∀ g : G,
      ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * q =
        q * ((rho g : unitary
          (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro g
    have hg : ∀ gamma : K, ∃ delta : K,
        g * C.iota gamma * g⁻¹ = C.iota delta := by
      intro gamma
      exact ⟨⟨g * (gamma : G) * g⁻¹,
        (inferInstance : K.Normal).conj_mem (gamma : G) gamma.property g⟩, rfl⟩
    exact NormalKazhdanUltraproduct.nk_07_commute_q C g hg
  obtain ⟨phi, hphi, Q, D, hQproj, hQclass, hDq, _hDne,
      _hcard, _hmap, hclass⟩ :=
    manuscriptCornerCoronaClass G X rho q hqstar hqid hqne hcentral
  exact ⟨{
    rho := rho
    kazhdan := KD
    p := p
    q := q
    p_eq := rfl
    q_eq := rfl
    Q := Q
    phi := phi
    phi_strictMono := hphi
    corner := D
    Q_projection := hQproj
    Q_class := hQclass
    corner_q := hDq
    cornerClass := hclass }⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
