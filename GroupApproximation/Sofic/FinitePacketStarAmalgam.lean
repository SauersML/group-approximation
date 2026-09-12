import GroupApproximation.Sofic.FinitePacketFullCollapse
import GroupApproximation.Sofic.MarkedCompressionGroup
import Mathlib.GroupTheory.PushoutI

/-!
# The star-permutation packet in an ascending-HNN amalgam

For an injective endomorphism `alpha : Gamma -> Gamma` with finite-index
image, this file constructs the finite permutation packet on the cosets of
`alpha(Gamma)` together with one fixed point.  It then adjoins that packet to
`Gamma` by the coset action and amalgamates the result with the mapping-
telescope model of the ascending HNN extension.

The final theorem applies `FinitePacketFullCollapse` directly.  Thus the
packet representations, covariance corrections, rank normalization,
Delorme primitive, scaled transport, and terminal integral-rank collapse are
all conclusions; none is supplied as a structure field.
-/

namespace GroupApproximation
namespace FinitePacketStarAmalgam

open Monoid SemidirectProduct MarkedCompression

noncomputable section

variable {Gamma : Type} [Group Gamma]
variable (alpha : Gamma →* Gamma) (halpha : Function.Injective alpha)

/-- The coset packet sites, with one additional fixed point. -/
abbrev Sites : Type := (Gamma ⧸ alpha.range) ⊕ Unit

noncomputable instance [alpha.range.FiniteIndex] : Fintype (Sites alpha) :=
  Fintype.ofFinite _

/-- `Gamma` acts on the coset sites and fixes the additional point. -/
noncomputable def siteAction : Gamma →* Equiv.Perm (Sites alpha) where
  toFun g := Equiv.sumCongr (MulAction.toPerm g) (Equiv.refl Unit)
  map_one' := by
    ext x
    cases x <;> simp
  map_mul' g h := by
    ext x
    cases x <;> simp [mul_smul]

/-- The finite noncommutative packet. -/
abbrev Packet : Type := Equiv.Perm (Sites alpha)

/-- Relabel packet permutations by the coset action. -/
noncomputable def packetAction : Gamma →* MulAut (Packet alpha) where
  toFun g := MulAut.conj (siteAction alpha g)
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [MulAut.conj_apply, mul_assoc]

/-- The packet host `Sym(Sites) semidirect Gamma`. -/
abbrev Host : Type :=
  SemidirectProduct (Packet alpha) Gamma (packetAction alpha)

/-- The packet subgroup of the host. -/
noncomputable def packetInHost : Packet alpha →* Host alpha := inl

/-- The base group inside the packet host. -/
noncomputable def baseInHost : Gamma →* Host alpha := inr

/-- The base coset. -/
noncomputable def root : Sites alpha :=
  Sum.inl (QuotientGroup.mk (1 : Gamma))

/-- The extra fixed point. -/
noncomputable def star : Sites alpha := Sum.inr ()

local instance sitesDecidableEq : DecidableEq (Sites alpha) :=
  Classical.decEq _

/-- The star transposition based at the coset of `g`. -/
noncomputable def orbit (g : Gamma) : Packet alpha :=
  Equiv.swap (Sum.inl (QuotientGroup.mk g)) (star alpha)

/-- Relabelling a star transposition translates its coset. -/
theorem packetAction_orbit (a g : Gamma) :
    packetAction alpha a (orbit alpha g) = orbit alpha (a * g) := by
  classical
  change MulAut.conj (siteAction alpha a) (orbit alpha g) = orbit alpha (a * g)
  unfold orbit
  rw [MulAut.conj_apply, ← Equiv.swap_apply_apply]
  congr 1

/-- Every star transposition is an involution. -/
theorem orbit_sq (g : Gamma) : orbit alpha g * orbit alpha g = 1 := by
  classical
  unfold orbit
  exact Equiv.swap_mul_self
    (Sum.inl (QuotientGroup.mk g) : Sites alpha) (star alpha)

/-- Two star transpositions satisfy the braid relation. -/
theorem orbit_braid (a : Gamma) :
    orbit alpha a * orbit alpha 1 * orbit alpha a =
      orbit alpha 1 * orbit alpha a * orbit alpha 1 := by
  classical
  by_cases h : (QuotientGroup.mk a : Gamma ⧸ alpha.range) =
      QuotientGroup.mk 1
  · unfold orbit
    rw [h]
  · let A : Sites alpha := Sum.inl (QuotientGroup.mk a)
    let R : Sites alpha := Sum.inl (QuotientGroup.mk (1 : Gamma))
    let z : Sites alpha := star alpha
    have hRA : R ≠ A := by
      intro h'
      apply h
      exact Sum.inl_injective h'.symm
    have hRz : R ≠ z := by simp [R, z, star]
    have hAz : A ≠ z := by simp [A, z, star]
    have hleft : Equiv.swap A z * Equiv.swap R z * Equiv.swap A z =
        Equiv.swap A R := by
      rw [Equiv.swap_comm A z]
      exact Equiv.swap_mul_swap_mul_swap hRz hRA
    have hright : Equiv.swap R z * Equiv.swap A z * Equiv.swap R z =
        Equiv.swap A R := by
      rw [Equiv.swap_comm R z, Equiv.swap_mul_swap_mul_swap hAz hRA.symm,
        Equiv.swap_comm R A]
    change Equiv.swap A z * Equiv.swap R z * Equiv.swap A z =
      Equiv.swap R z * Equiv.swap A z * Equiv.swap R z
    exact hleft.trans hright.symm

/-- Elements of the compressed image give the base star transposition. -/
theorem orbit_alpha (g : Gamma) : orbit alpha (alpha g) = orbit alpha 1 := by
  classical
  unfold orbit
  apply congrArg (fun x : Gamma ⧸ alpha.range ↦
    Equiv.swap (Sum.inl x) (star alpha))
  apply QuotientGroup.eq.mpr
  simp

/-- Packet covariance inside the semidirect-product host. -/
theorem host_covariance (a : Gamma) (f : Packet alpha) :
    baseInHost alpha a * packetInHost alpha f * (baseInHost alpha a)⁻¹ =
      packetInHost alpha (packetAction alpha a f) := by
  rw [baseInHost, packetInHost, ← map_inv, ← inl_aut]

/-! ## The amalgam with the ascending HNN extension -/

/-- The two factors of the concrete amalgam. -/
abbrev Factor : Bool → Type
  | false => Host alpha
  | true => Vertical alpha halpha

noncomputable instance : ∀ b, Group (Factor alpha halpha b)
  | false => inferInstanceAs (Group (Host alpha))
  | true => inferInstanceAs (Group (Vertical alpha halpha))

/-- The common base group in the two factors. -/
noncomputable def edge : ∀ b, Gamma →* Factor alpha halpha b
  | false => baseInHost alpha
  | true => iotaVertical alpha halpha

/-- The packet/HNN amalgam. -/
abbrev Carrier : Type := PushoutI (edge alpha halpha)

/-- The packet in the amalgam. -/
noncomputable def packet : Packet alpha →* Carrier alpha halpha :=
  (PushoutI.of (φ := edge alpha halpha) false).comp (packetInHost alpha)

/-- The common base copy in the amalgam. -/
noncomputable def iota : Gamma →* Carrier alpha halpha :=
  PushoutI.base (edge alpha halpha)

/-- The stable letter from the ascending-HNN factor. -/
noncomputable def stable : Carrier alpha halpha :=
  PushoutI.of (φ := edge alpha halpha) true (tVertical alpha halpha)

theorem iota_eq_host (g : Gamma) :
    iota alpha halpha g =
      PushoutI.of (φ := edge alpha halpha) false (baseInHost alpha g) := by
  exact (PushoutI.of_apply_eq_base (edge alpha halpha) false g).symm

theorem iota_eq_vertical (g : Gamma) :
    iota alpha halpha g =
      PushoutI.of (φ := edge alpha halpha) true
        (iotaVertical alpha halpha g) := by
  exact (PushoutI.of_apply_eq_base (edge alpha halpha) true g).symm

/-- Packet covariance survives in the amalgam. -/
theorem covariance (a : Gamma) (f : Packet alpha) :
    iota alpha halpha a * packet alpha halpha f * (iota alpha halpha a)⁻¹ =
      packet alpha halpha (packetAction alpha a f) := by
  rw [iota_eq_host]
  change
    PushoutI.of (φ := edge alpha halpha) false
        (baseInHost alpha a) *
      PushoutI.of (φ := edge alpha halpha) false
        (packetInHost alpha f) *
      (PushoutI.of (φ := edge alpha halpha) false
        (baseInHost alpha a))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, host_covariance]
  rfl

/-- The stable letter compresses the common base copy by `alpha`. -/
theorem compresses (g : Gamma) :
    stable alpha halpha * iota alpha halpha g * (stable alpha halpha)⁻¹ =
      iota alpha halpha (alpha g) := by
  rw [iota_eq_vertical, iota_eq_vertical]
  change
    PushoutI.of (φ := edge alpha halpha) true (tVertical alpha halpha) *
      PushoutI.of (φ := edge alpha halpha) true
        (iotaVertical alpha halpha g) *
      (PushoutI.of (φ := edge alpha halpha) true
        (tVertical alpha halpha))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, vertical_compress]

/-- The concrete conclusion returned by the full finite-packet collapse
theorem. -/
def CoordinateCollapse (B : OpAlmostRepresentation (Carrier alpha halpha)) : Prop :=
  ∃ S : Finset Gamma,
    WordMetric.IsSymmetricGeneratingSet (S : Set Gamma) ∧
    ∃ V : ∀ n, Packet alpha →* Matrix.unitaryGroup (B.model n) ℂ,
      ∃ Uhat : ↥S → ∀ n, Matrix.unitaryGroup (B.model n) ℂ,
        ∃ phi : ℕ → ℕ,
          (∀ j, j ≤ phi j) ∧
          (∀ f, QuotientGroup.mk (fun n ↦ V n f) =
            (OpAlmostRepresentation.coronaHom B) (packet alpha halpha f)) ∧
          (∀ a : ↥S, (QuotientGroup.mk (Uhat a) :
            NormMatrixCoronaUnitary B.model) =
              ((OpAlmostRepresentation.coronaHom B)
                (iota alpha halpha (a : Gamma)) :
                  NormMatrixCoronaUnitary B.model)) ∧
          (∀ n a f, Uhat a n * V n f * (Uhat a n)⁻¹ =
            V n (packetAction alpha (a : Gamma) f)) ∧
          ∃ N, ∀ j ≥ N, ∀ a ∈ S,
            V (phi j) (orbit alpha a) = V (phi j) (orbit alpha 1)

/-- **Premise-free analytic endpoint for the star-packet amalgam.**  Property
`(T)` supplies the finite symmetric generating set; every other datum is the
canonical one constructed above. -/
theorem coordinateCollapse
    [alpha.range.FiniteIndex]
    (hT : HasKazhdanPropertyT.{0, 0} Gamma)
    (B : OpAlmostRepresentation (Carrier alpha halpha)) :
    CoordinateCollapse alpha halpha B := by
  classical
  obtain ⟨S, _epsilon, _hone, hsymm, hclosure, _hpos, _hle, _hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  have hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Gamma) :=
    ⟨fun x hx ↦ Finset.mem_coe.mpr
      (hsymm x (Finset.mem_coe.mp hx)), hclosure⟩
  refine ⟨S, hgen, ?_⟩
  exact FinitePacketFullCollapse.exists_cofinal_exact_packet_collapse
    B (packet alpha halpha) (iota alpha halpha) (orbit alpha) S hgen hT
    (fun a ↦ packetAction alpha (a : Gamma))
    (fun a f ↦ covariance alpha halpha (a : Gamma) f)
    (fun a g ↦ packetAction_orbit alpha (a : Gamma) g)
    (stable alpha halpha) alpha (compresses alpha halpha)
    (fun a _ ↦ orbit_alpha alpha a) (orbit_sq alpha)
    (fun a _ ↦ orbit_braid alpha a)

end

end FinitePacketStarAmalgam
end GroupApproximation
