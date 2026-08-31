import GroupApproximation.Analysis.QuasiRegularCompression
import GroupApproximation.Analysis.AmenableTraceGeneratorDense
import GroupApproximation.Analysis.LocallyRFByIntSchedule
import GroupApproximation.Sofic.ResidualFinitePacket
import GroupApproximation.Sofic.CyclicStack
import GroupApproximation.Sofic.SoficActionCyclicExtension

/-!
# Amenable canonical trace for a locally residually finite-by-integer group

This module is the finite-window construction behind the following statement:
if every finitely generated subgroup of `N` is residually finite, then the
canonical trace of an ambient group

`G ≃ N ⋊[α] Multiplicative ℤ`

is amenable.  Keeping the ambient group `G` in the statement is important:
the completely positive maps below are compressions of quasi-regular
representations of `G` itself, so no transport of maximal group C-star
algebras across an equivalence (and hence no universe-changing C-star
isomorphism) is needed.

The algebraic part of the construction is recorded here independently of the
analytic estimates.  A finite set in `G`, viewed at finitely many integer
levels, determines a finitely generated subgroup of `N`.  Local residual
finiteness supplies one finite quotient separating any prescribed packet in
that subgroup.  The quotient fibres, stacked over the integer levels, give a
finite set of cosets in `G`; its canonical enumeration is injective and is
therefore a valid input to `QuasiRegularCompression.compressionMap`.

There are no literature inputs or choice axioms packaged as hypotheses in
this file.  The only noncomputable choices are the standard quotient
representatives and finite-set enumerations.
-/

namespace GroupApproximation
namespace LocallyRFByIntAmenableTrace

open SemidirectProduct
open SoficIntegerExtension
open ResidualFinitePacket
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G N : Type} [Group G] [Group N]
variable (α : Multiplicative ℤ →* MulAut N)
variable (e : G ≃* (N ⋊[α] Multiplicative ℤ))

/-! ## The finite normal-coordinate window -/

/-- Local residual finiteness in the precise form used by the construction. -/
def IsLocallyResiduallyFinite (N : Type) [Group N] : Prop :=
  ∀ H : Subgroup N, H.FG → Group.ResiduallyFinite ↑H

/-- The integer coordinate of an ambient group element. -/
def height (g : G) : ℤ :=
  Multiplicative.toAdd (e g).right

@[simp] theorem height_one : height α e (1 : G) = 0 := by
  simp [height]

theorem height_mul (g h : G) :
    height α e (g * h) = height α e g + height α e h := by
  simp [height, SemidirectProduct.mul_right, toAdd_mul]

theorem height_inv (g : G) : height α e g⁻¹ = -height α e g := by
  have h : 0 = height α e g⁻¹ + height α e g := by
    simpa using height_mul α e g⁻¹ g
  linarith

/-- The normal label of `g` as seen from integer level `j`.  The minus sign is
the one forced by conjugating the normal part down from that level. -/
def normalCoordinate (j : ℤ) (g : G) : N :=
  tw α (-j) (e g).left

@[simp] theorem normalCoordinate_one (j : ℤ) :
    normalCoordinate α e j (1 : G) = 1 := by
  simp [normalCoordinate, tw]

/-- The cocycle identity for the level-dependent normal coordinate. -/
theorem normalCoordinate_mul (j : ℤ) (g h : G) :
    normalCoordinate α e j (g * h) =
      normalCoordinate α e j g *
        normalCoordinate α e (j - height α e g) h := by
  rw [normalCoordinate, map_mul, SemidirectProduct.mul_left, tw_mul]
  congr 1
  have haction : (α (e g).right) (e h).left =
      tw α (height α e g) (e h).left := by
    simp [tw, height]
  rw [haction, ← tw_add]
  congr 1
  ring

/-- At height zero the normal coordinate detects every nonidentity ambient
element, at every integer level.  Twisting is an automorphism, while height
zero says that the semidirect-product right coordinate is the identity. -/
theorem normalCoordinate_ne_one_of_height_zero {g : G} (hg : g ≠ 1)
    (hheight : height α e g = 0) (j : ℤ) :
    normalCoordinate α e j g ≠ 1 := by
  intro hcoord
  have hleft : (e g).left = 1 := by
    apply tw_injective α (-j)
    simpa only [normalCoordinate, tw, map_one] using hcoord
  have hright : (e g).right = 1 := by
    apply Multiplicative.toAdd.injective
    simpa [height] using hheight
  apply hg
  apply e.injective
  rw [map_one]
  exact SemidirectProduct.ext hleft hright

/-- All normal labels visible from a finite ambient packet at a finite set of
integer levels. -/
noncomputable def normalWindow (F : Finset G) (J : Finset ℤ) : Finset N := by
  classical
  exact J.biUnion fun j ↦ F.image (normalCoordinate α e j)

theorem normalCoordinate_mem_normalWindow {F : Finset G} {J : Finset ℤ}
    {g : G} {j : ℤ} (hg : g ∈ F) (hj : j ∈ J) :
    normalCoordinate α e j g ∈ normalWindow α e F J := by
  classical
  rw [normalWindow, Finset.mem_biUnion]
  exact ⟨j, hj, Finset.mem_image_of_mem _ hg⟩

/-- The finitely generated subgroup containing every normal label in the
window. -/
noncomputable def normalWindowSubgroup (F : Finset G) (J : Finset ℤ) :
    Subgroup N :=
  Subgroup.closure (↑(normalWindow α e F J) : Set N)

theorem normalWindow_subset_subgroup (F : Finset G) (J : Finset ℤ) :
    (↑(normalWindow α e F J) : Set N) ⊆
      (normalWindowSubgroup α e F J : Set N) :=
  Subgroup.subset_closure

theorem normalWindowSubgroup_fg (F : Finset G) (J : Finset ℤ) :
    (normalWindowSubgroup α e F J).FG := by
  classical
  exact (Subgroup.fg_iff _).mpr
    ⟨↑(normalWindow α e F J), rfl, (normalWindow α e F J).finite_toSet⟩

theorem normalWindowSubgroup_residuallyFinite
    (hN : IsLocallyResiduallyFinite N) (F : Finset G) (J : Finset ℤ) :
    Group.ResiduallyFinite ↑(normalWindowSubgroup α e F J) :=
  hN (normalWindowSubgroup α e F J) (normalWindowSubgroup_fg α e F J)

/-- The normal-coordinate window, coerced into the subgroup it generates. -/
noncomputable def normalWindowInSubgroup (F : Finset G) (J : Finset ℤ) :
    Finset (normalWindowSubgroup α e F J) := by
  classical
  exact (normalWindow α e F J).attach.map
    ⟨fun x ↦ ⟨x.1, Subgroup.subset_closure x.2⟩, by
      intro x y hxy
      apply Subtype.ext
      exact congrArg
        (fun z : normalWindowSubgroup α e F J ↦ (z : N)) hxy⟩

/-- The finite residual packet used at one stage: every visible nonidentity
normal coordinate, with no unnecessary filtering by ambient height. -/
noncomputable def nontrivialNormalWindow (F : Finset G) (J : Finset ℤ) :
    Finset (normalWindowSubgroup α e F J) := by
  classical
  exact (normalWindowInSubgroup α e F J).erase 1

theorem nontrivialNormalWindow_avoids_one (F : Finset G) (J : Finset ℤ) :
    ∀ d ∈ nontrivialNormalWindow α e F J, d ≠ 1 := by
  classical
  intro d hd
  exact (Finset.mem_erase.mp hd).1

theorem normalCoordinate_mem_nontrivialNormalWindow
    {F : Finset G} {J : Finset ℤ} {g : G} {j : ℤ}
    (hg : g ∈ F) (hj : j ∈ J) (hne : normalCoordinate α e j g ≠ 1) :
    (⟨normalCoordinate α e j g,
      normalWindow_subset_subgroup α e F J
        (normalCoordinate_mem_normalWindow α e hg hj)⟩ :
        normalWindowSubgroup α e F J) ∈
      nontrivialNormalWindow α e F J := by
  classical
  rw [nontrivialNormalWindow, Finset.mem_erase]
  constructor
  · intro hone
    exact hne (congrArg Subtype.val hone)
  · rw [normalWindowInSubgroup, Finset.mem_map]
    exact ⟨⟨normalCoordinate α e j g,
      normalCoordinate_mem_normalWindow α e hg hj⟩, by simp, rfl⟩

/-! ## Extracting one residual packet -/

/-- Local residual finiteness gives one common finite quotient for every
finite packet of nonidentity elements in a finitely generated subgroup. -/
theorem exists_packet_of_fg (hN : IsLocallyResiduallyFinite N)
    (H : Subgroup N) (hH : H.FG) (D : Finset H)
    (hD : ∀ d ∈ D, d ≠ 1) : Nonempty (Packet H D) := by
  letI : Group.ResiduallyFinite H := hN H hH
  exact ResidualFinitePacket.exists_packet D hD

theorem exists_normalWindow_packet (hN : IsLocallyResiduallyFinite N)
    (F : Finset G) (J : Finset ℤ) :
    Nonempty (Packet (normalWindowSubgroup α e F J)
      (nontrivialNormalWindow α e F J)) :=
  exists_packet_of_fg hN (normalWindowSubgroup α e F J)
    (normalWindowSubgroup_fg α e F J) (nontrivialNormalWindow α e F J)
      (nontrivialNormalWindow_avoids_one α e F J)

/-! ## The packet subgroup inside the ambient group -/

/-- The normal factor, embedded in the chosen ambient presentation. -/
def kernelEmbedding : N →* G :=
  e.symm.toMonoidHom.comp (SemidirectProduct.inl : N →* (N ⋊[α] Multiplicative ℤ))

theorem kernelEmbedding_injective :
    Function.Injective (kernelEmbedding α e) :=
  e.symm.injective.comp (SemidirectProduct.inl_injective (φ := α))

variable {H : Subgroup N} {D : Finset H}

/-- The packet kernel, viewed as a subgroup of the original ambient group. -/
def ambientPacketSubgroup (P : Packet H D) : Subgroup G :=
  P.subgroup.map ((kernelEmbedding α e).comp H.subtype)

theorem height_eq_zero_of_mem_ambientPacketSubgroup (P : Packet H D) {x : G}
    (hx : x ∈ ambientPacketSubgroup α e P) : height α e x = 0 := by
  rcases hx with ⟨m, hm, rfl⟩
  simp [height, kernelEmbedding]

/-- A representative of the quotient fibre `q` at integer level `j`, in the
ambient group. -/
noncomputable def windowRepresentative (P : Packet H D)
    (q : P.quotientModel) (j : ℤ) : G :=
  e.symm
    (SemidirectProduct.inr (Multiplicative.ofAdd j) *
      SemidirectProduct.inl ((Quotient.out q : H) : N))

/-- The corresponding point in the quasi-regular `G`-set. -/
noncomputable def windowCoset (P : Packet H D)
    (q : P.quotientModel) (j : ℤ) : G ⧸ ambientPacketSubgroup α e P :=
  QuotientGroup.mk (windowRepresentative α e P q j)

theorem height_eq_zero_of_fixed_windowCoset (P : Packet H D) (g : G)
    (q : P.quotientModel) (j : ℤ)
    (hfix : g • windowCoset α e P q j = windowCoset α e P q j) :
    height α e g = 0 := by
  change QuotientGroup.mk (g * windowRepresentative α e P q j) =
    QuotientGroup.mk (windowRepresentative α e P q j) at hfix
  have hmem :=
    (QuotientGroup.eq (s := ambientPacketSubgroup α e P)).mp hfix
  have hz := height_eq_zero_of_mem_ambientPacketSubgroup α e P hmem
  rw [height_mul, height_inv, height_mul] at hz
  linarith

theorem no_fixed_windowCoset_of_height_ne_zero (P : Packet H D) (g : G)
    (hg : height α e g ≠ 0) (q : P.quotientModel) (j : ℤ) :
    g • windowCoset α e P q j ≠ windowCoset α e P q j := by
  intro hfix
  exact hg (height_eq_zero_of_fixed_windowCoset α e P g q j hfix)

/-- At height zero, a fixed packet coset forces the visible normal coordinate
into the packet kernel. -/
theorem normalCoordinate_mem_packetSubgroup_of_fixed (P : Packet H D) (g : G)
    (q : P.quotientModel) (j : ℤ) (hg0 : height α e g = 0)
    (hdH : normalCoordinate α e j g ∈ H)
    (hfix : g • windowCoset α e P q j = windowCoset α e P q j) :
    (⟨normalCoordinate α e j g, hdH⟩ : H) ∈ P.subgroup := by
  let d : H := ⟨normalCoordinate α e j g, hdH⟩
  let w : G := windowRepresentative α e P q j
  change QuotientGroup.mk (g * w) = QuotientGroup.mk w at hfix
  have hmemb : w⁻¹ * (g * w) ∈ ambientPacketSubgroup α e P :=
    (QuotientGroup.eq (s := ambientPacketSubgroup α e P)).mp hfix.symm
  rcases hmemb with ⟨m, hm, hmap⟩
  have heg : e g = SemidirectProduct.inl (e g).left := by
    rw [CyclicStack.eq_inl_mul_tpow α (e g)]
    change Multiplicative.toAdd (e g).right = 0 at hg0
    rw [hg0]
    simp [CyclicStack.tpow]
  have hmid :
      (CyclicStack.tpow α j)⁻¹ * e g * CyclicStack.tpow α j =
        SemidirectProduct.inl (normalCoordinate α e j g) := by
    rw [heg]
    calc
      _ = CyclicStack.tpow α (-j) * SemidirectProduct.inl (e g).left *
          (CyclicStack.tpow α (-j))⁻¹ := by
            rw [CyclicStack.tpow_neg]
            group
      _ = _ := by
        rw [normalCoordinate, tw, CyclicStack.tpow,
          SemidirectProduct.inl_aut]
        group
  have hcalc : e (w⁻¹ * (g * w)) =
      SemidirectProduct.inl
        (((((Quotient.out q : H)⁻¹ * d * Quotient.out q : H)) : N)) := by
    dsimp [w, windowRepresentative]
    simp only [map_mul, map_inv, e.apply_symm_apply]
    calc
      _ = (SemidirectProduct.inl ((Quotient.out q : H) : N))⁻¹ *
          ((CyclicStack.tpow α j)⁻¹ * e g * CyclicStack.tpow α j) *
            SemidirectProduct.inl ((Quotient.out q : H) : N) := by
              simp only [CyclicStack.tpow]
              group
      _ = _ := by rw [hmid, ← map_inv, ← map_mul, ← map_mul]
  have hinl :
      (SemidirectProduct.inl ((m : H) : N) : N ⋊[α] Multiplicative ℤ) =
        SemidirectProduct.inl
          (((((Quotient.out q : H)⁻¹ * d * Quotient.out q : H)) : N)) := by
    calc
      _ = e (kernelEmbedding α e (m : H)) := by simp [kernelEmbedding]
      _ = e (w⁻¹ * (g * w)) := congrArg e hmap
      _ = _ := hcalc
  have hmval : m = (Quotient.out q : H)⁻¹ * d * Quotient.out q := by
    apply Subtype.ext
    exact SemidirectProduct.inl_injective hinl
  have hconj : (Quotient.out q : H)⁻¹ * d * Quotient.out q ∈ P.subgroup := by
    simpa [← hmval] using hm
  have hd := P.normal'.conj_mem
    ((Quotient.out q : H)⁻¹ * d * Quotient.out q) hconj
      (Quotient.out q : H)
  dsimp [d] at hd ⊢
  convert hd using 1 <;> group

/-- Fibre and integer level together determine the ambient coset.  This is the
cardinality lemma hidden by an `image`-based construction: equality of the
ambient cosets first forces equality of heights, and after cancelling the
common stable-letter power it is exactly equality in `H / P.subgroup`. -/
theorem windowCoset_pair_injective (P : Packet H D) :
    Function.Injective
      (fun x : P.quotientModel × ℤ ↦ windowCoset α e P x.1 x.2) := by
  rintro ⟨q, j⟩ ⟨r, k⟩ hcoset
  have hmem :
      (windowRepresentative α e P q j)⁻¹ * windowRepresentative α e P r k ∈
        ambientPacketSubgroup α e P :=
    (QuotientGroup.eq (s := ambientPacketSubgroup α e P)).mp hcoset
  rcases hmem with ⟨m, hm, hmap⟩
  have hright := congrArg
    (fun z : G ↦ Multiplicative.toAdd (e z).right) hmap
  have hjk : j = k := by
    simp [kernelEmbedding, windowRepresentative, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right] at hright
    omega
  subst k
  have hsemidirect := congrArg e hmap
  have hcancel :
      ((SemidirectProduct.inr (Multiplicative.ofAdd j) *
          SemidirectProduct.inl ((Quotient.out q : H) : N))⁻¹ *
        (SemidirectProduct.inr (Multiplicative.ofAdd j) *
          SemidirectProduct.inl ((Quotient.out r : H) : N)) :
            N ⋊[α] Multiplicative ℤ) =
      SemidirectProduct.inl
        ((((Quotient.out q : H)⁻¹ * Quotient.out r : H) : N)) := by
    calc
      _ = (SemidirectProduct.inl ((Quotient.out q : H) : N))⁻¹ *
          SemidirectProduct.inl ((Quotient.out r : H) : N) := by group
      _ = _ := by simp
  have hinl :
      (SemidirectProduct.inl ((m : H) : N) : N ⋊[α] Multiplicative ℤ) =
        SemidirectProduct.inl
          ((((Quotient.out q : H)⁻¹ * Quotient.out r : H) : N)) := by
    simpa [kernelEmbedding, windowRepresentative, hcancel] using hsemidirect
  have hmval : m = (Quotient.out q : H)⁻¹ * Quotient.out r := by
    apply Subtype.ext
    exact SemidirectProduct.inl_injective hinl
  have hqr : q = r := by
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
    apply (QuotientGroup.eq (s := P.subgroup)).mpr
    simpa [← hmval] using hm
  exact Prod.ext hqr rfl

/-- The exact finite model used for an `L`-level compression.  Its cardinality
is definitionally the product of the cyclic level count and the residual
quotient count. -/
@[reducible] noncomputable def cyclicWindowModel (P : Packet H D) (L : ℕ)
    [NeZero L] :
    FiniteModel :=
  ⟨ZMod L × P.quotientModel, inferInstance, inferInstance⟩

@[simp] theorem card_cyclicWindowModel (P : Packet H D) (L : ℕ) [NeZero L] :
    Fintype.card (cyclicWindowModel P L) =
      L * Fintype.card P.quotientModel := by
  simp only [cyclicWindowModel, Fintype.card_prod, ZMod.card]

/-- Direct coset coordinates for the cyclic window.  The integer
representative of a level is its `ZMod.val`. -/
@[reducible] noncomputable def cyclicWindowCoset (P : Packet H D) (L : ℕ)
    [NeZero L] :
    cyclicWindowModel P L → G ⧸ ambientPacketSubgroup α e P :=
  fun x ↦ windowCoset α e P x.2 (x.1.val : ℤ)

theorem no_fixed_cyclicWindowCoset_of_height_ne_zero (P : Packet H D)
    (L : ℕ) [NeZero L] (g : G) (hg : height α e g ≠ 0)
    (x : cyclicWindowModel P L) :
    g • cyclicWindowCoset α e P L x ≠ cyclicWindowCoset α e P L x :=
  no_fixed_windowCoset_of_height_ne_zero α e P g hg x.2 (x.1.val : ℤ)

theorem cyclicWindowCoset_injective (P : Packet H D) (L : ℕ) [NeZero L] :
    Function.Injective
      (fun x : ZMod L × P.quotientModel ↦
        windowCoset α e P x.2 (x.1.val : ℤ)) := by
  intro x y hxy
  change windowCoset α e P x.2 (x.1.val : ℤ) =
    windowCoset α e P y.2 (y.1.val : ℤ) at hxy
  have hp : (x.2, (x.1.val : ℤ)) = (y.2, (y.1.val : ℤ)) :=
    windowCoset_pair_injective α e P hxy
  have hq : x.2 = y.2 := congrArg Prod.fst hp
  have hj : (x.1.val : ℤ) = (y.1.val : ℤ) := congrArg Prod.snd hp
  exact Prod.ext (ZMod.val_injective _ (Int.ofNat_injective hj)) hq

/-- The quasi-regular compression attached to the residual packet and cyclic
level window. -/
noncomputable def windowCompression (P : Packet H D) (L : ℕ) [NeZero L] :=
  QuasiRegularCompression.compressionMap (ambientPacketSubgroup α e P)
    (cyclicWindowModel P L) (cyclicWindowCoset α e P L)

theorem windowCompression_one (P : Packet H D) (L : ℕ) [NeZero L] :
    windowCompression α e P L 1 = 1 :=
  QuasiRegularCompression.compressionMap_one (ambientPacketSubgroup α e P)
    (cyclicWindowModel P L) (cyclicWindowCoset_injective α e P L)

theorem windowCompression_completelyPositive (P : Packet H D) (L : ℕ)
    [NeZero L] :
    Quasidiagonal.IsCompletelyPositiveOnMatrices (cyclicWindowModel P L)
      ⇑(windowCompression α e P L) :=
  QuasiRegularCompression.isCompletelyPositiveOnMatrices_compressionMap
    (ambientPacketSubgroup α e P) (cyclicWindowModel P L)
      (cyclicWindowCoset α e P L)

theorem norm_windowCompression_le (P : Packet H D) (L : ℕ) [NeZero L]
    (a : MaximalGroupCStar G) :
    ‖windowCompression α e P L a‖ ≤ ‖a‖ :=
  QuasiRegularCompression.norm_compressionMap_le
    (ambientPacketSubgroup α e P) (cyclicWindowModel P L)
      (cyclicWindowCoset_injective α e P L) a

/-! ## Integer-boundary bookkeeping -/

/-- The cyclic levels where adding `q` wraps around the chosen integer
representatives.  Away from this set, `ZMod.val` agrees with honest integer
addition, which is exactly what the normal-coordinate cocycle needs. -/
abbrev boundaryLevels (L : ℕ) [NeZero L] (q : ℤ) : Finset (ZMod L) :=
  badLevels L q

theorem boundaryLevels_card_le (L : ℕ) [NeZero L] (q : ℤ) :
    (boundaryLevels L q).card ≤ 2 * q.natAbs :=
  card_badLevels_le q

theorem val_add_eq_of_not_boundary {L : ℕ} [NeZero L] {q : ℤ}
    {j : ZMod L} (hj : j ∉ boundaryLevels L q) :
    ((j + (q : ZMod L)).val : ℤ) = (j.val : ℤ) + q :=
  val_add_of_not_bad hj

/-! ## One-window escape and trace estimates -/

/-- All fibre coordinates over the cyclic wrap-around boundary. -/
noncomputable def boundaryCoordinates (P : Packet H D) (L : ℕ) [NeZero L]
    (q : ℤ) : Finset (cyclicWindowModel P L) := by
  classical
  exact boundaryLevels L q ×ˢ (Finset.univ : Finset P.quotientModel)

@[simp] theorem mem_boundaryCoordinates (P : Packet H D) (L : ℕ) [NeZero L]
    (q : ℤ) (x : cyclicWindowModel P L) :
    x ∈ boundaryCoordinates P L q ↔ x.1 ∈ boundaryLevels L q := by
  rw [boundaryCoordinates]
  simp

theorem card_boundaryCoordinates (P : Packet H D) (L : ℕ) [NeZero L]
    (q : ℤ) :
    (boundaryCoordinates P L q).card =
      (boundaryLevels L q).card * Fintype.card P.quotientModel := by
  rw [boundaryCoordinates, Finset.card_product, Finset.card_univ]

/-- A one-window escape estimate from the exact non-boundary action statement.
The premise is deliberately local: downstream code supplies the explicit
target coordinate obtained by multiplying the residual quotient label. -/
theorem escape_subset_boundary (P : Packet H D) (L : ℕ) [NeZero L] (g : G)
    (hinside : ∀ x : cyclicWindowModel P L,
      x.1 ∉ boundaryLevels L (height α e g) →
        g • cyclicWindowCoset α e P L x ∈
          Set.range (cyclicWindowCoset α e P L)) :
    QuasiRegularCompression.escape (ambientPacketSubgroup α e P)
        (cyclicWindowModel P L) (cyclicWindowCoset α e P L) g ⊆
      boundaryCoordinates P L (height α e g) := by
  intro x hx
  rw [QuasiRegularCompression.mem_escape] at hx
  by_contra hboundary
  have hxgood : x.1 ∉ boundaryLevels L (height α e g) := by
    intro hx
    exact hboundary ((mem_boundaryCoordinates P L (height α e g) x).mpr hx)
  exact hx (hinside x hxgood)

theorem card_escape_le_boundary (P : Packet H D) (L : ℕ) [NeZero L] (g : G)
    (hinside : ∀ x : cyclicWindowModel P L,
      x.1 ∉ boundaryLevels L (height α e g) →
        g • cyclicWindowCoset α e P L x ∈
          Set.range (cyclicWindowCoset α e P L)) :
    (QuasiRegularCompression.escape (ambientPacketSubgroup α e P)
        (cyclicWindowModel P L) (cyclicWindowCoset α e P L) g).card ≤
      (boundaryLevels L (height α e g)).card *
        Fintype.card P.quotientModel := by
  rw [← card_boundaryCoordinates P L (height α e g)]
  exact Finset.card_le_card (escape_subset_boundary α e P L g hinside)

/-- The generator-pair Hilbert--Schmidt defect is controlled by the boundary
escape set of the second generator. -/
theorem hsNorm_windowCompression_generatorDefect_le (P : Packet H D)
    (L : ℕ) [NeZero L] (g h : G) :
    hsNorm (cyclicWindowModel P L)
        (QuasiRegularCompression.generatorDefect (ambientPacketSubgroup α e P)
          (cyclicWindowModel P L) (cyclicWindowCoset α e P L) g h) ≤
      Real.sqrt
        ((QuasiRegularCompression.escape (ambientPacketSubgroup α e P)
          (cyclicWindowModel P L) (cyclicWindowCoset α e P L) h).card /
            (Fintype.card (cyclicWindowModel P L) : ℝ)) :=
  QuasiRegularCompression.hsNorm_generatorDefect_le_sqrt_escape
    (ambientPacketSubgroup α e P) (cyclicWindowModel P L)
      (cyclicWindowCoset_injective α e P L) g h

/-- If the selected window has no fixed coordinate for `g`, the compressed
generator has exactly the canonical trace value `0`. -/
theorem normTrace_windowCompression_generator_eq_zero (P : Packet H D)
    (L : ℕ) [NeZero L] (g : G)
    (hfix : ∀ x : cyclicWindowModel P L,
      g • cyclicWindowCoset α e P L x ≠ cyclicWindowCoset α e P L x) :
    normTrace (cyclicWindowModel P L)
        (windowCompression α e P L (maximalGroupCStarGenerator G g)) = 0 :=
  QuasiRegularCompression.normTrace_compressionMap_generator_eq_zero
    (ambientPacketSubgroup α e P) (cyclicWindowModel P L)
      (cyclicWindowCoset α e P L) g hfix

theorem normTrace_windowCompression_generator_of_height_ne_zero
    (P : Packet H D) (L : ℕ) [NeZero L] (g : G)
    (hg : height α e g ≠ 0) :
    normTrace (cyclicWindowModel P L)
        (windowCompression α e P L (maximalGroupCStarGenerator G g)) = 0 :=
  normTrace_windowCompression_generator_eq_zero α e P L g
    (no_fixed_cyclicWindowCoset_of_height_ne_zero α e P L g hg)

end

end LocallyRFByIntAmenableTrace
end GroupApproximation
