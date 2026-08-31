import GroupApproximation.Analysis.LocallyRFByIntAmenableTrace

/-!
# Exact finite-window action for locally RF-by-integer groups

This file supplies the algebraic action formulas used by the finite-window
amenable-trace construction.  Translation adds the integer height and left
multiplies the residual quotient label by the normal coordinate visible at
the new level.  Away from cyclic wrap-around this is an exact action inside
the selected window.  At height zero, residual separation rules out fixed
coordinates for every tested nonidentity element.
-/

namespace GroupApproximation
namespace LocallyRFByIntAmenableTrace

open SemidirectProduct SoficIntegerExtension ResidualFinitePacket
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G N : Type} [Group G] [Group N]
variable (α : Multiplicative ℤ →* MulAut N)
variable (e : G ≃* (N ⋊[α] Multiplicative ℤ))
variable {H : Subgroup N} {D : Finset H}

/-! ## Exact action on an integer fibre -/

/-- Left translation of an integer-level coset adds the ambient height and
multiplies its residual label by the normal coordinate at the new level. -/
theorem smul_windowCoset (P : Packet H D) (g : G) (q : P.quotientModel)
    (j : ℤ)
    (hdH : normalCoordinate α e (j + height α e g) g ∈ H) :
    g • windowCoset α e P q j =
      windowCoset α e P
        (P.quotientMap
          (⟨normalCoordinate α e (j + height α e g) g, hdH⟩ : H) * q)
        (j + height α e g) := by
  let m : ℤ := height α e g
  let d : H := ⟨normalCoordinate α e (j + m) g, by simpa [m] using hdH⟩
  let q' : P.quotientModel := P.quotientMap d * q
  have hlevel :
      e g * SemidirectProduct.inr (Multiplicative.ofAdd j) =
        SemidirectProduct.inr (Multiplicative.ofAdd (j + m)) *
          SemidirectProduct.inl (normalCoordinate α e (j + m) g) := by
    apply SemidirectProduct.ext
    · have hcancel :
          (α (Multiplicative.ofAdd (j + m)))
              (normalCoordinate α e (j + m) g) = (e g).left := by
        rw [normalCoordinate, tw]
        rw [← MulAut.mul_apply, ← map_mul]
        simp [← ofAdd_add]
      simpa [SemidirectProduct.mul_left] using hcancel.symm
    · have hegright : (e g).right = Multiplicative.ofAdd m := by
        apply Multiplicative.toAdd.injective
        simp [m, height]
      simp [SemidirectProduct.mul_right, hegright, ← ofAdd_add, add_comm]
  have hrep :
      e (g * windowRepresentative α e P q j) =
        SemidirectProduct.inr (Multiplicative.ofAdd (j + m)) *
          SemidirectProduct.inl (((d * Quotient.out q : H) : N)) := by
    calc
      _ = e g *
          (SemidirectProduct.inr (Multiplicative.ofAdd j) *
            SemidirectProduct.inl ((Quotient.out q : H) : N)) := by
              simp [windowRepresentative]
      _ = (e g * SemidirectProduct.inr (Multiplicative.ofAdd j)) *
          SemidirectProduct.inl ((Quotient.out q : H) : N) := by group
      _ = (SemidirectProduct.inr (Multiplicative.ofAdd (j + m)) *
            SemidirectProduct.inl ((d : H) : N)) *
          SemidirectProduct.inl ((Quotient.out q : H) : N) := by rw [hlevel]
      _ = _ := by
        rw [mul_assoc]
        congr 2
        simp
  let k : H := (d * Quotient.out q)⁻¹ * Quotient.out q'
  have hk : k ∈ P.subgroup := by
    apply (QuotientGroup.eq_one_iff k).mp
    change P.quotientMap k = 1
    simp [k, q']
  change QuotientGroup.mk (g * windowRepresentative α e P q j) =
    QuotientGroup.mk (windowRepresentative α e P q' (j + m))
  apply (QuotientGroup.eq (s := ambientPacketSubgroup α e P)).mpr
  refine ⟨k, hk, ?_⟩
  apply e.injective
  have htarget :
      e (windowRepresentative α e P q' (j + m)) =
        SemidirectProduct.inr (Multiplicative.ofAdd (j + m)) *
          SemidirectProduct.inl ((Quotient.out q' : H) : N) := by
    simp [windowRepresentative]
  change e (kernelEmbedding α e ((k : H) : N)) =
    e ((g * windowRepresentative α e P q j)⁻¹ *
      windowRepresentative α e P q' (j + m))
  rw [map_mul, map_inv, hrep, htarget]
  change e (e.symm (SemidirectProduct.inl ((k : H) : N))) = _
  rw [e.apply_symm_apply]
  dsimp [k]
  simp only [map_mul, map_inv]
  group

/-! ## Cyclic level windows -/

/-- The honest integer representatives of a cyclic window of length `L`. -/
noncomputable def levelWindow (L : ℕ) : Finset ℤ := by
  classical
  exact (Finset.range L).image (fun n : ℕ ↦ (n : ℤ))

/-- Every canonical `ZMod L` representative belongs to the honest level
window. -/
theorem zmod_val_mem_levelWindow (L : ℕ) [NeZero L] (j : ZMod L) :
    (j.val : ℤ) ∈ levelWindow L := by
  classical
  rw [levelWindow, Finset.mem_image]
  exact ⟨j.val, Finset.mem_range.mpr (ZMod.val_lt j), rfl⟩

/-- Away from cyclic wrap-around, the exact integer-level action gives an
exact cyclic-window coordinate. -/
theorem smul_cyclicWindowCoset_of_not_boundary (P : Packet H D) (L : ℕ)
    [NeZero L] (g : G) (x : cyclicWindowModel P L)
    (hx : x.1 ∉ boundaryLevels L (height α e g))
    (hdH : normalCoordinate α e
      ((x.1.val : ℤ) + height α e g) g ∈ H) :
    g • cyclicWindowCoset α e P L x =
      cyclicWindowCoset α e P L
        (x.1 + (height α e g : ZMod L),
          P.quotientMap
            (⟨normalCoordinate α e
              ((x.1.val : ℤ) + height α e g) g, hdH⟩ : H) * x.2) := by
  have hval := val_add_eq_of_not_boundary (L := L) hx
  change g • windowCoset α e P x.2 (x.1.val : ℤ) =
    windowCoset α e P _
      ((x.1 + (height α e g : ZMod L)).val : ℤ)
  rw [hval]
  exact smul_windowCoset α e P g x.2 (x.1.val : ℤ) hdH

/-- The corresponding non-boundary translate belongs to the selected cyclic
window. -/
theorem smul_cyclicWindowCoset_mem_range_of_not_boundary (P : Packet H D)
    (L : ℕ) [NeZero L] (g : G) (x : cyclicWindowModel P L)
    (hx : x.1 ∉ boundaryLevels L (height α e g))
    (hdH : normalCoordinate α e
      ((x.1.val : ℤ) + height α e g) g ∈ H) :
    g • cyclicWindowCoset α e P L x ∈
      Set.range (cyclicWindowCoset α e P L) := by
  let y : cyclicWindowModel P L :=
    (x.1 + (height α e g : ZMod L),
      P.quotientMap
        (⟨normalCoordinate α e
          ((x.1.val : ℤ) + height α e g) g, hdH⟩ : H) * x.2)
  exact ⟨y, (smul_cyclicWindowCoset_of_not_boundary α e P L g x hx hdH).symm⟩

/-! ## Residual separation gives exact trace zero -/

/-- The stage subgroup generated by the normal coordinates at the canonical
integer representatives of a cyclic window. -/
abbrev stageSubgroup (F : Finset G) (L : ℕ) : Subgroup N :=
  normalWindowSubgroup α e F (levelWindow L)

/-- The nonidentity residual packet at one cyclic stage. -/
abbrev stagePacket (F : Finset G) (L : ℕ) : Finset (stageSubgroup α e F L) :=
  nontrivialNormalWindow α e F (levelWindow L)

/-- A tested normal coordinate, bundled in the subgroup generated by the
stage window. -/
def testedNormalCoordinate (F : Finset G) (L : ℕ) {g : G} (hgF : g ∈ F)
    (j : ℤ) (hj : j ∈ levelWindow L) : stageSubgroup α e F L :=
  ⟨normalCoordinate α e j g,
    normalWindow_subset_subgroup α e F (levelWindow L)
      (normalCoordinate_mem_normalWindow α e hgF hj)⟩

/-- A tested height-zero nonidentity coordinate belongs to the residual
packet separated at that stage. -/
theorem testedNormalCoordinate_mem_stagePacket (F : Finset G) (L : ℕ)
    {g : G} (hgF : g ∈ F) (hg : g ≠ 1) (hg0 : height α e g = 0)
    (j : ℤ) (hj : j ∈ levelWindow L) :
    testedNormalCoordinate α e F L hgF j hj ∈ stagePacket α e F L := by
  apply normalCoordinate_mem_nontrivialNormalWindow α e hgF hj
  exact normalCoordinate_ne_one_of_height_zero α e hg hg0 j

/-- Packet separation turns the exact fibre action into a no-fixed-point
statement. -/
theorem no_fixed_windowCoset_of_packet_element (P : Packet H D) (d : H)
    (hdD : d ∈ D) (g : G) (q : P.quotientModel) (j : ℤ)
    (hact : g • windowCoset α e P q j =
      windowCoset α e P (P.quotientMap d * q) j) :
    g • windowCoset α e P q j ≠ windowCoset α e P q j := by
  intro hfix
  have hcoset : windowCoset α e P (P.quotientMap d * q) j =
      windowCoset α e P q j := hact.symm.trans hfix
  have hpairs : (P.quotientMap d * q, j) = (q, j) := by
    apply windowCoset_pair_injective α e P
    exact hcoset
  have hq : P.quotientMap d * q = q := congrArg Prod.fst hpairs
  have hone : P.quotientMap d = 1 := by
    apply mul_right_cancel (b := q)
    simpa using hq
  exact (P.quotientMap_ne_one_of_mem hdD) hone

/-- At height zero, the exact action formula at a tested stage coordinate. -/
theorem smul_windowCoset_tested_height_zero (F : Finset G) (L : ℕ)
    (P : Packet (stageSubgroup α e F L) (stagePacket α e F L))
    {g : G} (hgF : g ∈ F) (hg0 : height α e g = 0)
    (q : P.quotientModel) (j : ℤ) (hj : j ∈ levelWindow L) :
    g • windowCoset α e P q j =
      windowCoset α e P
        (P.quotientMap (testedNormalCoordinate α e F L hgF j hj) * q) j := by
  have hdH : normalCoordinate α e (j + height α e g) g ∈
      stageSubgroup α e F L := by
    rw [hg0, add_zero]
    exact (testedNormalCoordinate α e F L hgF j hj).property
  simpa [testedNormalCoordinate, hg0] using
    (smul_windowCoset α e P g q j hdH)

/-- A tested height-zero nonidentity element fixes no coordinate of the
cyclic window built from its normal-coordinate packet. -/
theorem no_fixed_cyclicWindowCoset_of_mem (F : Finset G) (L : ℕ) [NeZero L]
    (P : Packet (stageSubgroup α e F L) (stagePacket α e F L))
    {g : G} (hgF : g ∈ F) (hg : g ≠ 1) (hg0 : height α e g = 0) :
    ∀ x : cyclicWindowModel P L,
      g • cyclicWindowCoset α e P L x ≠ cyclicWindowCoset α e P L x := by
  intro x hfix
  let j : ℤ := (x.1.val : ℤ)
  have hj : j ∈ levelWindow L := zmod_val_mem_levelWindow L x.1
  let d : stageSubgroup α e F L := testedNormalCoordinate α e F L hgF j hj
  have hdD : d ∈ stagePacket α e F L := by
    exact testedNormalCoordinate_mem_stagePacket α e F L hgF hg hg0 j hj
  have hact : g • windowCoset α e P x.2 j =
      windowCoset α e P (P.quotientMap d * x.2) j := by
    exact smul_windowCoset_tested_height_zero α e F L P hgF hg0 x.2 j hj
  have hfix' : g • windowCoset α e P x.2 j = windowCoset α e P x.2 j := by
    simpa [cyclicWindowCoset, j] using hfix
  exact no_fixed_windowCoset_of_packet_element α e P d hdD g x.2 j hact hfix'

/-- On every tested height-zero nonidentity element, the compressed canonical
generator has normalized trace exactly zero. -/
theorem normTrace_windowCompression_generator_eq_zero_of_mem
    (F : Finset G) (L : ℕ) [NeZero L]
    (P : Packet (stageSubgroup α e F L) (stagePacket α e F L))
    {g : G} (hgF : g ∈ F) (hg : g ≠ 1) (hg0 : height α e g = 0) :
    normTrace (cyclicWindowModel P L)
        (windowCompression α e P L (maximalGroupCStarGenerator G g)) = 0 :=
  normTrace_windowCompression_generator_eq_zero α e P L g
    (no_fixed_cyclicWindowCoset_of_mem α e F L P hgF hg hg0)

end

end LocallyRFByIntAmenableTrace
end GroupApproximation
