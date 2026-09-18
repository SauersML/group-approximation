import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopfH2.Commutator

/-!
# Hopf formula versus `groupHomology.H2`: every multiplier element is hit (lane LVHopfH2)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Hopf formula; Brown II.5 Thm 5.3).
Every `z ∈ K ∩ [E,E]` is `Φ c` for a 2-cycle `c`.  Proof by a pushout: put
`T := (K × ℤ[G]) ⧸ {(Φ c, -∂ c)}`, with `tK : K → T`, `tC : ℤ[G] → T`, so `tK ∘ Φ = tC ∘ ∂`.
The map `x ↦ tK (x σ(p x)⁻¹) + tC [p x]` is a homomorphism `E → T` into an abelian group, hence
kills `[E,E]`; on `K` it is `tK`.  So `tK z = 0`, i.e. `(z, 0) = (Φ c, -∂ c)` for some `c`.

* `hopfPushTK_phi`: `tK ∘ Φ = tC ∘ ∂`.
* `hopfPushTheta hf : E →* Multiplicative T`.
* `hopfChainPhi_exists_of_mem`: surjectivity of `Φ` from 2-cycles onto the multiplier.
-/

namespace GroupApproximation.Full.LVHopf

section Surjective

variable {G : Type} [Group G] {α : Type} {f : FreeGroup α →* G}

/-- The pushout relations `c ↦ (Φ c, -∂ c)`. -/
noncomputable def hopfPushRel (hf : Function.Surjective f) :
    (G × G →₀ ℤ) →+ Additive (HopfExtK f) × (G →₀ ℤ) :=
  (AddMonoidHom.inl (Additive (HopfExtK f)) (G →₀ ℤ)).comp (hopfChainPhi hf) -
    (AddMonoidHom.inr (Additive (HopfExtK f)) (G →₀ ℤ)).comp hopfChainD

/-- The pushout `T = (K × ℤ[G]) ⧸ {(Φ c, -∂ c)}`. -/
abbrev HopfPush (hf : Function.Surjective f) : Type :=
  (Additive (HopfExtK f) × (G →₀ ℤ)) ⧸ (hopfPushRel hf).range

/-- `tK : K → T`. -/
noncomputable def hopfPushTK (hf : Function.Surjective f) : Additive (HopfExtK f) →+ HopfPush hf :=
  (QuotientAddGroup.mk' (hopfPushRel hf).range).comp
    (AddMonoidHom.inl (Additive (HopfExtK f)) (G →₀ ℤ))

/-- `tC : ℤ[G] → T`. -/
noncomputable def hopfPushTC (hf : Function.Surjective f) : (G →₀ ℤ) →+ HopfPush hf :=
  (QuotientAddGroup.mk' (hopfPushRel hf).range).comp
    (AddMonoidHom.inr (Additive (HopfExtK f)) (G →₀ ℤ))

/-- `tK ∘ Φ = tC ∘ ∂`. -/
theorem hopfPushTK_phi (hf : Function.Surjective f) (c : G × G →₀ ℤ) :
    hopfPushTK hf (hopfChainPhi hf c) = hopfPushTC hf (hopfChainD c) := by
  rw [← sub_eq_zero, hopfPushTK, hopfPushTC, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact AddMonoidHom.mem_range.mpr ⟨c, by
    rw [hopfPushRel, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]⟩

/-- `tK [σ g σ h σ(gh)⁻¹] = tC (h - gh + g)`. -/
theorem hopfPushTK_rc (hf : Function.Surjective f) (g h : G) :
    hopfPushTK hf (hopfExtRcK hf g h) =
      hopfPushTC hf (Finsupp.single h 1 - Finsupp.single (g * h) 1 + Finsupp.single g 1) := by
  have e := hopfPushTK_phi hf (Finsupp.single (g, h) 1)
  rw [hopfChainPhi_single_one hf g h, hopfChainD_single g h 1] at e
  exact e

theorem hopfPushDiv_mem (hf : Function.Surjective f) (x : HopfExt f) :
    x * (hopfExtSec hf (hopfExtProj f x))⁻¹ ∈ (hopfExtProj f).ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hopfExtProj_sec hf (hopfExtProj f x), mul_inv_cancel]

/-- The `K`-coordinate `x σ(p x)⁻¹` of `x ∈ E`. -/
noncomputable def hopfPushDiv (hf : Function.Surjective f) (x : HopfExt f) :
    Additive (HopfExtK f) :=
  Additive.ofMul ⟨x * (hopfExtSec hf (hopfExtProj f x))⁻¹, hopfPushDiv_mem hf x⟩

/-- A group identity: if `y v⁻¹` commutes with `u`, then `x u⁻¹ (y v⁻¹) (u v s⁻¹) = x y s⁻¹`. -/
theorem hopfPush_aux {E : Type} [Group E] (x y u v s : E) (hb : y * v⁻¹ * u = u * (y * v⁻¹)) :
    x * u⁻¹ * (y * v⁻¹) * (u * v * s⁻¹) = x * y * s⁻¹ := by
  calc x * u⁻¹ * (y * v⁻¹) * (u * v * s⁻¹) = x * u⁻¹ * (y * v⁻¹ * u) * v * s⁻¹ := by
        simp only [mul_assoc]
    _ = x * u⁻¹ * (u * (y * v⁻¹)) * v * s⁻¹ := by rw [hb]
    _ = x * y * s⁻¹ := by simp only [mul_assoc, inv_mul_cancel_left]

/-- `div (x y) = div x + div y + [σ(p x) σ(p y) σ(p x p y)⁻¹]`. -/
theorem hopfPushDiv_mul (hf : Function.Surjective f) (x y : HopfExt f) :
    hopfPushDiv hf (x * y) = hopfPushDiv hf x + hopfPushDiv hf y +
      hopfExtRcK hf (hopfExtProj f x) (hopfExtProj f y) := by
  apply Additive.ext
  apply Subtype.ext
  have hb : y * (hopfExtSec hf (hopfExtProj f y))⁻¹ * hopfExtSec hf (hopfExtProj f x) =
      hopfExtSec hf (hopfExtProj f x) * (y * (hopfExtSec hf (hopfExtProj f y))⁻¹) :=
    (Subgroup.mem_center_iff.mp (hopfExtProj_ker_le_center f (hopfPushDiv_mem hf y))
      (hopfExtSec hf (hopfExtProj f x))).symm
  have key := hopfPush_aux x y (hopfExtSec hf (hopfExtProj f x))
    (hopfExtSec hf (hopfExtProj f y)) (hopfExtSec hf (hopfExtProj f x * hopfExtProj f y)) hb
  show x * y * (hopfExtSec hf (hopfExtProj f (x * y)))⁻¹ =
    x * (hopfExtSec hf (hopfExtProj f x))⁻¹ * (y * (hopfExtSec hf (hopfExtProj f y))⁻¹) *
      (hopfExtSec hf (hopfExtProj f x) * hopfExtSec hf (hopfExtProj f y) *
        (hopfExtSec hf (hopfExtProj f x * hopfExtProj f y))⁻¹)
  rw [map_mul (hopfExtProj f) x y]
  exact key.symm

/-- On `K`: `div z + [σ 1 σ 1 σ(1·1)⁻¹] = z`. -/
theorem hopfPushDiv_add_rc (hf : Function.Surjective f) {z : HopfExt f}
    (hz : z ∈ (hopfExtProj f).ker) :
    hopfPushDiv hf z + hopfExtRcK hf 1 1 = Additive.ofMul ⟨z, hz⟩ := by
  apply Additive.ext
  apply Subtype.ext
  show z * (hopfExtSec hf (hopfExtProj f z))⁻¹ *
    (hopfExtSec hf 1 * hopfExtSec hf 1 * (hopfExtSec hf (1 * 1))⁻¹) = z
  rw [MonoidHom.mem_ker.mp hz, mul_one (1 : G), mul_inv_cancel_right (hopfExtSec hf 1)
    (hopfExtSec hf 1), inv_mul_cancel_right z (hopfExtSec hf 1)]

/-- The additive form `x ↦ tK (div x) + tC [p x]` of the homomorphism `E → T`. -/
noncomputable def hopfPushA (hf : Function.Surjective f) (x : HopfExt f) : HopfPush hf :=
  hopfPushTK hf (hopfPushDiv hf x) + hopfPushTC hf (Finsupp.single (hopfExtProj f x) 1)

theorem hopfPushA_mul (hf : Function.Surjective f) (x y : HopfExt f) :
    hopfPushA hf (x * y) = hopfPushA hf x + hopfPushA hf y := by
  have hrc := hopfPushTK_rc hf (hopfExtProj f x) (hopfExtProj f y)
  simp only [hopfPushA]
  rw [hopfPushDiv_mul hf x y, map_add, map_add, hrc, map_mul (hopfExtProj f) x y, map_add,
    map_sub]
  abel

/-- The homomorphism `θ : E →* Multiplicative T`. -/
noncomputable def hopfPushTheta (hf : Function.Surjective f) :
    HopfExt f →* Multiplicative (HopfPush hf) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (hopfPushA hf x)) fun x y =>
    (congrArg Multiplicative.ofAdd (hopfPushA_mul hf x y)).trans
      (ofAdd_add (hopfPushA hf x) (hopfPushA hf y))

/-- `θ` kills `[E,E]`, the target being abelian. -/
theorem hopfPushA_of_mem_commutator (hf : Function.Surjective f) {z : HopfExt f}
    (hz : z ∈ commutator (HopfExt f)) : hopfPushA hf z = 0 := by
  have h : hopfPushTheta hf z = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker (hopfPushTheta hf) hz)
  exact congrArg Multiplicative.toAdd h

/-- On `K`, `θ` is `tK`. -/
theorem hopfPushA_of_mem_ker (hf : Function.Surjective f) {z : HopfExt f}
    (hz : z ∈ (hopfExtProj f).ker) : hopfPushA hf z = hopfPushTK hf (Additive.ofMul ⟨z, hz⟩) := by
  have hrc := hopfPushTK_rc hf 1 1
  rw [mul_one (1 : G), sub_self, zero_add] at hrc
  rw [hopfPushA, MonoidHom.mem_ker.mp hz, ← hrc]
  exact (map_add (hopfPushTK hf) (hopfPushDiv hf z) (hopfExtRcK hf 1 1)).symm.trans
    (congrArg (hopfPushTK hf) (hopfPushDiv_add_rc hf hz))

/-- **Onto** (Hopf formula, l.733-735): every element of the multiplier `K ∩ [E,E]` is `Φ c` for a
2-cycle `c`. -/
theorem hopfChainPhi_exists_of_mem (hf : Function.Surjective f) {z : HopfExt f}
    (hK : z ∈ (hopfExtProj f).ker) (hC : z ∈ commutator (HopfExt f)) :
    ∃ c : G × G →₀ ℤ, hopfChainD c = 0 ∧ hopfChainPhi hf c = Additive.ofMul ⟨z, hK⟩ := by
  have h0 : hopfPushTK hf (Additive.ofMul ⟨z, hK⟩) = 0 := by
    rw [← hopfPushA_of_mem_ker hf hK]
    exact hopfPushA_of_mem_commutator hf hC
  rw [hopfPushTK, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff] at h0
  obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.mp h0
  rw [hopfPushRel, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at hc
  have h1 := congrArg Prod.fst hc
  have h2 := congrArg Prod.snd hc
  simp only [Prod.fst_sub, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, sub_zero] at h1
  simp only [Prod.snd_sub, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, zero_sub,
    neg_eq_zero] at h2
  exact ⟨c, h2, h1⟩

end Surjective

end GroupApproximation.Full.LVHopf
