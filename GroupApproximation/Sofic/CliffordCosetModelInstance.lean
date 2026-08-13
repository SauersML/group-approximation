import GroupApproximation.Sofic.CliffordLampGroup
import GroupApproximation.Sofic.CliffordMarkedWitness
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A constructive Clifford coset model

This file discharges the universal Clifford-coset interface
`CliffordCosetModel` of `CliffordMarkedWitness` with an explicit group: the
presented Clifford lamp group over the left coset space `G ⧸ iota.range`,
extended by `G` acting through coset permutations.

* The carrier is `CliffordLamp (G ⧸ iota.range) ⋊ G`.
* `ambient` is the right inclusion; `c` is the lamp at the root coset;
  `z` is the central sign.
* `root_commutes` is the fixing of the root coset by the image of `iota`.
* `distinct_site_commutator` unwinds to the braiding relation of the lamp
  group at two distinct cosets; the representative-level premise of the
  interface is exactly left-coset distinctness.
* `z_ne_one` is the crossing-form model separation `sign_ne_one`, available
  for every index type.

No injectivity of `iota` and no properness enter anywhere in this file.
-/

namespace GroupApproximation
namespace CliffordMarkedWitness

open CliffordLamp SemidirectProduct
open scoped commutatorElement

universe u

variable {Gamma : Type} [Group Gamma]
variable (G : Type u) [Group G] (iota : Gamma →* G)

/-! ## The coset space and the lamp action -/

/-- The left coset space of the image subgroup. -/
abbrev LampSites : Type u := G ⧸ iota.range

/-- The root coset. -/
def rootSite : LampSites G iota := QuotientGroup.mk 1

theorem smul_rootSite (g : G) :
    g • rootSite G iota =
      (QuotientGroup.mk g : G ⧸ iota.range) := by
  show g • (QuotientGroup.mk 1 : G ⧸ iota.range) = QuotientGroup.mk g
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- The image of `iota` fixes the root coset. -/
theorem iota_smul_rootSite (γ : Gamma) :
    iota γ • rootSite G iota = rootSite G iota := by
  rw [smul_rootSite]
  show (QuotientGroup.mk (iota γ) : G ⧸ iota.range) = QuotientGroup.mk 1
  rw [QuotientGroup.eq]
  exact Subgroup.inv_mem _ ⟨γ, rfl⟩

/-- Representative-level coset distinctness, in the exact form consumed by
the universal interface. -/
theorem site_ne_of_not_translate {g h : G}
    (hdist : ¬ ∃ γ : Gamma, g = h * iota γ) :
    g • rootSite G iota ≠ h • rootSite G iota := by
  rw [smul_rootSite, smul_rootSite]
  intro hc
  rw [QuotientGroup.eq, MonoidHom.mem_range] at hc
  obtain ⟨γ, hγ⟩ := hc
  refine hdist ⟨γ⁻¹, ?_⟩
  rw [map_inv, ← hγ, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel,
    one_mul]

/-- The coset permutation action on the lamp group. -/
def siteAction : G →* MulAut (CliffordLamp (LampSites G iota)) :=
  (permHom (LampSites G iota)).comp
    (MulAction.toPermHom G (LampSites G iota))

theorem siteAction_lamp (g : G) (x : LampSites G iota) :
    siteAction G iota g (lamp (LampSites G iota) x) =
      lamp (LampSites G iota) (g • x) := by
  show permHom (LampSites G iota)
      (MulAction.toPermHom G (LampSites G iota) g)
      (lamp (LampSites G iota) x) = lamp (LampSites G iota) (g • x)
  rw [permHom_apply_lamp]
  rfl

theorem siteAction_sign (g : G) :
    siteAction G iota g (sign (LampSites G iota)) =
      sign (LampSites G iota) := by
  show permHom (LampSites G iota)
      (MulAction.toPermHom G (LampSites G iota) g)
      (sign (LampSites G iota)) = sign (LampSites G iota)
  rw [permHom_apply_sign]

/-! ## The total group -/

/-- The Clifford lamp group over the coset space, extended by `G`. -/
abbrev TotalLampGroup : Type u :=
  CliffordLamp (LampSites G iota) ⋊[siteAction G iota] G

/-- Conjugating a lamp by an ambient element moves its site. -/
theorem conj_lamp (g : G) (x : LampSites G iota) :
    (inr g : TotalLampGroup G iota) *
        inl (lamp (LampSites G iota) x) * (inr g)⁻¹ =
      inl (lamp (LampSites G iota) (g • x)) := by
  rw [← map_inv, ← inl_aut, siteAction_lamp]

/-- **The constructive Clifford coset model.**  The presented lamp group
over the coset space, extended by the coset permutation action, satisfies
every axiom of the universal interface. -/
def cliffordCosetModel : CliffordCosetModel G iota where
  E := TotalLampGroup G iota
  groupE := inferInstance
  ambient := inr
  c := inl (lamp (LampSites G iota) (rootSite G iota))
  z := inl (sign (LampSites G iota))
  root_commutes := by
    intro γ
    have h : (inr (iota γ) : TotalLampGroup G iota) *
        inl (lamp (LampSites G iota) (rootSite G iota)) *
        (inr (iota γ))⁻¹ =
        inl (lamp (LampSites G iota) (rootSite G iota)) := by
      rw [conj_lamp, iota_smul_rootSite]
    have h' : (inr (iota γ) : TotalLampGroup G iota) *
        inl (lamp (LampSites G iota) (rootSite G iota)) =
        inl (lamp (LampSites G iota) (rootSite G iota)) * inr (iota γ) :=
      mul_inv_eq_iff_eq_mul.mp h
    exact h'.symm
  z_sq := by
    rw [← map_pow, sign_sq, map_one]
  z_central := by
    intro x
    obtain ⟨n, g⟩ := x
    show (inl (sign (LampSites G iota)) : TotalLampGroup G iota) *
        ⟨n, g⟩ = ⟨n, g⟩ * inl (sign (LampSites G iota))
    show (⟨sign (LampSites G iota), 1⟩ : TotalLampGroup G iota) * ⟨n, g⟩ =
      ⟨n, g⟩ * ⟨sign (LampSites G iota), 1⟩
    rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def]
    congr 1
    · show sign (LampSites G iota) * siteAction G iota 1 n =
        n * siteAction G iota g (sign (LampSites G iota))
      rw [map_one, siteAction_sign]
      show sign (LampSites G iota) * n = n * sign (LampSites G iota)
      exact (sign_commute (LampSites G iota) n).eq
    · rw [one_mul, mul_one]
  z_ne_one := by
    intro h
    exact sign_ne_one (LampSites G iota)
      (inl_injective (by rw [h, map_one]))
  distinct_site_commutator := by
    intro g h hdist
    have hsite : g • rootSite G iota ≠ h • rootSite G iota :=
      site_ne_of_not_translate G iota hdist
    show ⁅(inr g : TotalLampGroup G iota) *
        inl (lamp (LampSites G iota) (rootSite G iota)) * (inr g)⁻¹,
        inr h * inl (lamp (LampSites G iota) (rootSite G iota)) *
          (inr h)⁻¹⁆ = inl (sign (LampSites G iota))
    rw [conj_lamp, conj_lamp, ← map_commutatorElement,
      commutator_lamp_lamp (LampSites G iota) hsite]

/-- The universal interface is inhabited, constructively. -/
theorem cliffordCosetModel_nonempty :
    Nonempty (CliffordCosetModel G iota) :=
  ⟨cliffordCosetModel G iota⟩

end CliffordMarkedWitness
end GroupApproximation
