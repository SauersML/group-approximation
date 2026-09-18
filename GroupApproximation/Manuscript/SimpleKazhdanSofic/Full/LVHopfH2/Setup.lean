import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopf.Multiplier
import Mathlib.Tactic.Group

/-!
# Hopf formula versus `groupHomology.H2`: the central extension `F ⧸ [F,R]` (lane LVHopfH2)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Hopf formula; Hopf 1942,
Brown, *Cohomology of groups*, II.5 Thm 5.3).  For a surjection `f : F ↠ G` from a free group with
kernel `R`, put `E := F ⧸ [F,R]` and `K := ker (E → G) = R ⧸ [F,R]`.

* `HopfExt f`, `hopfExtProj f : E →* G`, `hopfExtProj_ker_le_center`: `K` is central.
* `HopfExtK f := ker (hopfExtProj f)` carries a `CommGroup` instance.
* `hopfExtSec hf : G → E`: a set-theoretic section.
* `hopfExtRc hf g h = σ g · σ h · σ (g h)⁻¹ ∈ K`, and its cocycle identity `hopfExtRc_cocycle`.
* `hopfExtRcK hf g h : Additive K`, with the additive cocycle identity `hopfExtRcK_cocycle`.
-/

namespace GroupApproximation.Full.LVHopf

section Setup

variable {G : Type} [Group G] {α : Type} (f : FreeGroup α →* G)

/-- The central extension `E = F ⧸ [F, R]` of a free presentation `f : F ↠ G`, `R = ker f`.
(`simple_kazhdan_sofic_group.tex` l.733-735, Hopf formula.) -/
abbrev HopfExt : Type := FreeGroup α ⧸ ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆

/-- The projection `E = F ⧸ [F, R] → G` induced by `f`. -/
def hopfExtProj : HopfExt f →* G :=
  QuotientGroup.lift ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆ f
    (Subgroup.commutator_le_right (⊤ : Subgroup (FreeGroup α)) f.ker)

theorem hopfExtProj_mk (x : FreeGroup α) :
    hopfExtProj f (QuotientGroup.mk' ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆ x) = f x :=
  rfl

/-- The kernel `R ⧸ [F,R]` of `E → G` is central (Hopf formula, l.733-735). -/
theorem hopfExtProj_ker_le_center : (hopfExtProj f).ker ≤ Subgroup.center (HopfExt f) := by
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆ z
  have h : f x = 1 := MonoidHom.mem_ker.mp hz
  exact mk'_mem_center_of_mem f.ker (MonoidHom.mem_ker.mpr h)

/-- The central kernel `K = R ⧸ [F,R]` of `E → G`. -/
abbrev HopfExtK : Type := (hopfExtProj f).ker

/-- `K` is abelian, being central. -/
instance hopfExtKCommGroup : CommGroup (HopfExtK f) :=
  { (inferInstance : Group (HopfExtK f)) with
    mul_comm := fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hopfExtProj_ker_le_center f b.2) (a : HopfExt f)) }

variable {f}

/-- A set-theoretic section `G → E` of `E → G`. -/
noncomputable def hopfExtSec (hf : Function.Surjective f) (g : G) : HopfExt f :=
  QuotientGroup.mk' ⁅(⊤ : Subgroup (FreeGroup α)), f.ker⁆ (Function.surjInv hf g)

theorem hopfExtProj_sec (hf : Function.Surjective f) (g : G) :
    hopfExtProj f (hopfExtSec hf g) = g :=
  Function.surjInv_eq hf g

/-- The factor set `σ g · σ h · σ (g h)⁻¹` of the section. -/
noncomputable def hopfExtRc (hf : Function.Surjective f) (g h : G) : HopfExt f :=
  hopfExtSec hf g * hopfExtSec hf h * (hopfExtSec hf (g * h))⁻¹

theorem hopfExtRc_mem (hf : Function.Surjective f) (g h : G) :
    hopfExtRc hf g h ∈ (hopfExtProj f).ker := by
  rw [MonoidHom.mem_ker, hopfExtRc, map_mul, map_mul, map_inv, hopfExtProj_sec hf g,
    hopfExtProj_sec hf h, hopfExtProj_sec hf (g * h), mul_inv_cancel]

/-- A free-group identity behind the cocycle identity of the factor set. -/
theorem hopfExt_cocycle_aux {E : Type} [Group E] (a b c d e p : E)
    (hX : a * (b * c * d⁻¹) = b * c * d⁻¹ * a) :
    b * c * d⁻¹ * (a * d * p⁻¹) = a * b * e⁻¹ * (e * c * p⁻¹) := by
  calc b * c * d⁻¹ * (a * d * p⁻¹) = b * c * d⁻¹ * a * d * p⁻¹ := by group
    _ = a * (b * c * d⁻¹) * d * p⁻¹ := by rw [hX]
    _ = a * b * e⁻¹ * (e * c * p⁻¹) := by group

/-- Cocycle identity of the factor set (it is central). -/
theorem hopfExtRc_cocycle (hf : Function.Surjective f) (g h k : G) :
    hopfExtRc hf h k * hopfExtRc hf g (h * k) = hopfExtRc hf g h * hopfExtRc hf (g * h) k := by
  have hX : hopfExtSec hf g * hopfExtRc hf h k = hopfExtRc hf h k * hopfExtSec hf g :=
    Subgroup.mem_center_iff.mp (hopfExtProj_ker_le_center f (hopfExtRc_mem hf h k))
      (hopfExtSec hf g)
  have key := hopfExt_cocycle_aux (hopfExtSec hf g) (hopfExtSec hf h) (hopfExtSec hf k)
    (hopfExtSec hf (h * k)) (hopfExtSec hf (g * h)) (hopfExtSec hf (g * h * k)) hX
  rw [hopfExtRc, hopfExtRc, hopfExtRc, hopfExtRc, ← mul_assoc g h k]
  exact key

/-- The factor set as an element of `Additive K`. -/
noncomputable def hopfExtRcK (hf : Function.Surjective f) (g h : G) : Additive (HopfExtK f) :=
  Additive.ofMul ⟨hopfExtRc hf g h, hopfExtRc_mem hf g h⟩

theorem hopfExtRcK_val (hf : Function.Surjective f) (g h : G) :
    ((Additive.toMul (hopfExtRcK hf g h) : HopfExtK f) : HopfExt f) = hopfExtRc hf g h :=
  rfl

/-- Additive cocycle identity of the factor set. -/
theorem hopfExtRcK_cocycle (hf : Function.Surjective f) (g h k : G) :
    hopfExtRcK hf h k + hopfExtRcK hf g (h * k) =
      hopfExtRcK hf g h + hopfExtRcK hf (g * h) k := by
  apply Additive.ext
  apply Subtype.ext
  exact hopfExtRc_cocycle hf g h k

end Setup

end GroupApproximation.Full.LVHopf
