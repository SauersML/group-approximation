import GroupApproximation.Steinberg.KervaireSteinberg

/-!
# Lifting homomorphisms through central quotients

Group-theoretic tools for the stability step of leaf T1b.iii
(`simple_kazhdan_sofic_group.tex`, l.733-735, `sec:questions`).

* `hom_eq_of_mul_inv_mem_center`: two homomorphisms out of a perfect group
  that agree modulo the centre are equal.
* `exists_lift_of_ker_le_center`: for `n ≥ 5`, every homomorphism
  `St_n(R) → H` lifts through any surjection `Q → H` with central kernel
  (Kervaire--Steinberg, via `KervaireSteinberg.every_centralExtension_splits`
  applied to the pullback extension).
* `relCommutator π = ⁅⊤, ker π⁆` and the induced map
  `quotHom π : G ⧸ ⁅⊤, ker π⁆ → H`, whose kernel is central.
-/

namespace GroupApproximation
namespace Full
namespace LVStability

open scoped commutatorElement

section Uniqueness

variable {G H : Type*} [Group G] [Group H]

/-- Two homomorphisms out of a perfect group which agree modulo the centre of
the target are equal. -/
theorem hom_eq_of_mul_inv_mem_center [Group.IsPerfect G] {f g : G →* H}
    (hfg : ∀ x, f x * (g x)⁻¹ ∈ Subgroup.center H) : f = g := by
  have hle : commutator G ≤ f.eqLocus g := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change f ⁅a, b⁆ = g ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    exact KervaireSteinberg.commutator_eq_of_eq_mod_center (hfg a) (hfg b)
  apply MonoidHom.ext
  intro x
  have hx : x ∈ commutator G := Group.IsPerfect.mem_commutator
  exact hle hx

/-- A homomorphism whose values on `ker π` are central kills `⁅⊤, ker π⁆`. -/
theorem commutator_ker_le_ker {K : Type*} [Group K] (π : G →* K) (f : G →* H)
    (hf : ∀ x ∈ π.ker, f x ∈ Subgroup.center H) :
    ⁅(⊤ : Subgroup G), π.ker⁆ ≤ f.ker := by
  rw [Subgroup.commutator_le]
  intro a _ b hb
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.1 (hf b hb) (f a)

end Uniqueness

section KervaireLift

/-- **Kervaire lift.** For `n ≥ 5`, every homomorphism `φ : St_n(R) → H` lifts
through a surjection `P : Q → H` whose kernel is central.  The lift is obtained
by splitting the pullback central extension of `St_n(R)`. -/
theorem exists_lift_of_ker_le_center {n : ℕ} (hn : 5 ≤ n) {R Q H : Type*} [Ring R]
    [Group Q] [Group H] (P : Q →* H) (hP : Function.Surjective P)
    (hker : P.ker ≤ Subgroup.center Q) (φ : SteinbergGroup (Fin n) R →* H) :
    ∃ F : SteinbergGroup (Fin n) R →* Q, P.comp F = φ := by
  let E : Subgroup (SteinbergGroup (Fin n) R × Q) :=
    (φ.comp (MonoidHom.fst _ _)).eqLocus (P.comp (MonoidHom.snd _ _))
  have hmem : ∀ x : SteinbergGroup (Fin n) R × Q, x ∈ E ↔ φ x.1 = P x.2 :=
    fun _ => Iff.rfl
  let C : CentralExtension E (SteinbergGroup (Fin n) R) :=
    { projection := (MonoidHom.fst _ _).comp E.subtype
      surjective := by
        intro g
        obtain ⟨q, hq⟩ := hP (φ g)
        exact ⟨⟨(g, q), (hmem (g, q)).2 hq.symm⟩, rfl⟩
      ker_le_center := by
        intro e he
        have h1 : e.1.1 = 1 := MonoidHom.mem_ker.1 he
        have hq : e.1.2 ∈ Subgroup.center Q := by
          apply hker
          rw [MonoidHom.mem_ker, ← (hmem e.1).1 e.2, h1, map_one]
        rw [Subgroup.mem_center_iff]
        intro e'
        apply Subtype.ext
        apply Prod.ext
        · change e'.1.1 * e.1.1 = e.1.1 * e'.1.1
          rw [h1, mul_one, one_mul]
        · change e'.1.2 * e.1.2 = e.1.2 * e'.1.2
          exact Subgroup.mem_center_iff.1 hq e'.1.2 }
  obtain ⟨s, hs⟩ := KervaireSteinberg.every_centralExtension_splits hn C
  refine ⟨(MonoidHom.snd _ _).comp (E.subtype.comp s), ?_⟩
  apply MonoidHom.ext
  intro g
  have hsg : (s g).1.1 = g := DFunLike.congr_fun hs g
  have hmemg : φ (s g).1.1 = P (s g).1.2 := (hmem (s g).1).1 (s g).2
  change P (s g).1.2 = φ g
  rw [← hmemg, hsg]

end KervaireLift

section RelCommutator

variable {G H : Type*} [Group G] [Group H]

/-- The relative commutator `⁅G, ker π⁆`. -/
abbrev relCommutator (π : G →* H) : Subgroup G := ⁅(⊤ : Subgroup G), π.ker⁆

instance relCommutator_normal (π : G →* H) : (relCommutator π).Normal :=
  Subgroup.commutator_normal ⊤ π.ker

theorem relCommutator_le_ker (π : G →* H) : relCommutator π ≤ π.ker :=
  Subgroup.commutator_le_right ⊤ π.ker

/-- The homomorphism `G ⧸ ⁅G, ker π⁆ → H` induced by `π`. -/
def quotHom (π : G →* H) : G ⧸ relCommutator π →* H :=
  QuotientGroup.lift (relCommutator π) π (relCommutator_le_ker π)

@[simp]
theorem quotHom_mk (π : G →* H) (x : G) :
    quotHom π (x : G ⧸ relCommutator π) = π x :=
  rfl

theorem quotHom_comp_mk' (π : G →* H) :
    (quotHom π).comp (QuotientGroup.mk' (relCommutator π)) = π :=
  MonoidHom.ext fun _ => rfl

theorem quotHom_surjective (π : G →* H) (hπ : Function.Surjective π) :
    Function.Surjective (quotHom π) := by
  intro h
  obtain ⟨x, hx⟩ := hπ h
  exact ⟨(x : G ⧸ relCommutator π), hx⟩

/-- The kernel of `quotHom π` is central in `G ⧸ ⁅G, ker π⁆`. -/
theorem quotHom_ker_le_center (π : G →* H) :
    (quotHom π).ker ≤ Subgroup.center (G ⧸ relCommutator π) := by
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have hx : x ∈ π.ker := MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hz)
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  have hc : ((⁅y, x⁆ : G) : G ⧸ relCommutator π) = 1 :=
    (QuotientGroup.eq_one_iff _).2
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) hx)
  have hyx : y * x = ⁅y, x⁆ * (x * y) := by
    rw [commutatorElement_def, mul_assoc _ x⁻¹, inv_mul_cancel_left, inv_mul_cancel_right]
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hyx, QuotientGroup.mk_mul, hc,
    one_mul]

/-- The image of `ker π` in `G ⧸ ⁅G, ker π⁆` is central. -/
theorem mk_mem_center_of_mem_ker (π : G →* H) {x : G} (hx : x ∈ π.ker) :
    (x : G ⧸ relCommutator π) ∈ Subgroup.center (G ⧸ relCommutator π) :=
  quotHom_ker_le_center π hx

/-- The quotient `G ⧸ ⁅G, ker π⁆` as a central extension of `H`. -/
def quotCentralExtension (π : G →* H) (hπ : Function.Surjective π) :
    CentralExtension (G ⧸ relCommutator π) H where
  projection := quotHom π
  surjective := quotHom_surjective π hπ
  ker_le_center := quotHom_ker_le_center π

/-- Kervaire lift into `U = G ⧸ ⁅G, ker π⁆`. -/
theorem exists_lift_quotHom {n : ℕ} (hn : 5 ≤ n) {R : Type*} [Ring R] (π : G →* H)
    (hπ : Function.Surjective π) (φ : SteinbergGroup (Fin n) R →* H) :
    ∃ F : SteinbergGroup (Fin n) R →* G ⧸ relCommutator π, (quotHom π).comp F = φ :=
  exists_lift_of_ker_le_center hn (quotHom π) (quotHom_surjective π hπ)
    (quotHom_ker_le_center π) φ

/-- Two homomorphisms from a perfect group into `G ⧸ ⁅G, ker π⁆` with the same
composite to `H` are equal. -/
theorem hom_eq_of_quotHom_comp_eq {P : Type*} [Group P] [Group.IsPerfect P] (π : G →* H)
    {f g : P →* G ⧸ relCommutator π} (h : (quotHom π).comp f = (quotHom π).comp g) :
    f = g := by
  apply hom_eq_of_mul_inv_mem_center
  intro x
  apply quotHom_ker_le_center π
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  have hx : quotHom π (f x) = quotHom π (g x) := DFunLike.congr_fun h x
  rw [hx, mul_inv_cancel]

end RelCommutator

end LVStability
end Full
end GroupApproximation
