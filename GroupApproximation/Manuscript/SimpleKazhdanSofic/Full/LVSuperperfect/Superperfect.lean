import GroupApproximation.Sofic.CentralCoverInheritance
import GroupApproximation.Steinberg.KervaireSteinberg
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVEGen.GLEqElementary

/-!
# Superperfect groups and the units of `L_{𝔽₂}(1,2)` (lane LVSuperperfect)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`) cites Caprace–Rémy: infinite
finitely presented simple Kazhdan groups exist.  The Lean route to that sentence is conditional on
the binder `hsp`: the units `Lˣ` of `L = L_{𝔽₂}(1,2)` are superperfect, meaning that every central
extension `E ↠ Lˣ` with `E` perfect is injective.

This file fixes that predicate (`IsSuperperfect`) and proves the transfer results that reduce `hsp`
to statements about matrix groups over `L`:

* `projection_injective_of_section`: a perfect central extension with a homomorphic section is
  injective.
* `isSuperperfect_of_forall_section`: if every central extension splits, the base is superperfect.
* `IsSuperperfect.of_mulEquiv`: superperfectness is invariant under group isomorphism.
* `isSuperperfect_steinberg`: `Stₙ(R)` is superperfect for `n ≥ 5` (Kervaire–Steinberg).
* `binaryLeavittUnits_isSuperperfect_of_gl`: `GL_r(L)` superperfect for some `r ≥ 1` gives `hsp`
  (prefix-code self-similarity `M_r(L) ≅ L`).
* `binaryLeavittUnits_isSuperperfect_of_steinbergToGL_injective`,
  `binaryLeavittUnits_isSuperperfect_of_K2_eq_bot`: `K₂(n, L) = ⊥` for some `n ≥ 5` gives `hsp`.
* `isSuperperfect_binaryLeavittUnits_iff`: `IsSuperperfect Lˣ` is, by `Iff.rfl`, the body of the
  endpoint binder `LeavittK2.EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`.  That
  module is not imported here, because importing it would wire its unverified foreign orphan closure.

Every imported module is already reachable from `GroupApproximation.lean`.
-/

namespace GroupApproximation.Full.LVSuperperfect

open scoped commutatorElement

universe u v

/-- A group `G` is **superperfect** (in central-extension form) if every central extension
`E ↠ G` with `E` perfect is injective.  For perfect `G` this says `H₂(G; ℤ) = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`.) -/
def IsSuperperfect (G : Type u) [Group G] : Prop :=
  ∀ (E : Type) [Group E] (P : CentralExtension E G),
    _root_.commutator E = ⊤ → Function.Injective P.projection

/-- **Formal splitting.**  A central extension `π : E ↠ G` with a homomorphic section `s` and
perfect `E` is injective: `ψ(x) = x · s(π x)⁻¹` is a homomorphism into the centre, so it kills
`[E, E] = E`, whence `x = s(π x)`. -/
theorem projection_injective_of_section {E : Type u} {G : Type v} [Group E] [Group G]
    (P : CentralExtension E G) (s : G →* E) (hs : P.projection.comp s = MonoidHom.id G)
    (hE : _root_.commutator E = ⊤) : Function.Injective P.projection := by
  have hsg : ∀ g : G, P.projection (s g) = g := fun g => DFunLike.congr_fun hs g
  have hcen : ∀ x : E, x * (s (P.projection x))⁻¹ ∈ Subgroup.center E := fun x => by
    apply P.ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsg, mul_inv_cancel]
  let ψ : E →* E := MonoidHom.mk' (fun x => x * (s (P.projection x))⁻¹) (fun x y => by
    have ha := Subgroup.mem_center_iff.mp (hcen y)
    show x * y * (s (P.projection (x * y)))⁻¹ =
      x * (s (P.projection x))⁻¹ * (y * (s (P.projection y))⁻¹)
    rw [map_mul, map_mul, mul_inv_rev, ha (x * (s (P.projection x))⁻¹)]
    calc x * y * ((s (P.projection y))⁻¹ * (s (P.projection x))⁻¹)
        = x * (y * (s (P.projection y))⁻¹) * (s (P.projection x))⁻¹ := by
          simp only [mul_assoc]
      _ = y * (s (P.projection y))⁻¹ * x * (s (P.projection x))⁻¹ := by rw [ha x]
      _ = y * (s (P.projection y))⁻¹ * (x * (s (P.projection x))⁻¹) := mul_assoc _ _ _)
  have hψ : ∀ x : E, ψ x = x * (s (P.projection x))⁻¹ := fun _ => rfl
  have hle : _root_.commutator E ≤ ψ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    have h₂ : ψ g₂ ∈ Subgroup.center E := by
      rw [hψ]
      exact hcen g₂
    exact (Subgroup.mem_center_iff.mp h₂ (ψ g₁))
  have hfix : ∀ x : E, x = s (P.projection x) := fun x => by
    have hmem : x ∈ _root_.commutator E := by
      rw [hE]
      exact Subgroup.mem_top x
    have h₁ : ψ x = 1 := MonoidHom.mem_ker.mp (hle hmem)
    rw [hψ] at h₁
    exact mul_inv_eq_one.mp h₁
  intro x y hxy
  calc x = s (P.projection x) := hfix x
    _ = s (P.projection y) := by rw [hxy]
    _ = y := (hfix y).symm

/-- If every central extension of `G` (with total group in `Type`) has a homomorphic section,
then `G` is superperfect. -/
theorem isSuperperfect_of_forall_section {G : Type u} [Group G]
    (h : ∀ (E : Type) [Group E] (P : CentralExtension E G),
      ∃ s : G →* E, P.projection.comp s = MonoidHom.id G) :
    IsSuperperfect G := by
  intro E _ P hE
  obtain ⟨s, hs⟩ := h E P
  exact projection_injective_of_section P s hs hE

/-- Superperfectness is invariant under isomorphism of the base group. -/
theorem IsSuperperfect.of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H)
    (hG : IsSuperperfect G) : IsSuperperfect H := by
  intro E _ P hE
  have hinj : Function.Injective (P.postcompEquiv e.symm).projection :=
    hG E (P.postcompEquiv e.symm) hE
  intro x y hxy
  apply hinj
  show e.symm.toMonoidHom (P.projection x) = e.symm.toMonoidHom (P.projection y)
  rw [hxy]

/-- Superperfectness transfers along isomorphisms in both directions. -/
theorem isSuperperfect_congr {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) :
    IsSuperperfect G ↔ IsSuperperfect H :=
  ⟨IsSuperperfect.of_mulEquiv e, IsSuperperfect.of_mulEquiv e.symm⟩

/-- **Kervaire–Steinberg.**  For `n ≥ 5` every central extension of `Stₙ(R)` splits, so the
Steinberg group is superperfect. -/
theorem isSuperperfect_steinberg {R : Type u} [Ring R] {n : ℕ} (hn : 5 ≤ n) :
    IsSuperperfect (SteinbergGroup (Fin n) R) := by
  apply isSuperperfect_of_forall_section
  intro E _ P
  exact KervaireSteinberg.every_centralExtension_splits hn P

/-- `IsSuperperfect Lˣ` is literally the body of the endpoint binder
`LeavittK2.EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`
(`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`). -/
theorem isSuperperfect_binaryLeavittUnits_iff :
    IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) ↔
      ∀ (E : Type) [Group E]
        (P : GroupApproximation.CentralExtension E
          ((GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ)),
        _root_.commutator E = ⊤ → Function.Injective P.projection :=
  Iff.rfl

/-- **`hsp` from matrix units.**  If `GL_r(L)` is superperfect for some `r ≥ 1`, then so is `Lˣ`,
since `GL_r(L) ≅ Lˣ` (`LVEGen.nonempty_glEquivUnits`).  With `r = 3` this is the route through
`H₂(GL₃(L); ℤ) = 0` (Khanh arXiv:2609.08428, Thm 4.4). -/
theorem binaryLeavittUnits_isSuperperfect_of_gl {r : ℕ} (hr : 1 ≤ r)
    (h : IsSuperperfect ((Matrix (Fin r) (Fin r) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))ˣ)) :
    IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) := by
  obtain ⟨e⟩ := LVEGen.nonempty_glEquivUnits (ZMod 2) hr
  exact h.of_mulEquiv e

/-- Conversely `Lˣ` superperfect makes every `GL_r(L)`, `r ≥ 1`, superperfect. -/
theorem gl_isSuperperfect_of_binaryLeavittUnits {r : ℕ} (hr : 1 ≤ r)
    (h : IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ)) :
    IsSuperperfect ((Matrix (Fin r) (Fin r) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))ˣ) := by
  obtain ⟨e⟩ := LVEGen.nonempty_glEquivUnits (ZMod 2) hr
  exact h.of_mulEquiv e.symm

/-- **`hsp` from an injective Steinberg projection.**  If `Stₙ(L) → GLₙ(L)` is injective for some
`n ≥ 5`, then `Stₙ(L) ≅ GLₙ(L) ≅ Lˣ`, and Kervaire–Steinberg gives superperfectness. -/
theorem binaryLeavittUnits_isSuperperfect_of_steinbergToGL_injective {n : ℕ} (hn : 5 ≤ n)
    (hinj : Function.Injective (LVEGen.steinbergToGL (ZMod 2) n)) :
    IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) := by
  have hsurj : Function.Surjective (LVEGen.steinbergToGL (ZMod 2) n) :=
    LVEGen.steinbergToGL_surjective (ZMod 2) (by omega)
  have hst : IsSuperperfect ((Matrix (Fin n) (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))ˣ) :=
    (isSuperperfect_steinberg (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) hn).of_mulEquiv
      (MulEquiv.ofBijective (LVEGen.steinbergToGL (ZMod 2) n) ⟨hinj, hsurj⟩)
  exact binaryLeavittUnits_isSuperperfect_of_gl (r := n) (by omega) hst

/-- **`hsp` from `K₂(n, L) = ⊥`** for some `n ≥ 5`, with `K₂(n, L)` the kernel of the Steinberg
projection `Stₙ(L) → Eₙ(L)`. -/
theorem binaryLeavittUnits_isSuperperfect_of_K2_eq_bot {n : ℕ} (hn : 5 ≤ n)
    (hK : (SteinbergGroup.projection (I := Fin n)
      (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).ker = ⊥) :
    IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) := by
  apply binaryLeavittUnits_isSuperperfect_of_steinbergToGL_injective hn
  rw [← MonoidHom.ker_eq_bot_iff, LVEGen.steinbergToGL_ker]
  exact hK

end GroupApproximation.Full.LVSuperperfect
