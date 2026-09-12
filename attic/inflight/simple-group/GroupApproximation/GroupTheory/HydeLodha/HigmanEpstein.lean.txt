import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Set.Disjoint
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Higman–Epstein commutator arguments

The simple group of `non_mf_groups_exist.tex`, Section 5, is Hyde–Lodha's `Q₂`.  Its
simplicity rests on the simplicity of the derived subgroup of a Higman–Thompson group,
and that is a commutator argument about supports of permutations, due to Higman and
Epstein.  This module proves the argument for an arbitrary group of permutations,
with the geometry recorded only through supports.

* `SupportedIn f U`: `f` fixes every point outside `U`.  Permutations supported in
  disjoint sets commute (`commute_of_supportedIn`).
* **Epstein's trick** (`commutatorElement_commutatorElement_of_displaced`): if `f` moves
  `U` off itself and `a, b` are supported in `U`, then `⁅⁅a, f⁆, b⁆ = ⁅a, b⁆`.
* `commutator_le_of_normal_commutator`: a subgroup normalized by `⁅G, G⁆` that contains
  an element displacing a set `U` into which `⁅G, G⁆` can move the supports of any two
  elements of `G` (with room for two disjoint copies) contains `⁅G, G⁆`.
  `isSimpleGroup_commutator` packages this as simplicity of `⁅G, G⁆`.
* `commutator_le_of_decomposition`: if every element of `P` is `z₀^i z₁^j c` with `z₀, z₁`
  commuting and `c` in a subgroup `C` on which `P` acts trivially modulo `⁅C, C⁆`, then
  `⁅P, P⁆ ≤ ⁅C, C⁆`.  For Thompson-like groups `z₀, z₁` carry the germs at the two ends and
  `C` is the compactly supported subgroup.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement

/-! ## Commutator identities -/

section GroupIdentities

variable {M : Type*} [Group M]

theorem commutatorElement_mul_left_of_commute {a a' b : M} (h : Commute a' b) :
    ⁅a * a', b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  calc a * a' * b * (a * a')⁻¹ * b⁻¹ = a * (a' * b) * a'⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * a') * a'⁻¹ * a⁻¹ * b⁻¹ := by rw [h.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_right_of_commute {a b b' : M} (h : Commute a b') :
    ⁅a, b * b'⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  have h' : b' * a⁻¹ = a⁻¹ * b' := (Commute.inv_left_iff.mpr h).eq.symm
  calc a * (b * b') * a⁻¹ * (b * b')⁻¹ = a * b * (b' * a⁻¹) * b'⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * b') * b'⁻¹ * b⁻¹ := by rw [h']
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_eq_conj (k a b : M) :
    ⁅a, b⁆ = k⁻¹ * ⁅k * a * k⁻¹, k * b * k⁻¹⁆ * k⁻¹⁻¹ := by
  simp only [commutatorElement_def]
  group

/-- `⁅x, b⁆ ∈ N` for `x ∈ N` and `b` in a subgroup normalizing `N`. -/
theorem commutatorElement_mem_left {N L : Subgroup M}
    (hN : ∀ n ∈ N, ∀ g ∈ L, g * n * g⁻¹ ∈ N) {x b : M} (hx : x ∈ N) (hb : b ∈ L) :
    ⁅x, b⁆ ∈ N := by
  have e : ⁅x, b⁆ = x * (b * x⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact N.mul_mem hx (hN _ (N.inv_mem hx) _ hb)

/-- `⁅a, f⁆ ∈ N` for `f ∈ N` and `a` in a subgroup normalizing `N`. -/
theorem commutatorElement_mem_right {N L : Subgroup M}
    (hN : ∀ n ∈ N, ∀ g ∈ L, g * n * g⁻¹ ∈ N) {a f : M} (ha : a ∈ L) (hf : f ∈ N) :
    ⁅a, f⁆ ∈ N := by
  rw [commutatorElement_def]
  exact N.mul_mem (hN _ hf _ ha) (N.inv_mem hf)

theorem commutator_le_self (G : Subgroup M) : ⁅G, G⁆ ≤ G := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact G.mul_mem (G.mul_mem (G.mul_mem h₁ h₂) (G.inv_mem h₁)) (G.inv_mem h₂)

end GroupIdentities

/-! ## Supports -/

section Supports

variable {X : Type*}

/-- `f` fixes every point outside `U`. -/
def SupportedIn (f : Equiv.Perm X) (U : Set X) : Prop := ∀ x, x ∉ U → f x = x

theorem SupportedIn.mono {f : Equiv.Perm X} {U V : Set X} (h : SupportedIn f U)
    (hUV : U ⊆ V) : SupportedIn f V :=
  fun x hx => h x (fun hxU => hx (hUV hxU))

theorem supportedIn_one (U : Set X) : SupportedIn (1 : Equiv.Perm X) U := fun _ _ => rfl

theorem SupportedIn.inv {f : Equiv.Perm X} {U : Set X} (h : SupportedIn f U) :
    SupportedIn f⁻¹ U := by
  intro x hx
  have hfx : f x = x := h x hx
  calc f⁻¹ x = f⁻¹ (f x) := by rw [hfx]
    _ = x := Equiv.symm_apply_apply f x

theorem SupportedIn.mul {f g : Equiv.Perm X} {U V : Set X} (hf : SupportedIn f U)
    (hg : SupportedIn g V) : SupportedIn (f * g) (U ∪ V) := by
  intro x hx
  have hxU : x ∉ U := fun h => hx (Or.inl h)
  have hxV : x ∉ V := fun h => hx (Or.inr h)
  rw [Equiv.Perm.mul_apply, hg x hxV, hf x hxU]

theorem SupportedIn.conj {g : Equiv.Perm X} {U : Set X} (h : SupportedIn g U)
    (k : Equiv.Perm X) : SupportedIn (k * g * k⁻¹) (k '' U) := by
  intro x hx
  have hk : k⁻¹ x ∉ U := by
    intro hU
    exact hx ⟨k⁻¹ x, hU, Equiv.apply_symm_apply k x⟩
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h _ hk]
  exact Equiv.apply_symm_apply k x

/-- A permutation supported in `U` maps `U` into `U`. -/
theorem SupportedIn.apply_mem {f : Equiv.Perm X} {U : Set X} (h : SupportedIn f U) {x : X}
    (hx : x ∈ U) : f x ∈ U := by
  by_contra hfx
  have h2 : f x = x := f.injective (h _ hfx)
  exact hfx (by rw [h2]; exact hx)

/-- Permutations supported in disjoint sets commute. -/
theorem commute_of_supportedIn {f g : Equiv.Perm X} {U V : Set X} (hf : SupportedIn f U)
    (hg : SupportedIn g V) (hUV : Disjoint U V) : Commute f g := by
  show f * g = g * f
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  by_cases hxU : x ∈ U
  · have hxV : x ∉ V := Set.disjoint_left.mp hUV hxU
    have hfxV : f x ∉ V := Set.disjoint_left.mp hUV (hf.apply_mem hxU)
    rw [hg x hxV, hg _ hfxV]
  · rw [hf x hxU]
    by_cases hxV : x ∈ V
    · have hgxU : g x ∉ U := Set.disjoint_right.mp hUV (hg.apply_mem hxV)
      rw [hf _ hgxU]
    · rw [hg x hxV, hf x hxU]

/-- **Epstein's trick.**  If `f` moves `U` off itself and `a, b` are supported in `U`, then
`⁅⁅a, f⁆, b⁆ = ⁅a, b⁆`: the factor `f a⁻¹ f⁻¹` of `⁅a, f⁆` is supported in `f '' U`. -/
theorem commutatorElement_commutatorElement_of_displaced {f a b : Equiv.Perm X} {U : Set X}
    (hdisp : Disjoint (f '' U) U) (ha : SupportedIn a U) (hb : SupportedIn b U) :
    ⁅⁅a, f⁆, b⁆ = ⁅a, b⁆ := by
  have hsplit : ⁅a, f⁆ = a * (f * a⁻¹ * f⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [hsplit]
  exact commutatorElement_mul_left_of_commute (commute_of_supportedIn (ha.inv.conj f) hb hdisp)

/-- Two permutations agreeing on a set `W` conjugate a permutation supported in `W` alike. -/
theorem conj_eq_of_eqOn {c d g : Equiv.Perm X} {W : Set X} (hc : SupportedIn c W)
    (hdg : ∀ x ∈ W, d x = g x) : d * c * d⁻¹ = g * c * g⁻¹ := by
  ext x
  simp only [Equiv.Perm.mul_apply]
  by_cases hx : g⁻¹ x ∈ W
  · have hgx : g (g⁻¹ x) = x := Equiv.apply_symm_apply g x
    have hdx : d⁻¹ x = g⁻¹ x := by
      have h1 : d (g⁻¹ x) = x := by rw [hdg _ hx, hgx]
      calc d⁻¹ x = d⁻¹ (d (g⁻¹ x)) := by rw [h1]
        _ = g⁻¹ x := Equiv.symm_apply_apply d _
    rw [hdx, hdg _ (hc.apply_mem hx)]
  · have hcx : c (g⁻¹ x) = g⁻¹ x := hc _ hx
    have hdx : d⁻¹ x ∉ W := by
      intro hW
      apply hx
      have h1 : g (d⁻¹ x) = x := by
        rw [← hdg _ hW]
        exact Equiv.apply_symm_apply d x
      have h2 : g⁻¹ x = d⁻¹ x := by
        calc g⁻¹ x = g⁻¹ (g (d⁻¹ x)) := by rw [h1]
          _ = d⁻¹ x := Equiv.symm_apply_apply g _
      rw [h2]
      exact hW
    rw [hc _ hdx, hcx]
    exact (Equiv.apply_symm_apply d x).trans (Equiv.apply_symm_apply g x).symm

/-- The commutator `⁅k, z⁆` conjugates like `k` on permutations supported away from `z '' W`,
where `W` supports `k`. -/
theorem conj_commutatorElement_eq {k z g : Equiv.Perm X} {W V : Set X}
    (hk : SupportedIn k W) (hg : SupportedIn g V) (hz : Disjoint (z '' W) V) :
    ⁅k, z⁆ * g * ⁅k, z⁆⁻¹ = k * g * k⁻¹ := by
  have hsplit : ⁅k, z⁆ = k * (z * k⁻¹ * z⁻¹) := by
    rw [commutatorElement_def]
    group
  have hc : Commute (z * k⁻¹ * z⁻¹) g := commute_of_supportedIn (hk.inv.conj z) hg hz
  rw [hsplit]
  calc k * (z * k⁻¹ * z⁻¹) * g * (k * (z * k⁻¹ * z⁻¹))⁻¹
      = k * ((z * k⁻¹ * z⁻¹) * g) * (z * k⁻¹ * z⁻¹)⁻¹ * k⁻¹ := by group
    _ = k * (g * (z * k⁻¹ * z⁻¹)) * (z * k⁻¹ * z⁻¹)⁻¹ * k⁻¹ := by rw [hc.eq]
    _ = k * g * k⁻¹ := by group

end Supports

/-! ## The simplicity criterion -/

section Criterion

variable {X : Type*}

/-- The room `⁅G, G⁆` has inside `U`: for all `g₁, g₂ ∈ G` some `k ∈ ⁅G, G⁆` moves the supports of
both into a set `U₁ ⊆ U`, and elements of `G` move `U₁` into two further disjoint parts of `U`. -/
def CommutatorRoom (G : Subgroup (Equiv.Perm X)) (U : Set X) : Prop :=
  ∀ g₁ ∈ G, ∀ g₂ ∈ G, ∃ k ∈ ⁅G, G⁆, ∃ k₂ ∈ G, ∃ k₃ ∈ G, ∃ U₁ U₂ U₃ : Set X,
    SupportedIn (k * g₁ * k⁻¹) U₁ ∧ SupportedIn (k * g₂ * k⁻¹) U₁ ∧
    k₂ '' U₁ ⊆ U₂ ∧ k₃ '' U₁ ⊆ U₃ ∧ Disjoint U₁ U₂ ∧ Disjoint U₁ U₃ ∧ Disjoint U₂ U₃ ∧
    U₁ ∪ U₂ ∪ U₃ ⊆ U

/-- **Higman–Epstein.**  A subgroup `N` normalized by `⁅G, G⁆`, containing a permutation `f`
that moves `U` off itself, where `⁅G, G⁆` has room inside `U`, contains `⁅G, G⁆`. -/
theorem commutator_le_of_normal_commutator (G N : Subgroup (Equiv.Perm X))
    (hN : ∀ n ∈ N, ∀ g ∈ ⁅G, G⁆, g * n * g⁻¹ ∈ N) {f : Equiv.Perm X} (hf : f ∈ N)
    {U : Set X} (hdisp : Disjoint (f '' U) U) (hroom : CommutatorRoom G U) :
    ⁅G, G⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨k, hk, k₂, hk₂, k₃, hk₃, U₁, U₂, U₃, ha₁, hb₁, h₂, h₃, d12, d13, d23, hsub⟩ :=
    hroom g₁ hg₁ g₂ hg₂
  have hkG : k ∈ G := commutator_le_self G hk
  have ha₁G : k * g₁ * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hkG hg₁) (G.inv_mem hkG)
  have hb₁G : k * g₂ * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hkG hg₂) (G.inv_mem hkG)
  have haM : ⁅k * g₁ * k⁻¹, k₂⁆ ∈ ⁅G, G⁆ := Subgroup.commutator_mem_commutator ha₁G hk₂
  have hbM : ⁅k * g₂ * k⁻¹, k₃⁆ ∈ ⁅G, G⁆ := Subgroup.commutator_mem_commutator hb₁G hk₃
  have hc : SupportedIn (k₂ * (k * g₁ * k⁻¹)⁻¹ * k₂⁻¹) U₂ := (ha₁.inv.conj k₂).mono h₂
  have hd : SupportedIn (k₃ * (k * g₂ * k⁻¹)⁻¹ * k₃⁻¹) U₃ := (hb₁.inv.conj k₃).mono h₃
  have hsa : ⁅k * g₁ * k⁻¹, k₂⁆ = (k * g₁ * k⁻¹) * (k₂ * (k * g₁ * k⁻¹)⁻¹ * k₂⁻¹) := by
    rw [commutatorElement_def]
    group
  have hsb : ⁅k * g₂ * k⁻¹, k₃⁆ = (k * g₂ * k⁻¹) * (k₃ * (k * g₂ * k⁻¹)⁻¹ * k₃⁻¹) := by
    rw [commutatorElement_def]
    group
  have h12 : U₁ ∪ U₂ ⊆ U := by
    intro x hx
    rcases hx with hx | hx
    · exact hsub (Or.inl (Or.inl hx))
    · exact hsub (Or.inl (Or.inr hx))
  have h13 : U₁ ∪ U₃ ⊆ U := by
    intro x hx
    rcases hx with hx | hx
    · exact hsub (Or.inl (Or.inl hx))
    · exact hsub (Or.inr hx)
  have haU : SupportedIn ⁅k * g₁ * k⁻¹, k₂⁆ U := by
    rw [hsa]
    exact (ha₁.mul hc).mono h12
  have hbU : SupportedIn ⁅k * g₂ * k⁻¹, k₃⁆ U := by
    rw [hsb]
    exact (hb₁.mul hd).mono h13
  have hN1 : ⁅⁅k * g₁ * k⁻¹, k₂⁆, f⁆ ∈ N := commutatorElement_mem_right hN haM hf
  have hN2 : ⁅⁅⁅k * g₁ * k⁻¹, k₂⁆, f⁆, ⁅k * g₂ * k⁻¹, k₃⁆⁆ ∈ N :=
    commutatorElement_mem_left hN hN1 hbM
  rw [commutatorElement_commutatorElement_of_displaced hdisp haU hbU] at hN2
  have hcb : Commute (k₂ * (k * g₁ * k⁻¹)⁻¹ * k₂⁻¹)
      ((k * g₂ * k⁻¹) * (k₃ * (k * g₂ * k⁻¹)⁻¹ * k₃⁻¹)) :=
    commute_of_supportedIn hc (hb₁.mul hd) (Set.disjoint_union_right.mpr ⟨d12.symm, d23⟩)
  have had : Commute (k * g₁ * k⁻¹) (k₃ * (k * g₂ * k⁻¹)⁻¹ * k₃⁻¹) :=
    commute_of_supportedIn ha₁ hd d13
  rw [hsa, hsb, commutatorElement_mul_left_of_commute hcb,
    commutatorElement_mul_right_of_commute had] at hN2
  rw [commutatorElement_eq_conj k g₁ g₂]
  exact hN _ hN2 _ ((⁅G, G⁆).inv_mem hk)

/-- **Simplicity of `⁅G, G⁆`**, when every nontrivial element of `⁅G, G⁆` displaces a set in
which `⁅G, G⁆` has room. -/
theorem isSimpleGroup_commutator (G : Subgroup (Equiv.Perm X)) (hne : ⁅G, G⁆ ≠ ⊥)
    (hdisp : ∀ f ∈ ⁅G, G⁆, f ≠ 1 → ∃ U : Set X, Disjoint (f '' U) U ∧ CommutatorRoom G U) :
    IsSimpleGroup ↥⁅G, G⁆ := by
  have hnt : Nontrivial ↥⁅G, G⁆ := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun H hH => ?_ }
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨⟨f, hfM⟩, hfH⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext (Subtype.ext h))
  have hNnorm : ∀ n ∈ H.map ⁅G, G⁆.subtype, ∀ g ∈ ⁅G, G⁆,
      g * n * g⁻¹ ∈ H.map ⁅G, G⁆.subtype := by
    rintro n ⟨x, hxH, rfl⟩ g hg
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hH.conj_mem x hxH ⟨g, hg⟩, rfl⟩
  have hfN : f ∈ H.map ⁅G, G⁆.subtype := ⟨⟨f, hfM⟩, hfH, rfl⟩
  obtain ⟨U, hU, hroom⟩ := hdisp f hfM hf1'
  have hle := commutator_le_of_normal_commutator G (H.map ⁅G, G⁆.subtype) hNnorm hfN hU hroom
  rw [Subgroup.eq_top_iff']
  intro x
  obtain ⟨y, hyH, hyx⟩ := hle x.2
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hyH

end Criterion

/-! ## Germs and the derived subgroup -/

section Decomposition

variable {M : Type*} [Group M]

/-- If `P` acts trivially on `C` modulo `⁅C, C⁆`, and `P = ⟨z₀⟩⟨z₁⟩C` with `z₀, z₁` commuting,
then `⁅P, P⁆ ≤ ⁅C, C⁆`. -/
theorem commutator_le_of_decomposition (P C : Subgroup M)
    (hconj : ∀ g ∈ P, ∀ c ∈ C, ⁅g, c⁆ ∈ ⁅C, C⁆) {z₀ z₁ : M} (hz₀ : z₀ ∈ P) (hz₁ : z₁ ∈ P)
    (hz : Commute z₀ z₁) (hdec : ∀ g ∈ P, ∃ i j : ℤ, ∃ c ∈ C, g = z₀ ^ i * z₁ ^ j * c) :
    ⁅P, P⁆ ≤ ⁅C, C⁆ := by
  have hCconj : ∀ g ∈ P, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    have e : g * c * g⁻¹ = ⁅g, c⁆ * c := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact C.mul_mem (commutator_le_self C (hconj g hg c hc)) hc
  have hK : ∀ g ∈ P, ∀ x ∈ ⁅C, C⁆, g * x * g⁻¹ ∈ ⁅C, C⁆ := by
    intro g hg x hx
    have hle : ⁅C, C⁆ ≤ (⁅C, C⁆).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro c₁ hc₁ c₂ hc₂
      rw [Subgroup.mem_comap]
      have e : (MulAut.conj g).toMonoidHom ⁅c₁, c₂⁆ = ⁅g * c₁ * g⁻¹, g * c₂ * g⁻¹⁆ := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (hCconj g hg c₁ hc₁) (hCconj g hg c₂ hc₂)
    have h := hle hx
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨i, j, c, hc, rfl⟩ := hdec g hg
  obtain ⟨i', j', c', hc', rfl⟩ := hdec h hh
  have hw : z₀ ^ i * z₁ ^ j ∈ P := P.mul_mem (P.zpow_mem hz₀ i) (P.zpow_mem hz₁ j)
  have hw' : z₀ ^ i' * z₁ ^ j' ∈ P := P.mul_mem (P.zpow_mem hz₀ i') (P.zpow_mem hz₁ j')
  have hcomm : Commute (z₀ ^ i' * z₁ ^ j') (z₀ ^ i * z₁ ^ j) := by
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact (Commute.refl z₀).zpow_zpow i' i
    · exact hz.zpow_zpow i' j
    · exact (hz.zpow_zpow i j').symm
    · exact (Commute.refl z₁).zpow_zpow j' j
  have e1 : ⁅z₀ ^ i * z₁ ^ j * c, z₀ ^ i' * z₁ ^ j' * c'⁆ =
      ((z₀ ^ i * z₁ ^ j) * ⁅c, z₀ ^ i' * z₁ ^ j' * c'⁆ * (z₀ ^ i * z₁ ^ j)⁻¹) *
        ⁅z₀ ^ i' * z₁ ^ j' * c', z₀ ^ i * z₁ ^ j⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  have e2 : ⁅z₀ ^ i' * z₁ ^ j' * c', z₀ ^ i * z₁ ^ j⁆ =
      ((z₀ ^ i' * z₁ ^ j') * ⁅c', z₀ ^ i * z₁ ^ j⁆ * (z₀ ^ i' * z₁ ^ j')⁻¹) *
        ⁅z₀ ^ i' * z₁ ^ j', z₀ ^ i * z₁ ^ j⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e1, e2, commutatorElement_eq_one_iff_commute.mpr hcomm, mul_one]
  have hK1 : ⁅c, z₀ ^ i' * z₁ ^ j' * c'⁆ ∈ ⁅C, C⁆ := by
    rw [← commutatorElement_inv]
    exact (⁅C, C⁆).inv_mem (hconj _ hh c hc)
  have hK2 : ⁅c', z₀ ^ i * z₁ ^ j⁆ ∈ ⁅C, C⁆ := by
    rw [← commutatorElement_inv]
    exact (⁅C, C⁆).inv_mem (hconj _ hw c' hc')
  exact (⁅C, C⁆).mul_mem (hK _ hw _ hK1) ((⁅C, C⁆).inv_mem (hK _ hw' _ hK2))

end Decomposition

#audit_axioms GroupApproximation.HydeLodha.commutator_le_of_normal_commutator
#audit_axioms GroupApproximation.HydeLodha.isSimpleGroup_commutator
#audit_axioms GroupApproximation.HydeLodha.commutator_le_of_decomposition

end HydeLodha
end GroupApproximation
