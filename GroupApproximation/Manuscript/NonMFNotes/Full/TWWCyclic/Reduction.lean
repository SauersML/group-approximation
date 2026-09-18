import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.FiniteIndex

/-!
# Reducing the cyclic extension step to the infinite-order case

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378), cyclic extension step of `TWW.SolvableInduction`
(Ozawa--Rørdam--Sato, GAFA 25 (2015), Thm 2 and §3).

Let `k` normalize `H`. Then `H ⊔ ⟨k⟩ / H` is cyclic, so it is either finite or
infinite. The finite case is `isModelled_sup_zpowers_of_pow_mem`, which needs no
amenability. This file proves:

* `isModelled_mono`: `IsModelled` is inherited by smaller subgroups.
* `isCyclicExtensionClosed_isModelled_of_isModelled_top`: models on the whole
  group give cyclic closure.
* `isCyclicExtensionClosed_isModelled_iff`: cyclic closure of `IsModelled` is
  equivalent to closure under extensions by elements of infinite order modulo
  the subgroup (`IsInfiniteOrderExtensionClosed`).
* `isCyclicExtensionClosed_isModelled_of_isOfFinOrder`: in a torsion group,
  `IsModelled` is closed under cyclic extensions.
-/

namespace GroupApproximation.Full.TWWCyclic

variable {G : Type} [Group G]

/-- A subgroup of a modelled subgroup is modelled. -/
theorem isModelled_mono {H K : Subgroup G} (hHK : H ≤ K) (hK : TWW.IsModelled K) :
    TWW.IsModelled H :=
  fun F hF ε hε => hK F (fun g hg => hHK (hF g hg)) ε hε

/-- Models on the whole group make `IsModelled` closed under cyclic extensions. -/
theorem isCyclicExtensionClosed_isModelled_of_isModelled_top
    (h : TWW.IsModelled (⊤ : Subgroup G)) :
    TWW.IsCyclicExtensionClosed (TWW.IsModelled (G := G)) :=
  fun _ _ _ _ _ => isModelled_mono le_top h

/-- Closure of `Q` under adjoining a normalizing element none of whose positive
powers lies in the subgroup. -/
def IsInfiniteOrderExtensionClosed (Q : Subgroup G → Prop) : Prop :=
  ∀ (H : Subgroup G) (k : G), (∀ h ∈ H, k * h * k⁻¹ ∈ H) →
    (∀ h ∈ H, k⁻¹ * h * k ∈ H) → (∀ m : ℕ, 0 < m → k ^ m ∉ H) → Q H →
      Q (H ⊔ Subgroup.zpowers k)

/-- **Dichotomy.** `IsModelled` is closed under normalizing cyclic extensions if
and only if it is closed under those of infinite order modulo the subgroup. The
finite-order case is `isModelled_sup_zpowers_of_pow_mem`. -/
theorem isCyclicExtensionClosed_isModelled_iff :
    TWW.IsCyclicExtensionClosed (TWW.IsModelled (G := G)) ↔
      IsInfiniteOrderExtensionClosed (TWW.IsModelled (G := G)) := by
  constructor
  · intro h H k hk hk' _ hH
    exact h H k hk hk' hH
  · intro h H k hk hk' hH
    by_cases hfin : ∃ m : ℕ, 0 < m ∧ k ^ m ∈ H
    · obtain ⟨m, hm, hkm⟩ := hfin
      exact isModelled_sup_zpowers_of_pow_mem hk hk' hm hkm hH
    · exact h H k hk hk' (fun m hm hkm => hfin ⟨m, hm, hkm⟩) hH

/-- In a torsion group, `IsModelled` is closed under normalizing cyclic
extensions. -/
theorem isCyclicExtensionClosed_isModelled_of_isOfFinOrder (hG : ∀ g : G, IsOfFinOrder g) :
    TWW.IsCyclicExtensionClosed (TWW.IsModelled (G := G)) := by
  intro H k hk hk' hH
  obtain ⟨m, hm, hkm⟩ := isOfFinOrder_iff_pow_eq_one.mp (hG k)
  have hmem : k ^ m ∈ H := by
    rw [hkm]
    exact H.one_mem
  exact isModelled_sup_zpowers_of_pow_mem hk hk' hm hmem hH

end GroupApproximation.Full.TWWCyclic
