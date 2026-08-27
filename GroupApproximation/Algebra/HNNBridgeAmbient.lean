import GroupApproximation.Algebra.CoprodIAltWord

/-!
# The ambient group of the Higman--Neumann--Neumann bridge

The bridge is built inside `A ∗ F₂`, and the two families whose freeness it
needs are `uₖ = a^{k+1} b a^{-(k+1)}` and `gen k · uₖ`.  The first lives in the
free part; the second mixes `A`-letters with `F₂`-letters, and its expansion
runs over **three** factors --- `A`, `⟨a⟩`, `⟨b⟩` --- in the index pattern
`0,1,2,1,0,1,2,1,…`.

**Do not build the ambient as `Monoid.Coprod A (FreeGroup (Fin 2))` and then
try to reach the three-factor picture.**  That needs associativity of free
products, `A ∗ (ℤ ∗ ℤ) ≅ A ∗ ℤ ∗ ℤ`, and pinned Mathlib has no such lemma:
`CoprodI` is indexed and there is nothing relating a nested binary coproduct to
a three-element indexed one.  Building it would be a development in itself, and
it is unnecessary.

Instead the ambient is *defined* as the three-factor free product from the
start.  `a` and `b` are then letters of two of the factors rather than elements
of a separately-constructed `F₂`, the expansion of either family is immediately
a list of letters, and `CoprodIAltWord.listProd_ne_one` --- the general
criterion, which asks only for nontrivial letters and distinct consecutive
indices --- applies to both without any transfer.

`Algebra.HNNBridgeFreeness` proves the first family free in `FreeGroup (Fin 2)`;
the argument there is the model for the second, but it should be re-run in this
ambient rather than transported into it.
-/

namespace GroupApproximation
namespace HNNBridgeAmbient

open Monoid Monoid.CoprodI

/-- The three factors: the group being embedded, and two infinite cyclic
groups. -/
def fam3 (A : Type) (i : Fin 3) : Type :=
  if i = 0 then A else FreeGroup Unit

instance fam3_group (A : Type) [Group A] (i : Fin 3) : Group (fam3 A i) := by
  unfold fam3
  split <;> infer_instance

noncomputable instance fam3_decEq (A : Type) [Group A] [DecidableEq A]
    (i : Fin 3) : DecidableEq (fam3 A i) := Classical.decEq _

variable (A : Type) [Group A]

/-- The ambient group `A ∗ ℤ ∗ ℤ`. -/
abbrev Amb : Type := CoprodI (fam3 A)

/-- The copy of `A`. -/
def incl : A →* Amb A := CoprodI.of (M := fam3 A) (i := 0)

theorem incl_injective : Function.Injective (incl A) :=
  CoprodI.of_injective (M := fam3 A) 0

variable {A}

/-- The generator of the first cyclic factor. -/
def a3 : Amb A := CoprodI.of (i := 1) (FreeGroup.of Unit.unit)

/-- The generator of the second cyclic factor. -/
def b3 : Amb A := CoprodI.of (i := 2) (FreeGroup.of Unit.unit)

/-- The conjugate family, in the ambient. -/
def u3 (k : ℕ) : Amb A := a3 ^ (k + 1) * b3 * (a3 ^ (k + 1))⁻¹

/-- The second family: the first, translated by the generators of `A`. -/
def v3 (gen : ℕ → A) (k : ℕ) : Amb A := incl A (gen k) * u3 k

theorem u3_zpow (k : ℕ) (n : ℤ) :
    (u3 k : Amb A) ^ n = a3 ^ ((k : ℤ) + 1) * b3 ^ n * a3 ^ (-((k : ℤ) + 1)) := by
  rw [u3, conj_zpow]
  have hk : (k : ℤ) + 1 = (↑(k + 1) : ℤ) := by omega
  rw [hk, zpow_natCast, zpow_neg, zpow_natCast]

/-! ## Normalizing the generating family

The expansion of the second family `gen k · uₖ` is uniform only if the
`A`-letters are genuinely there.  If `gen k = 1` the block degenerates: the
`A`-letter must be *omitted*, and then two consecutive `a`-blocks meet at the
same index and cancel rather than merging into something nontrivial --- indeed
`v k = u k` in that case, and its powers telescope, which is a different shape
of word altogether.

The case is removable.  Replacing any generator that happens to be trivial by
one fixed nontrivial element changes neither the spanning property (adding an
element of the group and deleting `1` are both invisible to the closure) nor
anything else the bridge uses.  So the construction may assume throughout that
the family never takes the value `1`, and the expansion stays uniform.

If `A` is trivial there is nothing to do: it embeds in any finitely generated
group. -/

theorem exists_spanning_ne_one {A : Type} [Group A] [Nontrivial A] (gen : ℕ → A)
    (hspan : Subgroup.closure (Set.range gen) = ⊤) :
    ∃ gen' : ℕ → A, (∀ k, gen' k ≠ 1) ∧
      Subgroup.closure (Set.range gen') = ⊤ := by
  classical
  obtain ⟨g₀, hg₀⟩ := exists_ne (1 : A)
  refine ⟨fun k ↦ if gen k = 1 then g₀ else gen k, ?_, ?_⟩
  · intro k
    by_cases h : gen k = 1
    · simpa [h] using hg₀
    · simp [h]
  · rw [Subgroup.eq_top_iff']
    intro x
    have hsub : Set.range gen ⊆
        (Subgroup.closure
          (Set.range fun k ↦ if gen k = 1 then g₀ else gen k) : Set A) := by
      rintro _ ⟨k, rfl⟩
      by_cases h : gen k = 1
      · rw [h]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨k, by simp [h]⟩
    have hle := (Subgroup.closure_le _).2 hsub
    rw [hspan] at hle
    exact hle (Subgroup.mem_top x)

end HNNBridgeAmbient
end GroupApproximation
