import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.OperatorMFPositiveControls
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Infinite multiplicity of the non-MF phenomenon

The manuscript records that the phenomenon is not a single group: the
family `E × ℤ^k` is finitely presented, pairwise nonisomorphic, and non-MF
for every `k`.  Each half is elementary on top of machine-checked inputs,
and all three are proved here.

* Finite presentation needs direct products of finitely presented groups,
  which `Algebra.ProductFinitePresentation` supplies; `ℤ^k` is finitely
  presented by induction on the coordinate split.
* Non-MF is heredity: the first factor embeds, and operator-MF passes to
  subgroups, so a non-MF factor obstructs the product.
* Pairwise nonisomorphism is counted rather than ranked.  The manuscript
  separates the members by the torsion-free rank of the abelianization;
  the count of homomorphisms into the two-element group is the same
  invariant read mod `2`, and it needs no structure theory: homomorphisms
  out of a product into an abelian group split, `ℤ^k` contributes exactly
  `2^k` of them, and the factor contributed by `E` is finite and nonzero
  because `E` is finitely generated.  So `m · 2^k` determines `k`.

The second multiplicity sense of the manuscript --- pairing `E` with the
continuum of two-generator groups of B. H. Neumann --- is not formalized
here; it needs Neumann's continuum family, which is a separate
construction.
-/

namespace GroupApproximation
namespace ProductMultiplicity

open ProductFinitePresentation

universe u

/-! ## The free abelian group of rank `k` -/

/-- The free abelian group of rank `k`, written multiplicatively. -/
abbrev IntPow (k : ℕ) : Type := Fin k → Multiplicative ℤ

/-- Splitting off the first coordinate of `ℤ^{k+1}`. -/
def intPowSucc (k : ℕ) : IntPow (k + 1) ≃* Multiplicative ℤ × IntPow k where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    obtain ⟨a, g⟩ := p
    simp [Fin.tail_cons]
  map_mul' _ _ := rfl

instance : Subsingleton (IntPow 0) := ⟨fun _ _ ↦ funext fun i ↦ isEmptyElim i⟩

theorem intPow_finitelyPresented :
    ∀ k : ℕ, Group.IsFinitelyPresented (IntPow k)
  | 0 => by
      haveI : Finite (IntPow 0) := Finite.of_subsingleton
      infer_instance
  | k + 1 => by
      haveI := intPow_finitelyPresented k
      exact Group.IsFinitelyPresented.equiv (intPowSucc k).symm

/-! ## The family -/

/-- The multiplicity family `G × ℤ^k`. -/
abbrev Family (G : Type u) [Group G] (k : ℕ) : Type u := G × IntPow k

theorem family_finitelyPresented (G : Type u) [Group G]
    [Group.IsFinitelyPresented G] (k : ℕ) :
    Group.IsFinitelyPresented (Family G k) := by
  haveI := intPow_finitelyPresented k
  infer_instance

theorem not_isOperatorMF_family {G : Type u} [Group G] (h : ¬ IsOperatorMF G)
    (k : ℕ) : ¬ IsOperatorMF (Family G k) := by
  intro hMF
  refine h (IsOperatorMF.comap hMF (MonoidHom.inl G (IntPow k)) ?_)
  intro a b hab
  simpa using congrArg Prod.fst hab

/-! ## Counting homomorphisms into the two-element group -/

/-- The two-element group, used as a counting target. -/
abbrev TwoGroup : Type := Multiplicative (ZMod 2)

theorem card_twoGroup : Nat.card TwoGroup = 2 := by
  have hcard : Nat.card TwoGroup = Nat.card (ZMod 2) :=
    Nat.card_congr (Multiplicative.ofAdd (α := ZMod 2)).symm
  rw [hcard, Nat.card_eq_fintype_card, ZMod.card]

/-- Precomposition with an isomorphism is a bijection on homomorphism
sets. -/
def homCongrLeft {A B P : Type*} [Group A] [Group B] [Group P] (e : A ≃* B) :
    (B →* P) ≃ (A →* P) where
  toFun f := f.comp e.toMonoidHom
  invFun f := f.comp e.symm.toMonoidHom
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

/-- Homomorphisms out of a direct product into an abelian group split. -/
def homProdEquiv (A B P : Type*) [Group A] [Group B] [CommGroup P] :
    (A × B →* P) ≃ (A →* P) × (B →* P) where
  toFun f := (f.comp (MonoidHom.inl A B), f.comp (MonoidHom.inr A B))
  invFun p := p.1.noncommCoprod p.2 fun _ _ ↦ Commute.all _ _
  left_inv f := MonoidHom.noncommCoprod_unique f
  right_inv p := by
    obtain ⟨f, g⟩ := p
    simp

theorem card_hom_prod (A B P : Type*) [Group A] [Group B] [CommGroup P] :
    Nat.card (A × B →* P) = Nat.card (A →* P) * Nat.card (B →* P) := by
  rw [Nat.card_congr (homProdEquiv A B P), Nat.card_prod]

theorem card_hom_multiplicativeInt (P : Type*) [CommGroup P] :
    Nat.card (Multiplicative ℤ →* P) = Nat.card P :=
  (Nat.card_congr (zpowersHom P)).symm

theorem card_hom_intPow (P : Type*) [CommGroup P] :
    ∀ k : ℕ, Nat.card (IntPow k →* P) = Nat.card P ^ k
  | 0 => by
      haveI : Subsingleton (IntPow 0 →* P) :=
        ⟨fun f g ↦ MonoidHom.ext fun x ↦ by
          rw [Subsingleton.elim x 1, map_one, map_one]⟩
      rw [pow_zero]
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  | k + 1 => by
      rw [← Nat.card_congr (homCongrLeft (intPowSucc k)), card_hom_prod,
        card_hom_multiplicativeInt, card_hom_intPow P k, pow_succ]
      ring

/-- A finitely generated group has only finitely many homomorphisms to a
finite group: a homomorphism is determined by its values on a finite
generating set. -/
theorem finite_hom_of_fg (A : Type*) [Group A] [Group.FG A] (P : Type*)
    [Group P] [Finite P] : Finite (A →* P) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp ‹Group.FG A›
  haveI : Finite S := hSfin.to_subtype
  refine Finite.of_injective (fun f : A →* P ↦ fun s : S ↦ f s) ?_
  intro f g hfg
  refine MonoidHom.eq_of_eqOn_dense hS ?_
  intro x hx
  exact congrFun hfg ⟨x, hx⟩

/-! ## Pairwise nonisomorphism -/

theorem card_hom_family (G : Type u) [Group G] (k : ℕ) :
    Nat.card (Family G k →* TwoGroup) = Nat.card (G →* TwoGroup) * 2 ^ k := by
  rw [card_hom_prod, card_hom_intPow, card_twoGroup]

/-- **The members of the family are pairwise nonisomorphic.**  The
homomorphism count into the two-element group is `m · 2^k` with `m` finite
and nonzero, so it determines `k`. -/
theorem eq_of_family_mulEquiv {G : Type u} [Group G] [Group.FG G] {k l : ℕ}
    (e : Family G k ≃* Family G l) : k = l := by
  haveI : Finite (G →* TwoGroup) := finite_hom_of_fg G TwoGroup
  haveI : Nonempty (G →* TwoGroup) := ⟨1⟩
  have hpos : 0 < Nat.card (G →* TwoGroup) := Nat.card_pos
  have hcard :
      Nat.card (G →* TwoGroup) * 2 ^ k = Nat.card (G →* TwoGroup) * 2 ^ l := by
    rw [← card_hom_family, ← card_hom_family]
    exact (Nat.card_congr (homCongrLeft e)).symm
  exact Nat.pow_right_injective (le_refl 2)
    (Nat.eq_of_mul_eq_mul_left hpos hcard)

/-! ## The chosen witness -/

open ChosenMarkedPresentation

/-- **Infinite multiplicity for the chosen witness.**  Every member of the
family `E × ℤ^k` is finitely presented and not operator-MF. -/
theorem chosenFamily_finitelyPresented_not_isOperatorMF (k : ℕ) :
    Group.IsFinitelyPresented (Family MarkedGroup k) ∧
      ¬ IsOperatorMF (Family MarkedGroup k) :=
  ⟨family_finitelyPresented MarkedGroup k,
    not_isOperatorMF_family ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF.2 k⟩

/-- The chosen family has pairwise nonisomorphic members. -/
theorem chosenFamily_eq_of_mulEquiv {k l : ℕ}
    (e : Family MarkedGroup k ≃* Family MarkedGroup l) : k = l := by
  haveI : Group.FG MarkedGroup :=
    fg_of_isFinitelyPresented MarkedGroup
  exact eq_of_family_mulEquiv e

/-- Closed form: there is an infinite family of pairwise nonisomorphic
finitely presented groups, none of them operator-MF. -/
theorem manuscriptInfiniteMultiplicity :
    ∃ F : ℕ → Type,
      ∃ _ : ∀ k, Group (F k),
        (∀ k, Group.IsFinitelyPresented (F k)) ∧
          (∀ k, ¬ IsOperatorMF (F k)) ∧
          (∀ k l, Nonempty (F k ≃* F l) → k = l) := by
  refine ⟨fun k ↦ Family MarkedGroup k, fun _ ↦ inferInstance,
    fun k ↦ (chosenFamily_finitelyPresented_not_isOperatorMF k).1,
    fun k ↦ (chosenFamily_finitelyPresented_not_isOperatorMF k).2, ?_⟩
  rintro k l ⟨e⟩
  exact chosenFamily_eq_of_mulEquiv e

end ProductMultiplicity
end GroupApproximation
