import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionVanishExt

/-!
# Homological algebra for the UCT step of Schafhauser's argument

Lane `TWWSchafhauser-3d3`, work order `WO-TWWSchafhauser-3d-3` ("UCT kills the class").
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). That
theorem cites Tikuisis--White--Winter, Ann. of Math. 185 (2017), Theorem A, through
C. Schafhauser, J. reine angew. Math. 759 (2020), §4--5.

This file contains the diagram chases in abelian groups that the Rosenberg--Schochet argument
(Duke Math. J. 55 (1987), §1) uses. All of them are unconditional.

* `IsDivisibleGroup.exists_descend`: `Hom(-, D)` is exact in the middle for divisible `D`.
  Together with `IsDivisibleGroup.exists_extension` this makes `B ↦ Hom(K_*(B), D)` a
  cohomology theory. That is the first step of Rosenberg--Schochet, Theorem 1.17.
* `injective_of_four_lemma`, `surjective_of_four_lemma`, `bijective_of_five_lemma`: the four
  and five lemmas for abelian groups. The five lemma compares two cohomology theories that
  agree on points.
* `injective_of_exact_of_subsingleton`, `eq_zero_of_exact_of_subsingleton`: in an exact
  sequence `E → KK¹(S, J) → Hom(K_*(S), K_*(J))` with `E = 0` (by `gradedExt_one_subsingleton`)
  the comparison map is injective. So a class whose boundary maps vanish is zero.
-/

namespace GroupApproximation.Full.TWWSchafhauser

universe u v w u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ v₄ v₅

noncomputable section

namespace IsDivisibleGroup

variable {D : Type u} [AddCommGroup D]

/-- **`Hom(-, D)` is exact in the middle for divisible `D`.** Let `M' → M → M''` be exact at
`M`, and let `φ : M → D` vanish on the image of `M'`. Then `φ` factors through `M''`. The map
`M → M''` need not be surjective: the factorisation through its image is extended to `M''`
by divisibility of `D`. -/
theorem exists_descend (hD : IsDivisibleGroup D) {M' : Type v} {M : Type w} {M'' : Type u₁}
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M''] (f : M' →+ M) (g : M →+ M'')
    (hexact : ∀ x : M, g x = 0 → ∃ y : M', f y = x) (φ : M →+ D)
    (hφ : ∀ y : M', φ (f y) = 0) :
    ∃ ψ : M'' →+ D, ∀ x : M, ψ (g x) = φ x := by
  have key : ∀ x x' : M, g x = g x' → φ x = φ x' := by
    intro x x' h
    obtain ⟨y, hy⟩ := hexact (x - x') (by rw [map_sub, h, sub_self])
    rw [← sub_eq_zero, ← map_sub φ, ← hy, hφ]
  let c : g.range → M := fun z => Classical.choose (AddMonoidHom.mem_range.mp z.2)
  have hc : ∀ z : g.range, g (c z) = z := fun z =>
    Classical.choose_spec (AddMonoidHom.mem_range.mp z.2)
  let ψ₀ : g.range →+ D := AddMonoidHom.mk' (fun z => φ (c z)) (by
    intro a b
    show φ (c (a + b)) = φ (c a) + φ (c b)
    rw [← map_add φ]
    apply key
    simp only [map_add, hc, AddSubgroup.coe_add])
  obtain ⟨ψ, hψ⟩ := hD.exists_extension g.range.subtype (AddSubgroup.subtype_injective g.range) ψ₀
  refine ⟨ψ, fun x => ?_⟩
  have hx : g x ∈ g.range := AddMonoidHom.mem_range.mpr ⟨x, rfl⟩
  have h1 : ψ (g x) = φ (c ⟨g x, hx⟩) := DFunLike.congr_fun hψ ⟨g x, hx⟩
  rw [h1]
  apply key
  exact hc ⟨g x, hx⟩

end IsDivisibleGroup

/-! ## The four and five lemmas -/

section FourFive

variable {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃} {A₄ : Type u₄} {A₅ : Type u₅}
  {B₁ : Type v₁} {B₂ : Type v₂} {B₃ : Type v₃} {B₄ : Type v₄} {B₅ : Type v₅}
  [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅]
  [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃] [AddCommGroup B₄] [AddCommGroup B₅]

/-- **Four lemma, injectivity half.** Take a commutative ladder
`A₁ → A₂ → A₃ → A₄` over `B₁ → B₂ → B₃ → B₄`. Assume the top row is a complex at `A₂` and exact
at `A₃`, and the bottom row is exact at `B₂`. If `α₁` is surjective and `α₂`, `α₄` are
injective, then `α₃` is injective. -/
theorem injective_of_four_lemma
    (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄)
    (g₁ : B₁ →+ B₂) (g₂ : B₂ →+ B₃) (g₃ : B₃ →+ B₄)
    (α₁ : A₁ →+ B₁) (α₂ : A₂ →+ B₂) (α₃ : A₃ →+ B₃) (α₄ : A₄ →+ B₄)
    (h₁₂ : ∀ x, α₂ (f₁ x) = g₁ (α₁ x)) (h₂₃ : ∀ x, α₃ (f₂ x) = g₂ (α₂ x))
    (h₃₄ : ∀ x, α₄ (f₃ x) = g₃ (α₃ x))
    (hf₂₁ : ∀ x, f₂ (f₁ x) = 0) (hf₃ : ∀ x, f₃ x = 0 → ∃ y, f₂ y = x)
    (hg₂ : ∀ x, g₂ x = 0 → ∃ y, g₁ y = x)
    (hα₁ : Function.Surjective α₁) (hα₂ : Function.Injective α₂)
    (hα₄ : Function.Injective α₄) : Function.Injective α₃ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hf₃ x (hα₄ (by rw [h₃₄, hx, map_zero, map_zero]))
  obtain ⟨z, hz⟩ := hg₂ (α₂ y) (by rw [← h₂₃, hx])
  obtain ⟨w, rfl⟩ := hα₁ z
  have hw : f₁ w = y := hα₂ (by rw [h₁₂, hz])
  subst hw
  exact hf₂₁ w

/-- **Four lemma, surjectivity half.** Take a commutative ladder
`A₂ → A₃ → A₄ → A₅` over `B₂ → B₃ → B₄ → B₅`. Assume the top row is exact at `A₄`, and the
bottom row is exact at `B₃` and a complex at `B₄`. If `α₂`, `α₄` are surjective and `α₅` is
injective, then `α₃` is surjective. -/
theorem surjective_of_four_lemma
    (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄) (f₄ : A₄ →+ A₅)
    (g₂ : B₂ →+ B₃) (g₃ : B₃ →+ B₄) (g₄ : B₄ →+ B₅)
    (α₂ : A₂ →+ B₂) (α₃ : A₃ →+ B₃) (α₄ : A₄ →+ B₄) (α₅ : A₅ →+ B₅)
    (h₂₃ : ∀ x, α₃ (f₂ x) = g₂ (α₂ x)) (h₃₄ : ∀ x, α₄ (f₃ x) = g₃ (α₃ x))
    (h₄₅ : ∀ x, α₅ (f₄ x) = g₄ (α₄ x))
    (hf₄ : ∀ x, f₄ x = 0 → ∃ y, f₃ y = x)
    (hg₃ : ∀ x, g₃ x = 0 → ∃ y, g₂ y = x) (hg₄₃ : ∀ x, g₄ (g₃ x) = 0)
    (hα₂ : Function.Surjective α₂) (hα₄ : Function.Surjective α₄)
    (hα₅ : Function.Injective α₅) : Function.Surjective α₃ := by
  intro b
  obtain ⟨a, ha⟩ := hα₄ (g₃ b)
  obtain ⟨a', rfl⟩ := hf₄ a (hα₅ (by rw [h₄₅, ha, hg₄₃, map_zero]))
  obtain ⟨c, hc⟩ := hg₃ (b - α₃ a') (by rw [map_sub, ← h₃₄, ha, sub_self])
  obtain ⟨c', rfl⟩ := hα₂ c
  refine ⟨a' + f₂ c', ?_⟩
  rw [map_add, h₂₃, hc]
  abel

/-- **Five lemma for abelian groups.** Take a commutative ladder `A₁ → ⋯ → A₅` over
`B₁ → ⋯ → B₅`. Assume the top row is a complex at `A₂` and exact at `A₃`, `A₄`, and the bottom
row is exact at `B₂`, `B₃` and a complex at `B₄`. If `α₁` is surjective, `α₂`, `α₄` are
bijective and `α₅` is injective, then `α₃` is bijective. -/
theorem bijective_of_five_lemma
    (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄) (f₄ : A₄ →+ A₅)
    (g₁ : B₁ →+ B₂) (g₂ : B₂ →+ B₃) (g₃ : B₃ →+ B₄) (g₄ : B₄ →+ B₅)
    (α₁ : A₁ →+ B₁) (α₂ : A₂ →+ B₂) (α₃ : A₃ →+ B₃) (α₄ : A₄ →+ B₄) (α₅ : A₅ →+ B₅)
    (h₁₂ : ∀ x, α₂ (f₁ x) = g₁ (α₁ x)) (h₂₃ : ∀ x, α₃ (f₂ x) = g₂ (α₂ x))
    (h₃₄ : ∀ x, α₄ (f₃ x) = g₃ (α₃ x)) (h₄₅ : ∀ x, α₅ (f₄ x) = g₄ (α₄ x))
    (hf₂₁ : ∀ x, f₂ (f₁ x) = 0) (hf₃ : ∀ x, f₃ x = 0 → ∃ y, f₂ y = x)
    (hf₄ : ∀ x, f₄ x = 0 → ∃ y, f₃ y = x)
    (hg₂ : ∀ x, g₂ x = 0 → ∃ y, g₁ y = x) (hg₃ : ∀ x, g₃ x = 0 → ∃ y, g₂ y = x)
    (hg₄₃ : ∀ x, g₄ (g₃ x) = 0)
    (hα₁ : Function.Surjective α₁) (hα₂ : Function.Bijective α₂)
    (hα₄ : Function.Bijective α₄) (hα₅ : Function.Injective α₅) :
    Function.Bijective α₃ :=
  ⟨injective_of_four_lemma f₁ f₂ f₃ g₁ g₂ g₃ α₁ α₂ α₃ α₄ h₁₂ h₂₃ h₃₄ hf₂₁ hf₃ hg₂ hα₁
      hα₂.1 hα₄.1,
    surjective_of_four_lemma f₂ f₃ f₄ g₂ g₃ g₄ α₂ α₃ α₄ α₅ h₂₃ h₃₄ h₄₅ hf₄ hg₃ hg₄₃ hα₂.2
      hα₄.2 hα₅⟩

end FourFive

/-! ## The UCT chase -/

/-- **A vanishing `Ext` term makes the UCT comparison injective.** If `E → K → H` is exact at
`K` and `E = 0`, then `K → H` is injective. For the Rosenberg--Schochet sequence,
`E = Ext¹_ℤ(K_*(S), K_{*+1}(J))`, `K = KK¹(S, J)` and `H = Hom(K_*(S), K_*(J))`. -/
theorem injective_of_exact_of_subsingleton {E : Type u₁} {K : Type u₂} {H : Type u₃}
    [AddCommGroup E] [AddCommGroup K] [AddCommGroup H] [Subsingleton E]
    (i : E →+ K) (γ : K →+ H) (hexact : ∀ x : K, γ x = 0 → ∃ e : E, i e = x) :
    Function.Injective γ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨e, rfl⟩ := hexact x hx
  rw [Subsingleton.elim e 0, map_zero]

/-- **A class with vanishing invariants is zero.** In an exact sequence `E → K → H` with
`E = 0`, an element of `K` that maps to zero in `H` is zero. For the extension class of
Schafhauser's pulled-back extension, the image in `Hom(K_*(S), K_*(J))` is the pair of
boundary maps. -/
theorem eq_zero_of_exact_of_subsingleton {E : Type u₁} {K : Type u₂} {H : Type u₃}
    [AddCommGroup E] [AddCommGroup K] [AddCommGroup H] [Subsingleton E]
    (i : E →+ K) (γ : K →+ H) (hexact : ∀ x : K, γ x = 0 → ∃ e : E, i e = x)
    (x : K) (hx : γ x = 0) : x = 0 :=
  (injective_iff_map_eq_zero γ).mp (injective_of_exact_of_subsingleton i γ hexact) x hx

end

end GroupApproximation.Full.TWWSchafhauser
