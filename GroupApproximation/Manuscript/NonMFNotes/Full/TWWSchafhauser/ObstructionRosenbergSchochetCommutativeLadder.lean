import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionVanishHom

/-!
# Six-term exact sequences, ladders and `Hom(-, D)`

Lane `TWWSch3d3-3C3`, work order `WO-TWWSchafhauser-3d3-3C` (section 3C3). Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, J. reine angew. Math. 759 (2020), §§4--5.

The finite-complex step of Rosenberg–Schochet (Duke Math. J. 55 (1987), Thm. 1.17) compares two
cohomology theories on commutative algebras: `A ↦ Ext(A, J)` and `A ↦ Hom(K₁(A), D)`, `D`
divisible. Each turns an extension `0 → I → A → Q → 0` into a cyclic six-term exact sequence,
and the comparison map gives a ladder between them. The five lemma then propagates bijectivity
from ideal and quotient to the middle term (Mayer–Vietoris induction over cells).

* `SixTermExact`: exactness of a cyclic sequence `X₀ → X₁ → ⋯ → X₅ → X₀`;
* `SixTermExact.rotate`: the rotated sequence is exact;
* `SixTermExact.bijective₀` … `bijective₅`: the five lemma for a ladder of six-term sequences,
  at each position;
* `SixTermExact.bijective_one_four`: bijectivity at positions `0, 2, 3, 5` gives it at `1, 4`;
* `SixTermExact.dual`: for divisible `D`, `Hom(-, D)` sends a six-term exact sequence to a
  six-term exact sequence (`IsDivisibleGroup.exists_descend`).
-/

namespace GroupApproximation.Full.TWWSchafhauser

universe u u₀ u₁ u₂ u₃ u₄ u₅ v₀ v₁ v₂ v₃ v₄ v₅

section SixTerm

variable {X₀ : Type u₀} {X₁ : Type u₁} {X₂ : Type u₂} {X₃ : Type u₃} {X₄ : Type u₄}
  {X₅ : Type u₅} [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
  [AddCommGroup X₄] [AddCommGroup X₅]

/-- **A cyclic six-term exact sequence** `X₀ → X₁ → X₂ → X₃ → X₄ → X₅ → X₀`: consecutive maps
compose to zero, and the kernel of each map is the image of the previous one. -/
structure SixTermExact (d₀ : X₀ →+ X₁) (d₁ : X₁ →+ X₂) (d₂ : X₂ →+ X₃) (d₃ : X₃ →+ X₄)
    (d₄ : X₄ →+ X₅) (d₅ : X₅ →+ X₀) : Prop where
  comp₀ : ∀ x, d₁ (d₀ x) = 0
  comp₁ : ∀ x, d₂ (d₁ x) = 0
  comp₂ : ∀ x, d₃ (d₂ x) = 0
  comp₃ : ∀ x, d₄ (d₃ x) = 0
  comp₄ : ∀ x, d₅ (d₄ x) = 0
  comp₅ : ∀ x, d₀ (d₅ x) = 0
  exact₀ : ∀ x, d₀ x = 0 → ∃ y, d₅ y = x
  exact₁ : ∀ x, d₁ x = 0 → ∃ y, d₀ y = x
  exact₂ : ∀ x, d₂ x = 0 → ∃ y, d₁ y = x
  exact₃ : ∀ x, d₃ x = 0 → ∃ y, d₂ y = x
  exact₄ : ∀ x, d₄ x = 0 → ∃ y, d₃ y = x
  exact₅ : ∀ x, d₅ x = 0 → ∃ y, d₄ y = x

variable {d₀ : X₀ →+ X₁} {d₁ : X₁ →+ X₂} {d₂ : X₂ →+ X₃} {d₃ : X₃ →+ X₄} {d₄ : X₄ →+ X₅}
  {d₅ : X₅ →+ X₀}

/-- **Rotation.** `X₁ → ⋯ → X₅ → X₀ → X₁` is exact when `X₀ → ⋯ → X₅ → X₀` is. -/
theorem SixTermExact.rotate (h : SixTermExact d₀ d₁ d₂ d₃ d₄ d₅) :
    SixTermExact d₁ d₂ d₃ d₄ d₅ d₀ :=
  ⟨h.comp₁, h.comp₂, h.comp₃, h.comp₄, h.comp₅, h.comp₀,
    h.exact₁, h.exact₂, h.exact₃, h.exact₄, h.exact₅, h.exact₀⟩

variable {Y₀ : Type v₀} {Y₁ : Type v₁} {Y₂ : Type v₂} {Y₃ : Type v₃} {Y₄ : Type v₄}
  {Y₅ : Type v₅} [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₂] [AddCommGroup Y₃]
  [AddCommGroup Y₄] [AddCommGroup Y₅]
  {e₀ : Y₀ →+ Y₁} {e₁ : Y₁ →+ Y₂} {e₂ : Y₂ →+ Y₃} {e₃ : Y₃ →+ Y₄} {e₄ : Y₄ →+ Y₅}
  {e₅ : Y₅ →+ Y₀}

/-- **Five lemma for six-term ladders, position 1.** Given a commutative ladder
`αᵢ : Xᵢ → Yᵢ` between six-term exact sequences, with `α₅` surjective, `α₀`, `α₂` bijective
and `α₃` injective, the map `α₁` is bijective. -/
theorem SixTermExact.bijective₁ (hX : SixTermExact d₀ d₁ d₂ d₃ d₄ d₅)
    (hY : SixTermExact e₀ e₁ e₂ e₃ e₄ e₅)
    (α₀ : X₀ →+ Y₀) (α₁ : X₁ →+ Y₁) (α₂ : X₂ →+ Y₂) (α₃ : X₃ →+ Y₃) (α₅ : X₅ →+ Y₅)
    (sq₀ : ∀ x, α₁ (d₀ x) = e₀ (α₀ x)) (sq₁ : ∀ x, α₂ (d₁ x) = e₁ (α₁ x))
    (sq₂ : ∀ x, α₃ (d₂ x) = e₂ (α₂ x)) (sq₅ : ∀ x, α₀ (d₅ x) = e₅ (α₅ x))
    (hα₅ : Function.Surjective α₅) (hα₀ : Function.Bijective α₀)
    (hα₂ : Function.Bijective α₂) (hα₃ : Function.Injective α₃) :
    Function.Bijective α₁ :=
  bijective_of_five_lemma d₅ d₀ d₁ d₂ e₅ e₀ e₁ e₂ α₅ α₀ α₁ α₂ α₃ sq₅ sq₀ sq₁ sq₂
    hX.comp₅ hX.exact₁ hX.exact₂ hY.exact₀ hY.exact₁ hY.comp₁ hα₅ hα₀ hα₂ hα₃

/-- **Five lemma for six-term ladders, position 2.** -/
theorem SixTermExact.bijective₂ (hX : SixTermExact d₀ d₁ d₂ d₃ d₄ d₅)
    (hY : SixTermExact e₀ e₁ e₂ e₃ e₄ e₅)
    (α₀ : X₀ →+ Y₀) (α₁ : X₁ →+ Y₁) (α₂ : X₂ →+ Y₂) (α₃ : X₃ →+ Y₃) (α₄ : X₄ →+ Y₄)
    (sq₀ : ∀ x, α₁ (d₀ x) = e₀ (α₀ x)) (sq₁ : ∀ x, α₂ (d₁ x) = e₁ (α₁ x))
    (sq₂ : ∀ x, α₃ (d₂ x) = e₂ (α₂ x)) (sq₃ : ∀ x, α₄ (d₃ x) = e₃ (α₃ x))
    (hα₀ : Function.Surjective α₀) (hα₁ : Function.Bijective α₁)
    (hα₃ : Function.Bijective α₃) (hα₄ : Function.Injective α₄) :
    Function.Bijective α₂ :=
  SixTermExact.bijective₁ hX.rotate hY.rotate α₁ α₂ α₃ α₄ α₀ sq₁ sq₂ sq₃ sq₀ hα₀ hα₁ hα₃ hα₄

/-- **Five lemma for six-term ladders, position 3.** -/
theorem SixTermExact.bijective₃ (hX : SixTermExact d₀ d₁ d₂ d₃ d₄ d₅)
    (hY : SixTermExact e₀ e₁ e₂ e₃ e₄ e₅)
    (α₁ : X₁ →+ Y₁) (α₂ : X₂ →+ Y₂) (α₃ : X₃ →+ Y₃) (α₄ : X₄ →+ Y₄) (α₅ : X₅ →+ Y₅)
    (sq₁ : ∀ x, α₂ (d₁ x) = e₁ (α₁ x)) (sq₂ : ∀ x, α₃ (d₂ x) = e₂ (α₂ x))
    (sq₃ : ∀ x, α₄ (d₃ x) = e₃ (α₃ x)) (sq₄ : ∀ x, α₅ (d₄ x) = e₄ (α₄ x))
    (hα₁ : Function.Surjective α₁) (hα₂ : Function.Bijective α₂)
    (hα₄ : Function.Bijective α₄) (hα₅ : Function.Injective α₅) :
    Function.Bijective α₃ :=
  SixTermExact.bijective₁ hX.rotate.rotate hY.rotate.rotate α₂ α₃ α₄ α₅ α₁ sq₂ sq₃ sq₄ sq₁
    hα₁ hα₂ hα₄ hα₅

/-- **Five lemma for six-term ladders, position 4.** -/
theorem SixTermExact.bijective₄ (hX : SixTermExact d₀ d₁ d₂ d₃ d₄ d₅)
    (hY : SixTermExact e₀ e₁ e₂ e₃ e₄ e₅)
    (α₀ : X₀ →+ Y₀) (α₂ : X₂ →+ Y₂) (α₃ : X₃ →+ Y₃) (α₄ : X₄ →+ Y₄) (α₅ : X₅ →+ Y₅)
    (sq₂ : ∀ x, α₃ (d₂ x) = e₂ (α₂ x)) (sq₃ : ∀ x, α₄ (d₃ x) = e₃ (α₃ x))
    (sq₄ : ∀ x, α₅ (d₄ x) = e₄ (α₄ x)) (sq₅ : ∀ x, α₀ (d₅ x) = e₅ (α₅ x))
    (hα₂ : Function.Surjective α₂) (hα₃ : Function.Bijective α₃)
    (hα₅ : Function.Bijective α₅) (hα₀ : Function.Injective α₀) :
    Function.Bijective α₄ :=
  SixTermExact.bijective₁ hX.rotate.rotate.rotate hY.rotate.rotate.rotate α₃ α₄ α₅ α₀ α₂
    sq₃ sq₄ sq₅ sq₂ hα₂ hα₃ hα₅ hα₀

/-- **Five lemma for six-term ladders, position 5.** -/
theorem SixTermExact.bijective₅ (hX : SixTermExact d₀ d₁ d₂ d₃ d₄ d₅)
    (hY : SixTermExact e₀ e₁ e₂ e₃ e₄ e₅)
    (α₀ : X₀ →+ Y₀) (α₁ : X₁ →+ Y₁) (α₃ : X₃ →+ Y₃) (α₄ : X₄ →+ Y₄) (α₅ : X₅ →+ Y₅)
    (sq₃ : ∀ x, α₄ (d₃ x) = e₃ (α₃ x)) (sq₄ : ∀ x, α₅ (d₄ x) = e₄ (α₄ x))
    (sq₅ : ∀ x, α₀ (d₅ x) = e₅ (α₅ x)) (sq₀ : ∀ x, α₁ (d₀ x) = e₀ (α₀ x))
    (hα₃ : Function.Surjective α₃) (hα₄ : Function.Bijective α₄)
    (hα₀ : Function.Bijective α₀) (hα₁ : Function.Injective α₁) :
    Function.Bijective α₅ :=
  SixTermExact.bijective₁ hX.rotate.rotate.rotate.rotate hY.rotate.rotate.rotate.rotate
    α₄ α₅ α₀ α₁ α₃ sq₄ sq₅ sq₀ sq₃ hα₃ hα₄ hα₀ hα₁

/-- **Five lemma for six-term ladders, position 0.** -/
theorem SixTermExact.bijective₀ (hX : SixTermExact d₀ d₁ d₂ d₃ d₄ d₅)
    (hY : SixTermExact e₀ e₁ e₂ e₃ e₄ e₅)
    (α₀ : X₀ →+ Y₀) (α₁ : X₁ →+ Y₁) (α₂ : X₂ →+ Y₂) (α₄ : X₄ →+ Y₄) (α₅ : X₅ →+ Y₅)
    (sq₄ : ∀ x, α₅ (d₄ x) = e₄ (α₄ x)) (sq₅ : ∀ x, α₀ (d₅ x) = e₅ (α₅ x))
    (sq₀ : ∀ x, α₁ (d₀ x) = e₀ (α₀ x)) (sq₁ : ∀ x, α₂ (d₁ x) = e₁ (α₁ x))
    (hα₄ : Function.Surjective α₄) (hα₅ : Function.Bijective α₅)
    (hα₁ : Function.Bijective α₁) (hα₂ : Function.Injective α₂) :
    Function.Bijective α₀ :=
  SixTermExact.bijective₁ hX.rotate.rotate.rotate.rotate.rotate
    hY.rotate.rotate.rotate.rotate.rotate α₅ α₀ α₁ α₂ α₄ sq₅ sq₀ sq₁ sq₄ hα₄ hα₅ hα₁ hα₂

/-- **Ideal and quotient determine the middle.** In a commutative ladder of six-term exact
sequences, bijectivity at positions `0, 2, 3, 5` gives bijectivity at positions `1` and `4`.
For the sequences of an extension `0 → I → A → Q → 0` the positions `1, 4` are the two terms
belonging to `A`. -/
theorem SixTermExact.bijective_one_four (hX : SixTermExact d₀ d₁ d₂ d₃ d₄ d₅)
    (hY : SixTermExact e₀ e₁ e₂ e₃ e₄ e₅)
    (α₀ : X₀ →+ Y₀) (α₁ : X₁ →+ Y₁) (α₂ : X₂ →+ Y₂) (α₃ : X₃ →+ Y₃) (α₄ : X₄ →+ Y₄)
    (α₅ : X₅ →+ Y₅)
    (sq₀ : ∀ x, α₁ (d₀ x) = e₀ (α₀ x)) (sq₁ : ∀ x, α₂ (d₁ x) = e₁ (α₁ x))
    (sq₂ : ∀ x, α₃ (d₂ x) = e₂ (α₂ x)) (sq₃ : ∀ x, α₄ (d₃ x) = e₃ (α₃ x))
    (sq₄ : ∀ x, α₅ (d₄ x) = e₄ (α₄ x)) (sq₅ : ∀ x, α₀ (d₅ x) = e₅ (α₅ x))
    (hα₀ : Function.Bijective α₀) (hα₂ : Function.Bijective α₂)
    (hα₃ : Function.Bijective α₃) (hα₅ : Function.Bijective α₅) :
    Function.Bijective α₁ ∧ Function.Bijective α₄ :=
  ⟨SixTermExact.bijective₁ hX hY α₀ α₁ α₂ α₃ α₅ sq₀ sq₁ sq₂ sq₅ hα₅.2 hα₀ hα₂ hα₃.1,
    SixTermExact.bijective₄ hX hY α₀ α₂ α₃ α₄ α₅ sq₂ sq₃ sq₄ sq₅ hα₂.2 hα₃ hα₅ hα₀.1⟩

end SixTerm

/-! ## `Hom(-, D)` of a six-term exact sequence -/

namespace CommutativeLadder

variable {D : Type u} [AddCommGroup D]

/-- **Precomposition** with `f : M → N`, as an additive map `Hom(N, D) → Hom(M, D)`. -/
def precomp {M : Type v₀} {N : Type v₁} [AddCommGroup M] [AddCommGroup N] (f : M →+ N) :
    (N →+ D) →+ (M →+ D) where
  toFun φ := φ.comp f
  map_zero' := AddMonoidHom.ext fun _ => rfl
  map_add' _ _ := AddMonoidHom.ext fun _ => rfl

theorem precomp_apply {M : Type v₀} {N : Type v₁} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) (φ : N →+ D) : precomp f φ = φ.comp f :=
  rfl

/-- `Hom(-, D)` of a complex is a complex. -/
theorem precomp_precomp_eq_zero {M' : Type v₀} {M : Type v₁} {M'' : Type v₂} [AddCommGroup M']
    [AddCommGroup M] [AddCommGroup M''] (f : M' →+ M) (g : M →+ M'')
    (h : ∀ x, g (f x) = 0) (φ : M'' →+ D) : precomp f (precomp g φ) = 0 :=
  AddMonoidHom.ext fun x => by
    show φ (g (f x)) = 0
    rw [h x, map_zero]

/-- `Hom(-, D)` is exact for divisible `D`: if `M' → M → M''` is exact at `M` and `ψ : M → D`
vanishes on the image of `M'`, then `ψ` factors through `M''`. -/
theorem exists_precomp_eq (hD : IsDivisibleGroup D) {M' : Type v₀} {M : Type v₁} {M'' : Type v₂}
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M''] (f : M' →+ M) (g : M →+ M'')
    (hexact : ∀ x, g x = 0 → ∃ y, f y = x) (ψ : M →+ D) (hψ : precomp f ψ = 0) :
    ∃ φ : M'' →+ D, precomp g φ = ψ := by
  obtain ⟨φ, hφ⟩ := hD.exists_descend f g hexact ψ fun y => DFunLike.congr_fun hψ y
  exact ⟨φ, AddMonoidHom.ext hφ⟩

variable {Z₀ : Type u₀} {Z₁ : Type u₁} {Z₂ : Type u₂} {Z₃ : Type u₃} {Z₄ : Type u₄}
  {Z₅ : Type u₅} [AddCommGroup Z₀] [AddCommGroup Z₁] [AddCommGroup Z₂] [AddCommGroup Z₃]
  [AddCommGroup Z₄] [AddCommGroup Z₅]
  {c₀ : Z₀ →+ Z₁} {c₁ : Z₁ →+ Z₂} {c₂ : Z₂ →+ Z₃} {c₃ : Z₃ →+ Z₄} {c₄ : Z₄ →+ Z₅}
  {c₅ : Z₅ →+ Z₀}

/-- **`Hom(-, D)` of a six-term exact sequence is six-term exact**, `D` divisible. The dual of
`Z₀ → Z₁ → ⋯ → Z₅ → Z₀` is `Hom(Z₅, D) → Hom(Z₄, D) → ⋯ → Hom(Z₀, D) → Hom(Z₅, D)`. -/
theorem dual (hD : IsDivisibleGroup D) (hZ : SixTermExact c₀ c₁ c₂ c₃ c₄ c₅) :
    SixTermExact (precomp (D := D) c₄) (precomp (D := D) c₃) (precomp (D := D) c₂)
      (precomp (D := D) c₁) (precomp (D := D) c₀) (precomp (D := D) c₅) :=
  ⟨precomp_precomp_eq_zero c₃ c₄ hZ.comp₃, precomp_precomp_eq_zero c₂ c₃ hZ.comp₂,
    precomp_precomp_eq_zero c₁ c₂ hZ.comp₁, precomp_precomp_eq_zero c₀ c₁ hZ.comp₀,
    precomp_precomp_eq_zero c₅ c₀ hZ.comp₅, precomp_precomp_eq_zero c₄ c₅ hZ.comp₄,
    exists_precomp_eq hD c₄ c₅ hZ.exact₅, exists_precomp_eq hD c₃ c₄ hZ.exact₄,
    exists_precomp_eq hD c₂ c₃ hZ.exact₃, exists_precomp_eq hD c₁ c₂ hZ.exact₂,
    exists_precomp_eq hD c₀ c₁ hZ.exact₁, exists_precomp_eq hD c₅ c₀ hZ.exact₀⟩

end CommutativeLadder

end GroupApproximation.Full.TWWSchafhauser
