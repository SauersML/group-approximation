import GroupApproximation.Algebra.WreathSplitQuotient
import GroupApproximation.Algebra.PermutationalWreathRadicalTame
import GroupApproximation.Algebra.PermutationalWreathLinear
import GroupApproximation.Algebra.MalcevLinear
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Section 54.2: approximation properties are not closed under split extensions

Section 49 puts operator-MF on the positive side of a permanence question: the
property survives passage to and from a subgroup of finite index.  Section 54.2
is the opposite pole.  For a finite lamp group `K` and a group `G` acting on a
site set `X`, the permutational wreath product `K^{(X)} ⋊ G` sits in a *split*
extension whose kernel is the lamp group `K^{(X)}` and whose quotient is `G`,
and neither end constrains the middle at all.

Everything about the two ends is unconditional here.  The kernel is identified
with the lamp group outright, and over a finite lamp it is locally finite,
amenable, residually finite, operator-MF once the site set is countable, and —
for the mod-two lamp — linear over a field.  The quotient is a copy of the
acting group, so it carries residual finiteness, operator-MF and linearity
whenever the acting group does.

The failure at the middle is not proved here.  The repository contains no
non-MF or non-residually-finite witness in wreath form; the witness is the
concrete compression group of the dossier's Sections 39--47, supplied
elsewhere.  What these theorems contribute is the precise sense in which that
witness refutes permanence: `mf_not_closed_under_split_extension` and
`residuallyFinite_not_closed_under_split_extension` take the failure at the
middle as a hypothesis and return it *together with* the two positive
statements about the ends, which is exactly the shape a counterexample to a
closure property has to have.

The linearity clause carries no separate hypothesis.  Mal'cev's theorem, in the
form `MalcevLinear.not_injective_of_not_residuallyFinite`, converts a failure of
residual finiteness in a finitely generated group into the failure of linearity
over every field at once, so `linearity_not_closed_under_split_extension` runs
on the same hypothesis as the residual-finiteness statement.
-/

namespace GroupApproximation

namespace SplitExtensionFailure

open SemidirectProduct

universe u v w t

variable {K : Type u} [Group K] {G : Type w} [Group G] {X : Type v} [MulAction G X]

/-! ## The split extension -/

/-- **The split extension (54.9).**  The wreath projection onto the acting
group is surjective, is split by the canonical inclusion of the acting group,
and has kernel exactly the lamp subgroup.  The three clauses are the definition
of a split extension with the lamp group as kernel. -/
theorem wreath_split_extension :
    Function.Surjective ⇑(rightHom : Wreath K G X →* G) ∧
      (rightHom : Wreath K G X →* G).comp (inr : G →* Wreath K G X)
          = MonoidHom.id G ∧
      (rightHom : Wreath K G X →* G).ker
          = (inl : Lamp K X →* Wreath K G X).range :=
  ⟨SemidirectProduct.rightHom_surjective, SemidirectProduct.rightHom_comp_inr,
    ker_rightHom_eq_lampRange⟩

/-! ## The kernel is the lamp group -/

/-- The lamp coordinate of an element of the kernel of the wreath projection.
On the kernel the acting coordinate is trivial, so the twisting in the
semidirect product law disappears and the lamp coordinate is multiplicative. -/
def kerToLamp : ((rightHom : Wreath K G X →* G).ker) →* Lamp K X where
  toFun w := (w : Wreath K G X).left
  map_one' := rfl
  map_mul' a b := by
    have ha : (a : Wreath K G X).right = 1 := MonoidHom.mem_ker.mp a.2
    show ((a : Wreath K G X) * (b : Wreath K G X)).left
        = (a : Wreath K G X).left * (b : Wreath K G X).left
    rw [SemidirectProduct.mul_left, ha, map_one]
    rfl

/-- Two elements of the kernel with the same lamp coordinate agree, since their
acting coordinates are both trivial. -/
theorem kerToLamp_injective :
    Function.Injective
      (kerToLamp : ((rightHom : Wreath K G X →* G).ker) →* Lamp K X) := by
  intro a b hab
  have hleft : (a : Wreath K G X).left = (b : Wreath K G X).left := hab
  have ha : (a : Wreath K G X).right = 1 := MonoidHom.mem_ker.mp a.2
  have hb : (b : Wreath K G X).right = 1 := MonoidHom.mem_ker.mp b.2
  exact Subtype.ext (SemidirectProduct.ext hleft (by rw [ha, hb]))

/-- Every lamp configuration is the lamp coordinate of a kernel element, namely
of its own image under the canonical inclusion. -/
theorem kerToLamp_surjective :
    Function.Surjective
      (kerToLamp : ((rightHom : Wreath K G X →* G).ker) →* Lamp K X) := by
  intro f
  exact ⟨⟨inl f, MonoidHom.mem_ker.mpr (SemidirectProduct.rightHom_inl f)⟩, rfl⟩

/-- **The kernel of the wreath projection is the lamp group**, packaged as an
isomorphism.  This is the identification that makes every tameness statement
about the lamp group a statement about the kernel of the split extension. -/
noncomputable def kerRightHomEquiv :
    ((rightHom : Wreath K G X →* G).ker) ≃* Lamp K X :=
  MulEquiv.ofBijective kerToLamp ⟨kerToLamp_injective, kerToLamp_surjective⟩

/-! ## The kernel package, unconditionally -/

/-- **Clause 1 of Theorem 54.2, local finiteness.**  Over a finite lamp group
the kernel of the split extension is locally finite: a finite set of kernel
elements is supported on finitely many sites. -/
theorem ker_isLocallyFiniteGroup [Finite K] :
    IsLocallyFiniteGroup ((rightHom : Wreath K G X →* G).ker) :=
  lamp_isLocallyFiniteGroup.comap kerToLamp kerToLamp_injective

/-- **Clause 1 of Theorem 54.2, amenability.**  A locally finite group is
amenable, so the kernel of the split extension is amenable. -/
theorem ker_isAmenable [Finite K] :
    Amenability.IsAmenable ((rightHom : Wreath K G X →* G).ker) :=
  isAmenable_of_isLocallyFiniteGroup ker_isLocallyFiniteGroup

/-- The repository's finite-residual formulation of residual finiteness implies
Mathlib's class, since the two unfold to the same separation statement. -/
theorem residuallyFinite_of_isResiduallyFinite {H : Type*} [Group H]
    (h : IsResiduallyFinite H) : Group.ResiduallyFinite H :=
  Group.residuallyFinite_iff_exists_finiteIndex.mpr (isResiduallyFinite_iff.mp h)

/-- Over a finite lamp group the lamp group is residually finite in Mathlib's
sense: evaluation at a lit site separates a nontrivial configuration. -/
theorem lamp_residuallyFinite [Finite K] : Group.ResiduallyFinite (Lamp K X) :=
  residuallyFinite_of_isResiduallyFinite lamp_isResiduallyFinite

/-- **Clause 1 of Theorem 54.2, residual finiteness.**  The kernel of the split
extension is residually finite. -/
theorem ker_residuallyFinite [Finite K] :
    Group.ResiduallyFinite ((rightHom : Wreath K G X →* G).ker) := by
  haveI := lamp_residuallyFinite (K := K) (X := X)
  exact residuallyFinite_of_injective kerToLamp kerToLamp_injective

/-- Over a finite lamp group and a countable site set the lamp group is
countable: it is the union, over the countably many finite sets of sites, of
the finite groups of configurations supported there. -/
theorem countable_lamp [Finite K] [Countable X] : Countable (Lamp K X) := by
  classical
  haveI : ∀ S : Finset X, Finite ↥(suppIn (K := K) S) := fun S => suppIn_finite S
  have hsurj : Function.Surjective
      (fun p : (S : Finset X) × ↥(suppIn (K := K) S) => (p.2 : Lamp K X)) := by
    intro f
    refine ⟨⟨f.2.toFinset, ⟨f, ?_⟩⟩, rfl⟩
    rw [mem_suppIn]
    intro x hx
    by_contra hcon
    exact hx ((Set.Finite.mem_toFinset _).mpr hcon)
  exact hsurj.countable

/-- The lamp group of a finite lamp over a countable site set is operator-MF,
through residual finiteness. -/
theorem lamp_isOperatorMF [Finite K] [Countable X] : IsOperatorMF (Lamp K X) := by
  haveI := countable_lamp (K := K) (X := X)
  haveI := lamp_residuallyFinite (K := K) (X := X)
  exact isOperatorMF_of_residuallyFinite

/-- **Clause 1 of Theorem 54.2, MF.**  The kernel of the split extension is
operator-MF: it is a copy of the lamp group, which residual finiteness already
makes MF. -/
theorem ker_isOperatorMF [Finite K] [Countable X] :
    IsOperatorMF ((rightHom : Wreath K G X →* G).ker) :=
  lamp_isOperatorMF.comap kerToLamp kerToLamp_injective

/-- **Clause 1 of Theorem 54.2, linearity.**  For the mod-two lamp the kernel
of the split extension embeds in two-by-two matrices over a field, by the
unitriangular representation of Section 54.2. -/
theorem ker_exists_faithful_linear_representation :
    ∃ (F : Type v) (_ : Field F)
      (σ : ((rightHom : Wreath (Multiplicative (ZMod 2)) G X →* G).ker) →*
          Matrix (Fin 2) (Fin 2) F), Function.Injective σ := by
  obtain ⟨F, hF, ρ, hρ⟩ :=
    LampLinear.exists_faithful_linear_representation (S := X)
  letI : Field F := hF
  exact ⟨F, hF, ρ.comp kerToLamp, hρ.comp kerToLamp_injective⟩

/-! ## The quotient package -/

/-- The quotient of the wreath product by the kernel of its projection is a
copy of the acting group, so it is residually finite whenever the acting group
is. -/
theorem quotient_residuallyFinite (hG : Group.ResiduallyFinite G) :
    Group.ResiduallyFinite
      (Wreath K G X ⧸ (rightHom : Wreath K G X →* G).ker) := by
  haveI := hG
  exact residuallyFinite_of_injective
    (QuotientGroup.kerLift (rightHom : Wreath K G X →* G))
    (QuotientGroup.kerLift_injective _)

/-- **Clause 2 of Theorem 54.2.**  A countable residually finite acting group
makes the quotient of the split extension operator-MF. -/
theorem quotient_isOperatorMF [Countable G] (hG : Group.ResiduallyFinite G) :
    IsOperatorMF (Wreath K G X ⧸ (rightHom : Wreath K G X →* G).ker) := by
  haveI := hG
  exact (isOperatorMF_of_residuallyFinite : IsOperatorMF G).comap
    (QuotientGroup.kerLift (rightHom : Wreath K G X →* G))
    (QuotientGroup.kerLift_injective _)

/-! ## The permanence failures -/

/-- **Theorem 54.2 for MF.**  Given a countable residually finite acting group,
a finite lamp group, a countable site set, and a wreath product that is not
operator-MF, both ends of the split extension are operator-MF while the middle
is not.  Hence operator-MF is not closed under split extensions, even when the
kernel is locally finite, amenable and residually finite and the quotient is
residually finite.

The failure at the middle is the hypothesis `hW`; no witness for it lives in
this file. -/
theorem mf_not_closed_under_split_extension [Finite K] [Countable X] [Countable G]
    (hG : Group.ResiduallyFinite G) (hW : ¬ IsOperatorMF (Wreath K G X)) :
    IsOperatorMF ((rightHom : Wreath K G X →* G).ker) ∧
      IsOperatorMF (Wreath K G X ⧸ (rightHom : Wreath K G X →* G).ker) ∧
      ¬ IsOperatorMF (Wreath K G X) :=
  ⟨ker_isOperatorMF, quotient_isOperatorMF hG, hW⟩

/-- **Theorem 54.2 for residual finiteness.**  With a finite lamp group and a
residually finite acting group, both ends of the split extension are residually
finite; a wreath product that is not residually finite therefore shows that
residual finiteness is not closed under split extensions.  Countability is not
needed here.

The failure at the middle is the hypothesis `hW`. -/
theorem residuallyFinite_not_closed_under_split_extension [Finite K]
    (hG : Group.ResiduallyFinite G)
    (hW : ¬ Group.ResiduallyFinite (Wreath K G X)) :
    Group.ResiduallyFinite ((rightHom : Wreath K G X →* G).ker) ∧
      Group.ResiduallyFinite
        (Wreath K G X ⧸ (rightHom : Wreath K G X →* G).ker) ∧
      ¬ Group.ResiduallyFinite (Wreath K G X) :=
  ⟨ker_residuallyFinite, quotient_residuallyFinite hG, hW⟩

/-- A finitely generated wreath product that is not residually finite has no
faithful finite-dimensional representation over any field.  This is Mal'cev's
theorem in the contrapositive form of Section 46.4, applied to the middle group
of the split extension. -/
theorem wreath_not_linear [Group.FG (Wreath K G X)] {F : Type t} [Field F] {d : ℕ}
    (hW : ¬ Group.ResiduallyFinite (Wreath K G X))
    (ρ : Wreath K G X →* Matrix.GeneralLinearGroup (Fin d) F) :
    ¬ Function.Injective ρ :=
  MalcevLinear.not_injective_of_not_residuallyFinite hW ρ

/-- **Theorem 54.2 for linearity.**  Take the mod-two lamp, a faithful linear
representation `ρ₀` of the acting group, and a finitely generated wreath
product that is not residually finite.  Then the kernel of the split extension
is linear over a field, the quotient is linear over the very field the acting
group uses, and the middle group has no faithful representation over any field
at all.  The two ends may need different fields, which is exactly why the
property "linear over some field" is the one that fails.

The failure at the middle is the hypothesis `hW`, the same one the
residual-finiteness statement carries. -/
theorem linearity_not_closed_under_split_extension {F₀ : Type t} [Field F₀] {d₀ : ℕ}
    [Group.FG (Wreath (Multiplicative (ZMod 2)) G X)]
    (ρ₀ : G →* Matrix.GeneralLinearGroup (Fin d₀) F₀)
    (hρ₀ : Function.Injective ρ₀)
    (hW : ¬ Group.ResiduallyFinite (Wreath (Multiplicative (ZMod 2)) G X)) :
    (∃ (F : Type v) (_ : Field F)
        (σ : ((rightHom : Wreath (Multiplicative (ZMod 2)) G X →* G).ker) →*
            Matrix (Fin 2) (Fin 2) F), Function.Injective σ) ∧
      (∃ τ : (Wreath (Multiplicative (ZMod 2)) G X ⧸
            (rightHom : Wreath (Multiplicative (ZMod 2)) G X →* G).ker) →*
          Matrix.GeneralLinearGroup (Fin d₀) F₀, Function.Injective τ) ∧
      ∀ (F : Type t) [Field F] (d : ℕ)
        (ρ : Wreath (Multiplicative (ZMod 2)) G X →*
            Matrix.GeneralLinearGroup (Fin d) F),
        ¬ Function.Injective ρ := by
  refine ⟨ker_exists_faithful_linear_representation,
    ⟨ρ₀.comp (QuotientGroup.kerLift _),
      hρ₀.comp (QuotientGroup.kerLift_injective _)⟩, ?_⟩
  intro F _ d ρ
  exact MalcevLinear.not_injective_of_not_residuallyFinite hW ρ

end SplitExtensionFailure

end GroupApproximation
