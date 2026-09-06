import GroupApproximation.CharClass.RelativeExcision

/-!
# The local model: excision to a chart and homeomorphism invariance of pairs

Two thin wrappers around `RelativeExcision.lean`'s `excisionIso` and
`RelativeFunctorial.lean`'s `relPairIso`, published for `cc-thom`'s Euler-local
route (`notes/lix-lane-reports/cc-thom.md` §"From `cc-relative`", items (B3)
and (B4)):

* `excisionIsoPoint` — for `V` open containing a point `z`, restricting a
  relative class of `(X, {z}ᶜ)` to `V` gives an isomorphism onto the relative
  cohomology of `(V, V ∖ {z})`.
* `relCohomologyCongr` — a homeomorphism `e : X ≃ₜ Y` carrying `A` onto `B`
  induces an isomorphism `H^*(X, A) ≅ H^*(Y, B)`.

## Main definitions

* `pointComplementOpen X z : Opens X` — `{z}ᶜ`, given `[T1Space X]`.
* `excisionIsoPoint X z V hV hz n`.
* `relCohomologyCongr e A B hAB n`.
-/

open CategoryTheory Limits AlgebraicTopology TopologicalSpace

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Excision to a chart around a point -/

/-- The complement of a point, as an open set. -/
def pointComplementOpen (X : TopCat.{0}) [T1Space X] (z : X) : Opens X :=
  ⟨{z}ᶜ, isClosed_singleton.isOpen_compl⟩

@[simp] theorem pointComplementOpen_coe (X : TopCat.{0}) [T1Space X] (z : X) :
    (pointComplementOpen X z : Set X) = {z}ᶜ := rfl

theorem pointComplement_sup {X : TopCat.{0}} [T1Space X] (z : X) (V : Opens X)
    (hz : z ∈ V) : pointComplementOpen X z ⊔ V = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_sup, Opens.coe_top, pointComplementOpen_coe]
  ext x
  simp only [Set.mem_univ, iff_true, Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff]
  by_cases hxz : x = z
  · exact Or.inr (hxz ▸ hz)
  · exact Or.inl hxz

/-- **(B3)** Excision to a chart: for `V` open and containing `z`, restriction to
`V` induces an isomorphism `H^n(X, {z}ᶜ) ≅ H^n(V, V ∖ {z})`. -/
def excisionIsoPoint (X : TopCat.{0}) [T1Space X] (z : X) (V : Set X) (hV : IsOpen V)
    (hz : z ∈ V) (n : ℕ) :
    relCohomology (ZMod 2) X ({z}ᶜ) n
      ≅ relCohomology (ZMod 2) (TopCat.of V) ((Subtype.val ⁻¹' ({z}ᶜ)) : Set V) n :=
  excisionIso (pointComplementOpen X z) ⟨V, hV⟩ (pointComplement_sup z ⟨V, hV⟩ hz) n

/-! ## 2. Homeomorphism invariance of pairs -/

/-- **(B4)** A homeomorphism carrying `A` onto `B` induces an isomorphism of the
relative cohomology of the pairs `(X, A)` and `(Y, B)`. -/
def relCohomologyCongr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (hAB : e '' A = B) (n : ℕ) :
    relCohomology (ZMod 2) (TopCat.of X) A n ≅ relCohomology (ZMod 2) (TopCat.of Y) B n :=
  relPairIso (ZMod 2) (TopCat.isoOfHomeo e.symm)
    (fun y hy => by
      show e.symm y ∈ A
      rw [← hAB] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rwa [e.symm_apply_apply])
    (fun x hx => by
      show e x ∈ B
      rw [← hAB]
      exact ⟨x, hx, rfl⟩)
    n

end

end GroupApproximation.CharClass
