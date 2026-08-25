import GroupApproximation.Leavitt.ElementaryRoots
import Mathlib.Data.Matrix.Block

/-!
# Identity padding along an index embedding

`Leavitt/ElementaryGroup.lean` transports elementary groups along ring maps
(`elementaryGroupMap`) and along *equivalences* of index types
(`elementaryReindexEquiv`).  It has nothing for a mere **embedding** of index
types, and an embedding is what the rank-three analytic estimates need in
order to reach rank `n`: every ordered pair `(u, v)` of distinct indices in
`Fin n` together with a third index `w` determines an embedding
`Fin 3 ↪ Fin n`, and restricting a representation of `EL_n(R)` along the
induced homomorphism turns a rank-three estimate into an estimate at
`(u, v)`.

The Steinberg group has a presentation, so `SteinbergGroup.indexMap` is
immediate there.  `EL_ι(R)` has no presentation in the tree, so the map has
to be built on matrices and then shown to preserve the elementary subgroup.
That is what this file does:

* `padHom e : Matrix ι ι R →* Matrix κ κ R` sends `M` to the matrix with `M`
  in the `e`-block and the identity outside it.  It is a *monoid*
  homomorphism, not a ring homomorphism -- it does not preserve `0` -- which
  is exactly the amount of structure `Units.map` needs.
* `elementaryPad e : EL_ι(R) →* EL_κ(R)` is the induced map, and
  `elementaryPad_elementaryRoot` says it sends the root `x_{ij}(a)` to
  `x_{e i, e j}(a)`.

No hypothesis on `R` beyond `Ring R` is used, and none on `e` beyond
injectivity.
-/

namespace GroupApproximation
namespace ElementaryPadding

noncomputable section

open scoped Classical

/-! ### Splitting the target index type -/

section IndexEquiv

variable {ι κ : Type*}

/-- An embedding of index types splits its target into the source and the
complement of the image. -/
def padEquiv (e : ι ↪ κ) : ι ⊕ {a : κ // a ∉ Set.range e} ≃ κ :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl fun a : κ ↦ a ∈ Set.range e)

@[simp] theorem padEquiv_inl (e : ι ↪ κ) (i : ι) :
    padEquiv e (Sum.inl i) = e i := rfl

end IndexEquiv

/-! ### Padding a matrix by the identity -/

section Pad

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Ring R]

/-- The block form of the padded matrix: `M` in the source block, the
identity in the complementary block. -/
def blockPad (e : ι ↪ κ) :
    Matrix ι ι R →*
      Matrix (ι ⊕ {a : κ // a ∉ Set.range e}) (ι ⊕ {a : κ // a ∉ Set.range e}) R where
  toFun M := Matrix.fromBlocks M 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' M N := by
    rw [Matrix.fromBlocks_multiply]
    simp

/-- **Identity padding along an index embedding.**  The `(e i, e j)` entry of
`padHom e M` is `M i j`; outside the image of `e` the matrix is the
identity. -/
def padHom (e : ι ↪ κ) : Matrix ι ι R →* Matrix κ κ R :=
  (Matrix.reindexRingEquiv R (padEquiv e)).toRingHom.toMonoidHom.comp (blockPad e)

theorem padHom_apply (e : ι ↪ κ) (M : Matrix ι ι R) :
    padHom e M =
      Matrix.reindex (padEquiv e) (padEquiv e) (Matrix.fromBlocks M 0 0 1) := rfl

/-- Padding a single-entry perturbation of the identity moves the entry to
the corresponding position of the image. -/
theorem padHom_one_add_single (e : ι ↪ κ) (i j : ι) (a : R) :
    padHom e (1 + Matrix.single i j a) = 1 + Matrix.single (e i) (e j) a := by
  have hblock :
      Matrix.fromBlocks (1 + Matrix.single i j a) 0 0
          (1 : Matrix {a : κ // a ∉ Set.range e} {a : κ // a ∉ Set.range e} R) =
        1 + Matrix.single (Sum.inl i) (Sum.inl j) a := by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply]
  have hsingle :
      Matrix.reindex (padEquiv e) (padEquiv e)
          (Matrix.single (Sum.inl i) (Sum.inl j) a) =
        Matrix.single (e i) (e j) a := by
    simpa only [Matrix.reindex_apply, Equiv.symm_symm, padEquiv_inl] using
      Matrix.submatrix_single_equiv (α := R) (padEquiv e).symm (padEquiv e).symm
        (Sum.inl i) (Sum.inl j) a
  rw [padHom_apply, hblock]
  have hmap :
      (Matrix.reindexRingEquiv R (padEquiv e))
          ((1 : Matrix (ι ⊕ {a : κ // a ∉ Set.range e})
              (ι ⊕ {a : κ // a ∉ Set.range e}) R) +
            Matrix.single (Sum.inl i) (Sum.inl j) a) =
        1 + Matrix.single (e i) (e j) a := by
    rw [map_add, map_one]
    exact congrArg (fun z ↦ (1 : Matrix κ κ R) + z) hsingle
  exact hmap

/-- Padding as a homomorphism of unit groups. -/
def padUnitHom (e : ι ↪ κ) : (Matrix ι ι R)ˣ →* (Matrix κ κ R)ˣ :=
  Units.map (padHom e)

theorem padUnitHom_elementaryUnit (e : ι ↪ κ) (i j : ι) (hij : i ≠ j) (a : R) :
    padUnitHom e (elementaryUnit i j hij a) =
      elementaryUnit (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  change padHom e (1 + Matrix.single i j a) = 1 + Matrix.single (e i) (e j) a
  exact padHom_one_add_single e i j a

theorem elementaryGroup_pad_le (e : ι ↪ κ) :
    (elementaryGroup ι R).map (padUnitHom e) ≤ elementaryGroup κ R := by
  rw [elementaryGroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  change padUnitHom e (elementaryUnit i j hij a) ∈ elementaryGroup κ R
  rw [padUnitHom_elementaryUnit]
  exact elementaryUnit_mem _ _ _ a

/-- **The identity-padding homomorphism of elementary groups.**  This is the
map `EL_ι(R) →* EL_κ(R)` that `elementaryReindexEquiv` cannot supply, because
an embedding is not an equivalence. -/
def elementaryPad (e : ι ↪ κ) : elementaryGroup ι R →* elementaryGroup κ R :=
  ((padUnitHom e).comp (elementaryGroup ι R).subtype).codRestrict
    (elementaryGroup κ R) fun g ↦
      elementaryGroup_pad_le e
        (Subgroup.apply_coe_mem_map (padUnitHom e) (elementaryGroup ι R) g)

@[simp] theorem elementaryPad_elementaryRoot (e : ι ↪ κ) (i j : ι) (hij : i ≠ j)
    (a : R) :
    elementaryPad e (elementaryRoot i j hij a) =
      elementaryRoot (e i) (e j) (e.injective.ne hij) a := by
  apply Subtype.ext
  exact padUnitHom_elementaryUnit e i j hij a

end Pad

end

end ElementaryPadding
end GroupApproximation
