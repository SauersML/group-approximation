import GroupApproximation.Algebra.CornerRing
import Mathlib.Data.Matrix.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The Peirce identification `R ≅ M_m(T)`

`non_mf_groups_exist.tex`, inside the proof of `thm:mf-quotient-units`, item (a):

> There are orthogonal idempotents `e_1, …, e_m` with sum `1`, `m ≥ 4`, such
> that `e_1, …, e_{m-1}` are pairwise equivalent and `e_m` is equivalent to an
> idempotent `f ≤ e_1`.  **Then `R` is the ring of `m × m` matrices over
> `T = e_1Re_1`** …

This module proves the emphasised clause, in the generality in which it is
true and in which the printed proof uses it: a unital ring carrying orthogonal
pairwise equivalent idempotents summing to `1` *is* the matrix ring over the
corner at any one of them.  Nothing about pure infiniteness is involved; the
statement is pure idempotent algebra, so it is stated for an arbitrary ring and
an arbitrary finite index type.

## The route

Everything runs through a **complete system of matrix units**
(`MatrixUnitSystem`): elements `u i j` with

    `u i j * u k l = if j = k then u i l else 0`,      `∑ i, u i i = 1`.

* From such a system, the map `r ↦ (u i₀ p * r * u q i₀)` is a ring
  isomorphism `R ≃+* M_ι(T)`, `T = u i₀ i₀ · R · u i₀ i₀`
  (`peirceCoordEquiv`).  Multiplicativity is a *single* sum collapse,
  `∑ k, u k i₀ * u i₀ k = ∑ k, u k k = 1`; there is no quadruple sum anywhere.
  Injectivity is `∑ i, ∑ j, u i i₀ * (u i₀ i * r * u j i₀) * u i₀ j = r`,
  the same collapse read twice; surjectivity is the two delta collapses
  `u i₀ p * u i i₀ = δ_{pi} u i₀ i₀` and `u i₀ j * u q i₀ = δ_{jq} u i₀ i₀`.
* A system of matrix units is built from the printed data — orthogonal
  idempotents `e i` summing to `1`, each equivalent to `e i₀` — by normalising
  each equivalence (`exists_normalized_equivalence`) to a pair
  `x i * y i = e i`, `y i * x i = e i₀` supported on the right corners, and
  setting `u i j := x i * y j`.

## The normalisation lemma

`Algebra/PurelyInfiniteSandwich.lean` already has `exists_normalized_isometry`,
but only for `f ≤ e` (it needs `e * f = f` and `f * e = f`).  Orthogonal
idempotents are never comparable, so that lemma does not apply here and the
general normalisation is proved below: from `e = ab`, `f = ba` the pair
`(eaf, fbe)` works, because `a * f * b = (ab)(ab) = e` and
`b * e * a = (ba)(ba) = f`.
-/

namespace GroupApproximation
namespace MFQuotientUnits

variable {R : Type*} [Ring R]

/-! ### Normalising an equivalence of idempotents -/

/-- **Normalised equivalence.**  Two equivalent idempotents admit witnesses
`x ∈ eRf` and `y ∈ fRe` with `xy = e` and `yx = f`.

Unlike `exists_normalized_isometry`, no comparability between `e` and `f` is
assumed, so this applies to the orthogonal pieces of a Peirce decomposition. -/
theorem exists_normalized_equivalence {e f : R} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (h : IsEquivalentIdempotent R e f) :
    ∃ x y : R, x * y = e ∧ y * x = f ∧
      e * x = x ∧ x * f = x ∧ f * y = y ∧ y * e = y := by
  obtain ⟨a, b, hea, hfb⟩ := h
  have hafb : a * f * b = e := by
    rw [hfb]
    have h1 : a * (b * a) * b = a * b * (a * b) := by noncomm_ring
    rw [h1, ← hea]
    exact he
  have hbea : b * e * a = f := by
    rw [hea]
    have h1 : b * (a * b) * a = b * a * (b * a) := by noncomm_ring
    rw [h1, ← hfb]
    exact hf
  refine ⟨e * a * f, f * b * e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : e * a * f * (f * b * e) = e * (a * (f * f) * b) * e := by noncomm_ring
    rw [h1, hf, hafb, he]
    exact he
  · have h1 : f * b * e * (e * a * f) = f * (b * (e * e) * a) * f := by noncomm_ring
    rw [h1, he, hbea, hf]
    exact hf
  · have h1 : e * (e * a * f) = e * e * a * f := by noncomm_ring
    rw [h1, he]
  · have h1 : e * a * f * f = e * a * (f * f) := by noncomm_ring
    rw [h1, hf]
  · have h1 : f * (f * b * e) = f * f * b * e := by noncomm_ring
    rw [h1, hf]
  · have h1 : f * b * e * e = f * b * (e * e) := by noncomm_ring
    rw [h1, he]

/-! ### Complete systems of matrix units -/

/-- **A complete system of matrix units** in a unital ring: elements `u i j`
multiplying like the matrix units `E_{ij}`, with the diagonal summing to `1`. -/
structure MatrixUnitSystem (R : Type*) [Ring R] (ι : Type*) [Fintype ι]
    [DecidableEq ι] where
  /-- The matrix unit `u i j`. -/
  unit : ι → ι → R
  /-- `u i j * u k l = δ_{jk} u i l`. -/
  unit_mul_unit : ∀ i j k l : ι, unit i j * unit k l = if j = k then unit i l else 0
  /-- The diagonal is a resolution of the identity. -/
  sum_diag : ∑ i, unit i i = 1

namespace MatrixUnitSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unit_mul_unit_self (U : MatrixUnitSystem R ι) (i j l : ι) :
    U.unit i j * U.unit j l = U.unit i l := by
  rw [U.unit_mul_unit i j j l, if_pos rfl]

theorem unit_mul_unit_of_ne (U : MatrixUnitSystem R ι) {j k : ι} (h : j ≠ k)
    (i l : ι) : U.unit i j * U.unit k l = 0 := by
  rw [U.unit_mul_unit i j k l, if_neg h]

theorem isIdempotentElem_unit_diag (U : MatrixUnitSystem R ι) (i : ι) :
    IsIdempotentElem (U.unit i i) := U.unit_mul_unit_self i i i

/-- The corner `T = u_{i₀i₀} R u_{i₀i₀}` the matrix picture is taken over. -/
abbrev BaseCorner (U : MatrixUnitSystem R ι) (i₀ : ι) : Type _ :=
  Corner R (U.unit i₀ i₀) (U.isIdempotentElem_unit_diag i₀)

theorem mem_baseCorner (U : MatrixUnitSystem R ι) (i₀ : ι) (r : R) (p q : ι) :
    U.unit i₀ p * r * U.unit q i₀ ∈
      cornerNonUnitalSubring (U.unit i₀ i₀) (U.isIdempotentElem_unit_diag i₀) := by
  refine ⟨?_, ?_⟩
  · show U.unit i₀ i₀ * (U.unit i₀ p * r * U.unit q i₀) = U.unit i₀ p * r * U.unit q i₀
    have h1 : U.unit i₀ i₀ * (U.unit i₀ p * r * U.unit q i₀)
        = U.unit i₀ i₀ * U.unit i₀ p * r * U.unit q i₀ := by noncomm_ring
    rw [h1, U.unit_mul_unit_self i₀ i₀ p]
  · show U.unit i₀ p * r * U.unit q i₀ * U.unit i₀ i₀ = U.unit i₀ p * r * U.unit q i₀
    have h1 : U.unit i₀ p * r * U.unit q i₀ * U.unit i₀ i₀
        = U.unit i₀ p * r * (U.unit q i₀ * U.unit i₀ i₀) := by noncomm_ring
    rw [h1, U.unit_mul_unit_self q i₀ i₀]

/-- The `(p,q)` matrix coordinate of `r`, an element of `T`. -/
def peirceCoord (U : MatrixUnitSystem R ι) (i₀ : ι) (r : R) (p q : ι) :
    U.BaseCorner i₀ :=
  ⟨U.unit i₀ p * r * U.unit q i₀, U.mem_baseCorner i₀ r p q⟩

@[simp] theorem coe_peirceCoord (U : MatrixUnitSystem R ι) (i₀ : ι) (r : R)
    (p q : ι) :
    ((U.peirceCoord i₀ r p q : U.BaseCorner i₀) : R)
      = U.unit i₀ p * r * U.unit q i₀ := rfl

/-- Coercion turns a finite sum in the corner into the corresponding sum in
`R`.  Stated once so that no proof below has to fight the corner's `Ring`
instance. -/
theorem coe_corner_sum {e : R} (he : IsIdempotentElem e) {κ : Type*}
    (s : Finset κ) (g : κ → Corner R e he) :
    ((∑ k ∈ s, g k : Corner R e he) : R) = ∑ k ∈ s, ((g k : Corner R e he) : R) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, coe_corner_add, ih]

/-! ### The coordinate map is a ring isomorphism -/

/-- **The Peirce coordinate homomorphism `R →+* M_ι(T)`,**
`r ↦ (u_{i₀p} · r · u_{qi₀})`. -/
def peirceCoordHom (U : MatrixUnitSystem R ι) (i₀ : ι) :
    R →+* Matrix ι ι (U.BaseCorner i₀) where
  toFun r := Matrix.of fun p q => U.peirceCoord i₀ r p q
  map_one' := by
    refine Matrix.ext fun p q => corner_ext ?_
    show U.unit i₀ p * 1 * U.unit q i₀
      = ((1 : Matrix ι ι (U.BaseCorner i₀)) p q : R)
    rw [mul_one, U.unit_mul_unit i₀ p q i₀, Matrix.one_apply]
    by_cases h : p = q
    · rw [if_pos h, if_pos h, coe_cornerOne]
    · rw [if_neg h, if_neg h, coe_corner_zero]
  map_mul' r s := by
    refine Matrix.ext fun p q => corner_ext ?_
    show U.unit i₀ p * (r * s) * U.unit q i₀
      = ((Matrix.of (fun p q => U.peirceCoord i₀ r p q) *
          Matrix.of (fun p q => U.peirceCoord i₀ s p q) : Matrix ι ι (U.BaseCorner i₀))
            p q : R)
    rw [Matrix.mul_apply, coe_corner_sum]
    have hstep : ∀ k : ι,
        ((U.peirceCoord i₀ r p k * U.peirceCoord i₀ s k q : U.BaseCorner i₀) : R)
          = U.unit i₀ p * r * U.unit k k * (s * U.unit q i₀) := by
      intro k
      rw [coe_corner_mul]
      simp only [coe_peirceCoord]
      have h1 : U.unit i₀ p * r * U.unit k i₀ * (U.unit i₀ k * s * U.unit q i₀)
          = U.unit i₀ p * r * (U.unit k i₀ * U.unit i₀ k) * (s * U.unit q i₀) := by
        noncomm_ring
      rw [h1, U.unit_mul_unit_self k i₀ k]
    simp only [Matrix.of_apply]
    rw [Finset.sum_congr rfl fun k _ => hstep k]
    rw [← Finset.sum_mul, ← Finset.mul_sum, U.sum_diag]
    noncomm_ring
  map_zero' := by
    refine Matrix.ext fun p q => corner_ext ?_
    show U.unit i₀ p * 0 * U.unit q i₀
      = ((0 : Matrix ι ι (U.BaseCorner i₀)) p q : R)
    rw [Matrix.zero_apply, coe_corner_zero, mul_zero, zero_mul]
  map_add' r s := by
    refine Matrix.ext fun p q => corner_ext ?_
    show U.unit i₀ p * (r + s) * U.unit q i₀
      = ((Matrix.of (fun p q => U.peirceCoord i₀ r p q) +
          Matrix.of (fun p q => U.peirceCoord i₀ s p q) : Matrix ι ι (U.BaseCorner i₀))
            p q : R)
    rw [Matrix.add_apply, coe_corner_add]
    simp only [Matrix.of_apply, coe_peirceCoord]
    noncomm_ring

@[simp] theorem coe_peirceCoordHom_apply (U : MatrixUnitSystem R ι) (i₀ : ι)
    (r : R) (p q : ι) :
    ((U.peirceCoordHom i₀ r p q : U.BaseCorner i₀) : R)
      = U.unit i₀ p * r * U.unit q i₀ := rfl

/-- **Recomposition.**  The coordinates of `r` rebuild `r`; this is
`∑ i, u i i = 1` used on both sides. -/
theorem sum_recompose (U : MatrixUnitSystem R ι) (i₀ : ι) (r : R) :
    ∑ i, ∑ j, U.unit i i₀ * (U.unit i₀ i * r * U.unit j i₀) * U.unit i₀ j = r := by
  have hterm : ∀ i j : ι,
      U.unit i i₀ * (U.unit i₀ i * r * U.unit j i₀) * U.unit i₀ j
        = U.unit i i * r * U.unit j j := by
    intro i j
    have h1 : U.unit i i₀ * (U.unit i₀ i * r * U.unit j i₀) * U.unit i₀ j
        = (U.unit i i₀ * U.unit i₀ i) * r * (U.unit j i₀ * U.unit i₀ j) := by
      noncomm_ring
    rw [h1, U.unit_mul_unit_self i i₀ i, U.unit_mul_unit_self j i₀ j]
  calc ∑ i, ∑ j, U.unit i i₀ * (U.unit i₀ i * r * U.unit j i₀) * U.unit i₀ j
      = ∑ i, ∑ j, U.unit i i * r * U.unit j j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    _ = (∑ i, U.unit i i) * r * (∑ j, U.unit j j) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = r := by rw [U.sum_diag, one_mul, mul_one]

theorem peirceCoordHom_injective (U : MatrixUnitSystem R ι) (i₀ : ι) :
    Function.Injective (U.peirceCoordHom i₀) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  have hzero : ∀ p q : ι, U.unit i₀ p * r * U.unit q i₀ = 0 := by
    intro p q
    have := congrArg (fun M : Matrix ι ι (U.BaseCorner i₀) => (M p q : R)) hr
    simpa using this
  rw [← U.sum_recompose i₀ r]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [hzero i j, mul_zero, zero_mul]

theorem peirceCoordHom_surjective (U : MatrixUnitSystem R ι) (i₀ : ι) :
    Function.Surjective (U.peirceCoordHom i₀) := by
  intro A
  refine ⟨∑ i, ∑ j, U.unit i i₀ * ((A i j : U.BaseCorner i₀) : R) * U.unit i₀ j, ?_⟩
  refine Matrix.ext fun p q => corner_ext ?_
  rw [coe_peirceCoordHom_apply]
  have hexpand : U.unit i₀ p *
        (∑ i, ∑ j, U.unit i i₀ * ((A i j : U.BaseCorner i₀) : R) * U.unit i₀ j) *
        U.unit q i₀
      = ∑ i, ∑ j, (U.unit i₀ p * U.unit i i₀) * ((A i j : U.BaseCorner i₀) : R) *
          (U.unit i₀ j * U.unit q i₀) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    noncomm_ring
  rw [hexpand]
  have hinner : ∀ i : ι,
      (∑ j, (U.unit i₀ p * U.unit i i₀) * ((A i j : U.BaseCorner i₀) : R) *
          (U.unit i₀ j * U.unit q i₀))
        = (U.unit i₀ p * U.unit i i₀) * ((A i q : U.BaseCorner i₀) : R) *
          U.unit i₀ i₀ := by
    intro i
    rw [Finset.sum_eq_single q]
    · rw [U.unit_mul_unit_self i₀ q i₀]
    · intro j _ hjq
      rw [U.unit_mul_unit_of_ne hjq i₀ i₀, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ q) h
  rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_eq_single p]
  · rw [U.unit_mul_unit_self i₀ p i₀]
    have hmem := (A p q).2
    have h1 : U.unit i₀ i₀ * ((A p q : U.BaseCorner i₀) : R) =
        ((A p q : U.BaseCorner i₀) : R) := hmem.1
    have h2 : ((A p q : U.BaseCorner i₀) : R) * U.unit i₀ i₀ =
        ((A p q : U.BaseCorner i₀) : R) := hmem.2
    rw [h1, h2]
  · intro i _ hip
    rw [U.unit_mul_unit_of_ne (Ne.symm hip) i₀ i₀, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- **The Peirce isomorphism.**  A ring carrying a complete system of matrix
units indexed by `ι` is the ring of `ι × ι` matrices over the corner at any
diagonal unit. -/
noncomputable def peirceCoordEquiv (U : MatrixUnitSystem R ι) (i₀ : ι) :
    R ≃+* Matrix ι ι (U.BaseCorner i₀) :=
  RingEquiv.ofBijective (U.peirceCoordHom i₀)
    ⟨U.peirceCoordHom_injective i₀, U.peirceCoordHom_surjective i₀⟩

end MatrixUnitSystem

/-! ### Matrix units from a Peirce decomposition -/

section OfIdempotents

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **From the printed data to matrix units.**  Orthogonal idempotents summing
to `1`, all equivalent to `e i₀`, give a complete system of matrix units whose
`(i₀, i₀)` entry is `e i₀`. -/
theorem exists_matrixUnitSystem_of_orthogonal_equivalent (e : ι → R)
    (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : ι, i ≠ j → e i * e j = 0)
    (hsum : ∑ i, e i = 1) (i₀ : ι)
    (hequiv : ∀ i, IsEquivalentIdempotent R (e i) (e i₀)) :
    ∃ U : MatrixUnitSystem R ι, U.unit i₀ i₀ = e i₀ := by
  choose x y hxy hyx hex hxe hey hye using fun i =>
    exists_normalized_equivalence (hidem i) (hidem i₀) (hequiv i)
  have hcollapse : ∀ j k : ι, y j * x k = if j = k then e i₀ else 0 := by
    intro j k
    by_cases h : j = k
    · subst h
      rw [if_pos rfl, hyx j]
    · rw [if_neg h]
      calc y j * x k = (y j * e j) * (e k * x k) := by rw [hye j, hex k]
        _ = y j * (e j * e k) * x k := by noncomm_ring
        _ = 0 := by rw [horth j k h, mul_zero, zero_mul]
  refine ⟨⟨fun i j => x i * y j, ?_, ?_⟩, ?_⟩
  · intro i j k l
    have h1 : x i * y j * (x k * y l) = x i * (y j * x k) * y l := by noncomm_ring
    rw [h1, hcollapse j k]
    by_cases h : j = k
    · rw [if_pos h, if_pos h]
      have h2 : x i * e i₀ * y l = x i * y l := by rw [hxe i]
      exact h2
    · rw [if_neg h, if_neg h, mul_zero, zero_mul]
  · calc ∑ i, x i * y i = ∑ i, e i := Finset.sum_congr rfl fun i _ => hxy i
      _ = 1 := hsum
  · exact hxy i₀

/-- Two corners at equal idempotents are the same ring. -/
def cornerCongr {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : a = b) : Corner R a ha ≃+* Corner R b hb := by
  subst h
  exact RingEquiv.refl _

/-- **The printed Peirce identification.**

> Then `R` is the ring of `m × m` matrices over `T = e_1Re_1`.

Stated for an arbitrary finite index type and an arbitrary unital ring: from
orthogonal idempotents summing to `1`, all equivalent to `e i₀`, the ring `R`
is isomorphic to the matrix ring over the corner `e_{i₀} R e_{i₀}`. -/
theorem exists_ringEquiv_matrix_corner_of_orthogonal_equivalent (e : ι → R)
    (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : ∀ i j : ι, i ≠ j → e i * e j = 0)
    (hsum : ∑ i, e i = 1) (i₀ : ι)
    (hequiv : ∀ i, IsEquivalentIdempotent R (e i) (e i₀)) :
    Nonempty (R ≃+* Matrix ι ι (Corner R (e i₀) (hidem i₀))) := by
  obtain ⟨U, hU⟩ :=
    exists_matrixUnitSystem_of_orthogonal_equivalent e hidem horth hsum i₀ hequiv
  exact ⟨(U.peirceCoordEquiv i₀).trans
    (RingEquiv.mapMatrix
      (cornerCongr (U.isIdempotentElem_unit_diag i₀) (hidem i₀) hU))⟩

end OfIdempotents

/-- **The printed Peirce identification, as a closed proposition.**

`non_mf_groups_exist.tex`, proof of `thm:mf-quotient-units`, item (a):

> Then `R` is the ring of `m × m` matrices over `T = e_1Re_1` …

The ring, the index type and the idempotent family are all quantified inside
the proposition, so nothing is supplied as construction data. -/
def PeirceMatrixIdentification : Prop :=
  ∀ (R : Type) [Ring R] (ι : Type) [Fintype ι] [DecidableEq ι] (e : ι → R)
    (hidem : ∀ i, IsIdempotentElem (e i)),
    (∀ i j : ι, i ≠ j → e i * e j = 0) → ∑ i, e i = 1 →
      ∀ i₀ : ι, (∀ i, IsEquivalentIdempotent R (e i) (e i₀)) →
        Nonempty (R ≃+* Matrix ι ι (Corner R (e i₀) (hidem i₀)))

/-- **The printed sentence, proved.** -/
theorem peirceMatrixIdentification : PeirceMatrixIdentification := by
  intro R _ ι _ _ e hidem horth hsum i₀ hequiv
  exact exists_ringEquiv_matrix_corner_of_orthogonal_equivalent e hidem horth
    hsum i₀ hequiv

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_normalized_equivalence
#audit_axioms GroupApproximation.MFQuotientUnits.MatrixUnitSystem.peirceCoordEquiv
#audit_axioms
  GroupApproximation.MFQuotientUnits.exists_matrixUnitSystem_of_orthogonal_equivalent
#audit_axioms
  GroupApproximation.MFQuotientUnits.exists_ringEquiv_matrix_corner_of_orthogonal_equivalent
#audit_closed_axioms GroupApproximation.MFQuotientUnits.peirceMatrixIdentification
