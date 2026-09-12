import GroupApproximation.KOne.FiniteRankDeterminant

/-!
# A regularized determinant for a self-similar splitting

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient`: `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}`.
The injectivity half needs an invariant of `K₁` that separates scalars modulo
`(d-1)`-st powers.  This module is the invariant, stated for an abstract
self-similar vector space; `KOne/ToeplitzWordSpace.lean` supplies the instance.

## The construction

Let `e : V ≃ U × (ι → V)` be a linear isomorphism with `U` finite-dimensional
(for the Toeplitz space of words, `U = k` is the empty word and `ι = Fin d` the
first letter).  For an endomorphism `X` of `V` write

* `piMap ι X` for `X ⊕ ⋯ ⊕ X` on `ι → V`,
* `sep U ι X = 0 × X^{⊕ι}` and `lift1 U ι X = 1 × X^{⊕ι}` on `U × (ι → V)`,
* `defect e X = e X e⁻¹ - sep U ι X`, and `Tame e X` when the defect has finite
  rank.

Tame endomorphisms are closed under sums and products
(`defect_mul`: `defect (XY) = defect X · eYe⁻¹ + sep X · defect Y`).  For a tame
unit `g`, the operator

    `regOp e g = e g e⁻¹ ∘ (1 × (g⁻¹)^{⊕ι})`

differs from the identity by a finite-rank map (`finiteRank_regOp_sub_one`), and
`regDet e g = fdet (regOp e g)`.

## What it computes

* `regDet_mul` --- **a homomorphism** on tame units:
  `regOp (gh) = (A · regOp h · A⁻¹) · regOp g` with `A = e g e⁻¹`, and `fdet` is
  multiplicative and conjugation invariant.
* `regDet_mul_fdet_pow` --- on a finite-rank perturbation `g` of the identity,
  `regDet g · (fdet g)^{|ι|} = fdet g`, i.e. `regDet g = (fdet g)^{1-|ι|}`.
* `regDet_of_conj_eq` --- if `e g e⁻¹ = A × g^{⊕ι}` exactly, then `regDet g = det A`.
* `regDet_eq_one_of_sq_zero` --- a unipotent `1 + Y` whose defect is square-zero
  and kills `sep Y` has `regDet = 1`.

With `|ι| = d` the first and second give the obstruction: a scalar `c` that is
simultaneously `regDet` of a product of elementary lifts (value `1`) and of a
finite-rank perturbation of its own diagonal (value `c · (fdet g')^{1-d}`) is a
`(d-1)`-st power.
-/

namespace GroupApproximation
namespace RegularizedDet

open FiniteRankDet

variable {k : Type*} [Field k]
variable {U : Type*} [AddCommGroup U] [Module k U]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {ι : Type*}

/-! ### Diagonal and block maps -/

section Maps

variable (ι) in
/-- `X ⊕ ⋯ ⊕ X` on `ι → V`. -/
def piMap (X : Module.End k V) : Module.End k (ι → V) :=
  LinearMap.pi fun i : ι => X ∘ₗ LinearMap.proj i

@[simp] theorem piMap_apply (X : Module.End k V) (v : ι → V) (i : ι) :
    piMap ι X v i = X (v i) := rfl

theorem piMap_mul (X Y : Module.End k V) : piMap ι (X * Y) = piMap ι X * piMap ι Y :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem piMap_one : piMap ι (1 : Module.End k V) = 1 :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem piMap_zero : piMap ι (0 : Module.End k V) = 0 :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem piMap_add (X Y : Module.End k V) : piMap ι (X + Y) = piMap ι X + piMap ι Y :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem piMap_sub (X Y : Module.End k V) : piMap ι (X - Y) = piMap ι X - piMap ι Y :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem piMap_neg (X : Module.End k V) : piMap ι (-X) = -piMap ι X :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem piMap_smul (c : k) (X : Module.End k V) : piMap ι (c • X) = c • piMap ι X :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem finiteRank_piMap [Fintype ι] {X : Module.End k V} (hX : FiniteRank X) :
    FiniteRank (piMap ι X) := by
  haveI : FiniteDimensional k (LinearMap.range X) := hX
  refine FiniteRank.of_range_le (S := LinearMap.range
    (LinearMap.pi fun i : ι => (LinearMap.range X).subtype ∘ₗ LinearMap.proj i)) ?_
  rintro _ ⟨v, rfl⟩
  exact ⟨fun i => ⟨X (v i), ⟨v i, rfl⟩⟩, rfl⟩

variable (U ι) in
/-- `0 × X^{⊕ι}` on `U × (ι → V)`. -/
def sep (X : Module.End k V) : Module.End k (U × (ι → V)) :=
  (0 : Module.End k U).prodMap (piMap ι X)

variable (U ι) in
/-- `1 × X^{⊕ι}` on `U × (ι → V)`. -/
def lift1 (X : Module.End k V) : Module.End k (U × (ι → V)) :=
  (1 : Module.End k U).prodMap (piMap ι X)

variable (U ι V) in
/-- `1 × 0`, the projection onto the finite-dimensional part. -/
def projU : Module.End k (U × (ι → V)) :=
  (1 : Module.End k U).prodMap 0

theorem lift1_eq (X : Module.End k V) : lift1 U ι X = sep U ι X + projU U ι V :=
  LinearMap.ext fun p => Prod.ext (by simp [lift1, sep, projU]) (by simp [lift1, sep, projU])

theorem sep_mul (X Y : Module.End k V) : sep U ι (X * Y) = sep U ι X * sep U ι Y :=
  LinearMap.ext fun _ => rfl

theorem lift1_mul (X Y : Module.End k V) : lift1 U ι (X * Y) = lift1 U ι X * lift1 U ι Y :=
  LinearMap.ext fun _ => rfl

theorem sep_zero : sep U ι (0 : Module.End k V) = 0 :=
  LinearMap.ext fun p => Prod.ext (by simp [sep]) (funext fun i => by simp [sep])

theorem sep_add (X Y : Module.End k V) : sep U ι (X + Y) = sep U ι X + sep U ι Y :=
  LinearMap.ext fun p => Prod.ext (by simp [sep]) (funext fun i => by simp [sep])

theorem sep_sub (X Y : Module.End k V) : sep U ι (X - Y) = sep U ι X - sep U ι Y :=
  LinearMap.ext fun p => Prod.ext (by simp [sep]) (funext fun i => by simp [sep])

theorem sep_neg (X : Module.End k V) : sep U ι (-X) = -sep U ι X :=
  LinearMap.ext fun p => Prod.ext (by simp [sep]) (funext fun i => by simp [sep])

theorem sep_smul (c : k) (X : Module.End k V) : sep U ι (c • X) = c • sep U ι X :=
  LinearMap.ext fun p => Prod.ext (by simp [sep]) (funext fun i => by simp [sep])

theorem sep_one : sep U ι (1 : Module.End k V) = 1 - projU U ι V :=
  LinearMap.ext fun p => Prod.ext (by simp [sep, projU]) (funext fun i => by simp [sep, projU])

theorem sep_mul_projU (X : Module.End k V) : sep U ι X * projU U ι V = 0 :=
  LinearMap.ext fun p => Prod.ext (by simp [sep, projU]) (funext fun i => by simp [sep, projU])

theorem lift1_sub_one (X : Module.End k V) : lift1 U ι X - 1 = sep U ι (X - 1) :=
  LinearMap.ext fun p => Prod.ext (by simp [lift1, sep]) (funext fun i => by simp [lift1, sep])

theorem finiteRank_projU [FiniteDimensional k U] : FiniteRank (projU U ι V) := by
  refine FiniteRank.of_range_le (S := LinearMap.range (LinearMap.inl k U (ι → V))) ?_
  rintro _ ⟨p, rfl⟩
  exact ⟨p.1, by simp [projU]⟩

theorem finiteRank_sep [Fintype ι] {X : Module.End k V} (hX : FiniteRank X) :
    FiniteRank (sep U ι X) := by
  haveI : FiniteDimensional k (LinearMap.range (piMap ι X)) := finiteRank_piMap hX
  refine FiniteRank.of_range_le
    (S := (LinearMap.range (piMap ι X)).map (LinearMap.inr k U (ι → V))) ?_
  rintro _ ⟨p, rfl⟩
  exact ⟨piMap ι X p.2, ⟨p.2, rfl⟩, by simp [sep]⟩

end Maps

/-! ### Tame endomorphisms -/

section Tame

variable (e : V ≃ₗ[k] U × (ι → V))

theorem conj_mul (X Y : Module.End k V) : e.conj (X * Y) = e.conj X * e.conj Y :=
  e.conj_comp Y X

theorem conj_one : e.conj (1 : Module.End k V) = 1 :=
  e.conj_id

theorem finiteRank_conj {X : Module.End k V} (hX : FiniteRank X) : FiniteRank (e.conj X) := by
  haveI : FiniteDimensional k (LinearMap.range X) := hX
  refine FiniteRank.of_range_le (S := (LinearMap.range X).map (e : V →ₗ[k] U × (ι → V))) ?_
  rintro _ ⟨p, rfl⟩
  exact ⟨X (e.symm p), ⟨e.symm p, rfl⟩, rfl⟩

/-- **The defect** of `X` against the splitting `e`: `e X e⁻¹ - 0 × X^{⊕ι}`. -/
def defect (X : Module.End k V) : Module.End k (U × (ι → V)) :=
  e.conj X - sep U ι X

/-- `X` is **tame** for `e` when its defect has finite rank. -/
def Tame (X : Module.End k V) : Prop :=
  FiniteRank (defect e X)

theorem defect_mul (X Y : Module.End k V) :
    defect e (X * Y) = defect e X * e.conj Y + sep U ι X * defect e Y := by
  simp only [defect, conj_mul, sep_mul]
  noncomm_ring

theorem defect_add (X Y : Module.End k V) : defect e (X + Y) = defect e X + defect e Y := by
  simp only [defect, map_add, sep_add]
  abel

theorem defect_neg (X : Module.End k V) : defect e (-X) = -defect e X := by
  simp only [defect, map_neg, sep_neg]
  abel

theorem defect_smul (c : k) (X : Module.End k V) : defect e (c • X) = c • defect e X := by
  simp only [defect, map_smul, sep_smul, smul_sub]

theorem tame_one [FiniteDimensional k U] : Tame e (1 : Module.End k V) := by
  have h : defect e (1 : Module.End k V) = projU U ι V := by
    rw [defect, conj_one, sep_one, sub_sub_cancel]
  show FiniteRank (defect e (1 : Module.End k V))
  rw [h]
  exact finiteRank_projU

theorem Tame.add {X Y : Module.End k V} (hX : Tame e X) (hY : Tame e Y) : Tame e (X + Y) := by
  show FiniteRank (defect e (X + Y))
  rw [defect_add]
  exact FiniteRank.add hX hY

theorem Tame.neg {X : Module.End k V} (hX : Tame e X) : Tame e (-X) := by
  show FiniteRank (defect e (-X))
  rw [defect_neg]
  exact FiniteRank.neg hX

theorem Tame.sub {X Y : Module.End k V} (hX : Tame e X) (hY : Tame e Y) : Tame e (X - Y) := by
  rw [sub_eq_add_neg]
  exact hX.add e (hY.neg e)

theorem Tame.smul (c : k) {X : Module.End k V} (hX : Tame e X) : Tame e (c • X) := by
  show FiniteRank (defect e (c • X))
  rw [defect_smul]
  exact FiniteRank.smul c hX

theorem Tame.mul {X Y : Module.End k V} (hX : Tame e X) (hY : Tame e Y) : Tame e (X * Y) := by
  show FiniteRank (defect e (X * Y))
  rw [defect_mul]
  exact FiniteRank.add (FiniteRank.mul_right hX _) (FiniteRank.mul_left _ hY)

theorem tame_of_finiteRank [Fintype ι] {X : Module.End k V} (hX : FiniteRank X) : Tame e X :=
  FiniteRank.sub (finiteRank_conj e hX) (finiteRank_sep hX)

/-! ### The regularized determinant -/

/-- `e g e⁻¹ ∘ (1 × (g⁻¹)^{⊕ι})`. -/
def regOp (g : (Module.End k V)ˣ) : Module.End k (U × (ι → V)) :=
  e.conj (g : Module.End k V) * lift1 U ι ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V)

theorem finiteRank_regOp_sub_one [FiniteDimensional k U] {g : (Module.End k V)ˣ}
    (hg : Tame e (g : Module.End k V)) : FiniteRank (regOp e g - 1) := by
  have h1 : e.conj (g : Module.End k V) = sep U ι (g : Module.End k V) + defect e g := by
    rw [defect]
    abel
  have h2 : sep U ι (g : Module.End k V) *
      lift1 U ι ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V) = 1 - projU U ι V := by
    rw [lift1_eq, mul_add, ← sep_mul, Units.mul_inv, sep_one, sep_mul_projU, add_zero]
  have h : regOp e g - 1 = defect e g * lift1 U ι ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V)
      - projU U ι V := by
    rw [regOp, h1, add_mul, h2]
    abel
  rw [h]
  exact FiniteRank.sub (FiniteRank.mul_right hg _) finiteRank_projU

/-- Conjugation of a unit by the splitting. -/
def conjUnit (g : (Module.End k V)ˣ) : (Module.End k (U × (ι → V)))ˣ where
  val := e.conj (g : Module.End k V)
  inv := e.conj ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V)
  val_inv := by rw [← conj_mul, Units.mul_inv, conj_one]
  inv_val := by rw [← conj_mul, Units.inv_mul, conj_one]

/-- **The regularized determinant** of a unit. -/
noncomputable def regDet (g : (Module.End k V)ˣ) : k :=
  fdet (regOp e g)

theorem regDet_one : regDet e (1 : (Module.End k V)ˣ) = 1 := by
  rw [regDet, regOp, inv_one, Units.val_one, conj_one, lift1, piMap_one, LinearMap.prodMap_one,
    one_mul, fdet_one]

/-- **The regularized determinant is a homomorphism on tame units.** -/
theorem regDet_mul [FiniteDimensional k U] {g h : (Module.End k V)ˣ}
    (hg : Tame e (g : Module.End k V)) (hh : Tame e (h : Module.End k V)) :
    regDet e (g * h) = regDet e g * regDet e h := by
  have hgg : e.conj ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V) *
      e.conj (g : Module.End k V) = 1 := by
    rw [← conj_mul, Units.inv_mul, conj_one]
  have hsplit : regOp e (g * h)
      = ((conjUnit e g : Module.End k (U × (ι → V))) * regOp e h *
        (((conjUnit e g)⁻¹ : (Module.End k (U × (ι → V)))ˣ) : Module.End k (U × (ι → V)))) *
        regOp e g := by
    show e.conj ((g * h : (Module.End k V)ˣ) : Module.End k V) *
        lift1 U ι (((g * h)⁻¹ : (Module.End k V)ˣ) : Module.End k V)
      = (e.conj (g : Module.End k V) * (e.conj (h : Module.End k V) *
          lift1 U ι ((h⁻¹ : (Module.End k V)ˣ) : Module.End k V)) *
        e.conj ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V)) *
        (e.conj (g : Module.End k V) * lift1 U ι ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V))
    rw [mul_inv_rev, Units.val_mul, Units.val_mul, conj_mul, lift1_mul]
    calc e.conj (g : Module.End k V) * e.conj (h : Module.End k V) *
          (lift1 U ι ((h⁻¹ : (Module.End k V)ˣ) : Module.End k V) *
            lift1 U ι ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V))
        = e.conj (g : Module.End k V) * (e.conj (h : Module.End k V) *
            lift1 U ι ((h⁻¹ : (Module.End k V)ˣ) : Module.End k V)) *
          (e.conj ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V) * e.conj (g : Module.End k V)) *
            lift1 U ι ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V) := by
          rw [hgg]
          noncomm_ring
      _ = _ := by noncomm_ring
  have hconjrank : FiniteRank ((conjUnit e g : Module.End k (U × (ι → V))) * regOp e h *
      (((conjUnit e g)⁻¹ : (Module.End k (U × (ι → V)))ˣ) : Module.End k (U × (ι → V))) - 1) := by
    have hrw : (conjUnit e g : Module.End k (U × (ι → V))) * regOp e h *
        (((conjUnit e g)⁻¹ : (Module.End k (U × (ι → V)))ˣ) : Module.End k (U × (ι → V))) - 1
        = (conjUnit e g : Module.End k (U × (ι → V))) * (regOp e h - 1) *
          (((conjUnit e g)⁻¹ : (Module.End k (U × (ι → V)))ˣ) : Module.End k (U × (ι → V))) := by
      rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [hrw]
    exact FiniteRank.mul_right (FiniteRank.mul_left _ (finiteRank_regOp_sub_one e hh)) _
  rw [regDet, hsplit, fdet_mul hconjrank (finiteRank_regOp_sub_one e hg),
    fdet_units_conj _ (finiteRank_regOp_sub_one e hh), regDet, regDet, mul_comm]

/-- **On a finite-rank perturbation of the identity**,
`regDet g · (fdet g)^{|ι|} = fdet g`. -/
theorem regDet_mul_fdet_pow [FiniteDimensional k U] [Fintype ι] {g : (Module.End k V)ˣ}
    (hg : FiniteRank ((g : Module.End k V) - 1)) :
    regDet e g * fdet (g : Module.End k V) ^ Fintype.card ι = fdet (g : Module.End k V) := by
  have hinv := FiniteRank.inv_sub_one g hg
  have h1 : FiniteRank (e.conj (g : Module.End k V) - 1) := by
    rw [← conj_one e, ← map_sub]
    exact finiteRank_conj e hg
  have h2 : FiniteRank (lift1 U ι ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V) - 1) := by
    rw [lift1_sub_one]
    exact finiteRank_sep hinv
  have hpi : FiniteRank (piMap ι ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V) - 1) := by
    rw [← piMap_one, ← piMap_sub]
    exact finiteRank_piMap hinv
  rw [regDet, regOp, fdet_mul h1 h2, fdet_conj e hg, lift1, fdet_prodMap _ hpi, map_one,
    one_mul, piMap, fdet_pi hinv, mul_assoc, ← mul_pow, mul_comm (fdet _) (fdet _),
    fdet_units_mul_inv g hg, one_pow, mul_one]

/-- **Block-diagonal units.**  If `e g e⁻¹ = A × g^{⊕ι}` exactly, `regDet g = det A`. -/
theorem regDet_of_conj_eq [FiniteDimensional k U] {g : (Module.End k V)ˣ} (A : Module.End k U)
    (hA : e.conj (g : Module.End k V) = A.prodMap (piMap ι (g : Module.End k V))) :
    regDet e g = LinearMap.det A := by
  have h : regOp e g = A.prodMap (1 : Module.End k (ι → V)) := by
    rw [regOp, hA, lift1, LinearMap.prodMap_mul, mul_one, ← piMap_mul, Units.mul_inv, piMap_one]
  rw [regDet, h, fdet_prodMap_one]

/-- **Unipotent units with a square-zero defect.**  If `g = 1 + Y`, `g⁻¹ = 1 - Y`,
`Y² = 0`, and the defect `D` of `Y` satisfies `D · sep Y = 0` and `D² = 0`, then
`regOp g = 1 + D` and `regDet g = 1`. -/
theorem regDet_eq_one_of_sq_zero {g : (Module.End k V)ˣ} {Y : Module.End k V}
    (hgY : (g : Module.End k V) = 1 + Y)
    (hginv : ((g⁻¹ : (Module.End k V)ˣ) : Module.End k V) = 1 - Y)
    (hY : Y * Y = 0) (h1 : defect e Y * sep U ι Y = 0) (h2 : defect e Y * defect e Y = 0) :
    regDet e g = 1 := by
  have hconj : e.conj (1 + Y) = 1 + sep U ι Y + defect e Y := by
    rw [map_add, conj_one, defect]
    abel
  have hlift : lift1 U ι (1 - Y) = 1 - sep U ι Y := by
    rw [lift1_eq, sep_sub, sep_one]
    abel
  have hsq : sep U ι Y * sep U ι Y = 0 := by
    rw [← sep_mul, hY, sep_zero]
  have hP : regOp e g - 1 = defect e Y := by
    rw [regOp, hgY, hginv, hconj, hlift]
    have hexp : (1 + sep U ι Y + defect e Y) * (1 - sep U ι Y)
        = 1 + defect e Y - sep U ι Y * sep U ι Y - defect e Y * sep U ι Y := by
      noncomm_ring
    rw [hexp, hsq, h1]
    abel
  rw [regDet]
  apply fdet_eq_one_of_sub_one_mul_self_eq_zero
  rw [hP]
  exact h2

end Tame

end RegularizedDet
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.RegularizedDet.defect_mul
#audit_axioms GroupApproximation.RegularizedDet.Tame.mul
#audit_axioms GroupApproximation.RegularizedDet.tame_of_finiteRank
#audit_axioms GroupApproximation.RegularizedDet.finiteRank_regOp_sub_one
#audit_axioms GroupApproximation.RegularizedDet.regDet_one
#audit_axioms GroupApproximation.RegularizedDet.regDet_mul
#audit_axioms GroupApproximation.RegularizedDet.regDet_mul_fdet_pow
#audit_axioms GroupApproximation.RegularizedDet.regDet_of_conj_eq
#audit_axioms GroupApproximation.RegularizedDet.regDet_eq_one_of_sq_zero
