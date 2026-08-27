import GroupApproximation.Analysis.CStarCornerMap
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedComposite

/-!
# Ueda's corner map, built coordinate by coordinate

`UedaCornerMapStatement` asks for an injective unital star-algebra
homomorphism from the universal C-star HNN algebra `U` into the corner `ePe`
of the full amalgam `P`, carrying the base to `cornerBaseMap` and the stable
unitary to `cornerStableUnitary`.  The universal property
`universalCStarHNN_existsUnique_lift` reaches only same-universe codomains and
`ePe` is one universe up, so it cannot be applied to `ePe` itself.  It is
applied here once in each same-universe coordinate of `P` instead.

Both `U` and `P` are closed star subalgebras of bounded products over their
own representation families.  A compatible amalgam coordinate `Q` carries the
image `e_Q` of the projection, and the corner of `Q.carrier` at `e_Q` is a
same-universe covariant representation of the HNN datum: its base map and its
stable unitary are the images of the given pair under corner functoriality, so
its covariance is the image of the given covariance, and it is nontrivial as
soon as `e_Q ≠ 0`.  Evaluating an element of the ambient product of `U` at
that coordinate is contractive, so the family of those values is an element of
the ambient product of `P`.  It lands in `ePe` because the ambient elements
whose value does form a closed star subalgebra containing the two generators.

The construction is carried out at abstract C-star algebras, and only its
instantiation happens at the algebras of a `CoronaConjugator`.  That split is
not a matter of taste: at the concrete algebras every class derived from the
C-star structure of either bounded product is a search over a family indexed
by concrete matrix algebras, and each such search exhausts the typeclass
budget.  The one concrete input is that Ueda's projection survives every
coordinate, which holds because a unital homomorphism out of `M₂(D)` killing
`e₀₀` also kills `e₁₁ = e₁₀e₀₀e₀₁`, and so the unit.

Injectivity is the coordinate argument of the printed proof: composing with
the evaluated corner map at an HNN coordinate `R` produces a lift of the same
covariant pair as `cStarUpperLeftCornerMap` composed with evaluation at `R`,
lifts to a same-universe codomain are unique, `cStarUpperLeftCornerMap` is
injective, and the coordinate evaluations of `U` are jointly faithful.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open scoped CStarAlgebra ENNReal

noncomputable section

/-! ## The construction at abstract C-star algebras -/

section Abstract

universe u v w

/-- A corner at a nonzero projection is nontrivial. -/
theorem cStarCorner_nontrivial {K : Type v} [CStarAlgebra K] {p : K}
    (hp_star : star p = p) (hp_mul : p * p = p) (hp : p ≠ 0) :
    Nontrivial (CStarCorner p hp_star hp_mul) :=
  ⟨1, 0, fun h ↦ hp (congrArg Subtype.val h)⟩

/-- Composition of star-algebra homomorphisms through a single
`[CStarAlgebra _]` binder on each of the three algebras.  Writing `g.comp f`
at a `StarSubalgebra` carrier cannot elaborate: `StarAlgHom.comp` carries
separate `[Semiring]`, `[Algebra ℂ]` and `[Star]` binders, the `Semiring` is
fixed by unification with `f`, and the `Algebra ℂ` search then has to return a
term over exactly that `Semiring`, which it does not. -/
def starAlgComp {D : Type u} {K : Type v} {L : Type w}
    [CStarAlgebra D] [CStarAlgebra K] [CStarAlgebra L]
    (g : K →⋆ₐ[ℂ] L) (f : D →⋆ₐ[ℂ] K) : D →⋆ₐ[ℂ] L :=
  g.comp f

@[simp] theorem starAlgComp_apply {D : Type u} {K : Type v} {L : Type w}
    [CStarAlgebra D] [CStarAlgebra K] [CStarAlgebra L]
    (g : K →⋆ₐ[ℂ] L) (f : D →⋆ₐ[ℂ] K) (d : D) :
    starAlgComp g f d = g (f d) :=
  rfl

/-- The image of a covariant pair under a unital star-algebra homomorphism is
again a covariant pair, and so a covariant representation as soon as its
target is nontrivial.  The target sits one universe below the source here,
which is the point: the source pair lives in the corner of the amalgam. -/
def transportedHNNRepresentation {D : Type u} [CStarAlgebra D]
    {B0 B1 : StarSubalgebra ℂ D} {theta : B0 ≃⋆ₐ[ℂ] B1}
    {K : Type v} {L : Type u} [CStarAlgebra K] [CStarAlgebra L]
    (pi : D →⋆ₐ[ℂ] K) (u : unitary K)
    (hcov : ∀ b : B0,
      (u : K) * pi (b : D) = pi ((theta b : B1) : D) * (u : K))
    (g : K →⋆ₐ[ℂ] L) (hnt : Nontrivial L) :
    CStarHNNRepresentation B0 B1 theta where
  carrier := L
  instCStarAlgebra := inferInstance
  instNontrivial := hnt
  base := starAlgComp g pi
  stable := unitaryMapOfStarAlgHom g u
  covariance := fun b ↦ by
    have h := congrArg g (hcov b)
    rw [map_mul, map_mul] at h
    exact h

variable {D : Type u} [CStarAlgebra D] {B0 B1 : StarSubalgebra ℂ D}
variable {theta : B0 ≃⋆ₐ[ℂ] B1}
variable {C E F : Type u} [CStarAlgebra C] [CStarAlgebra E] [CStarAlgebra F]
variable {iA : C →⋆ₐ[ℂ] E} {iB : C →⋆ₐ[ℂ] F}
variable [Nonempty (CStarAmalgamRepresentation iA iB)]

/-! ### The corner in one compatible coordinate -/

/-- The image of the corner projection in one compatible coordinate. -/
def cornerProjectionAt (e : UniversalCStarAmalgam iA iB)
    (Q : CStarAmalgamRepresentation iA iB) : Q.carrier :=
  universalCStarAmalgamEval iA iB Q e

theorem cornerProjectionAt_star (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) (Q : CStarAmalgamRepresentation iA iB) :
    star (cornerProjectionAt e Q) = cornerProjectionAt e Q :=
  (map_star (universalCStarAmalgamEval iA iB Q) e).symm.trans
    (congrArg (universalCStarAmalgamEval iA iB Q) he_star)

theorem cornerProjectionAt_mul (e : UniversalCStarAmalgam iA iB)
    (he_mul : e * e = e) (Q : CStarAmalgamRepresentation iA iB) :
    cornerProjectionAt e Q * cornerProjectionAt e Q = cornerProjectionAt e Q :=
  (map_mul (universalCStarAmalgamEval iA iB Q) e e).symm.trans
    (congrArg (universalCStarAmalgamEval iA iB Q) he_mul)

/-- Corner functoriality along one coordinate evaluation. -/
def cornerMapAt (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (Q : CStarAmalgamRepresentation iA iB) :
    CStarCorner e he_star he_mul →⋆ₐ[ℂ]
      CStarCorner (cornerProjectionAt e Q)
        (cornerProjectionAt_star e he_star Q)
        (cornerProjectionAt_mul e he_mul Q) :=
  CStarCorner.map (universalCStarAmalgamEval iA iB Q) rfl

/-- The covariant representation of the HNN datum carried by one compatible
amalgam coordinate. -/
def cornerCoordinateHNN (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) (he_mul : e * e = e)
    (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0)
    (Q : CStarAmalgamRepresentation iA iB) :
    CStarHNNRepresentation B0 B1 theta :=
  transportedHNNRepresentation pi u hcov (cornerMapAt e he_star he_mul Q)
    (cStarCorner_nontrivial (cornerProjectionAt_star e he_star Q)
      (cornerProjectionAt_mul e he_mul Q) (hne Q))

/-! ### The lift on the ambient bounded products -/

/-- The coordinate family of the corner lift. -/
def cornerLiftCoord (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0)
    (y : UniversalCStarHNNAmbient B0 B1 theta)
    (Q : CStarAmalgamRepresentation iA iB) : Q.carrier :=
  CStarCorner.inclusion (cornerProjectionAt e Q)
    (cornerProjectionAt_star e he_star Q) (cornerProjectionAt_mul e he_mul Q)
    (y (cornerCoordinateHNN e he_star he_mul pi u hcov hne Q))

theorem cornerLiftCoord_norm_le (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) (he_mul : e * e = e)
    (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0)
    (y : UniversalCStarHNNAmbient B0 B1 theta)
    (Q : CStarAmalgamRepresentation iA iB) :
    ‖cornerLiftCoord e he_star he_mul pi u hcov hne y Q‖ ≤ ‖y‖ :=
  le_trans
    (NonUnitalStarAlgHom.norm_apply_le
      (CStarCorner.inclusion (cornerProjectionAt e Q)
        (cornerProjectionAt_star e he_star Q)
        (cornerProjectionAt_mul e he_mul Q))
      (y (cornerCoordinateHNN e he_star he_mul pi u hcov hne Q)))
    (lp.norm_apply_le_norm ENNReal.top_ne_zero y
      (cornerCoordinateHNN e he_star he_mul pi u hcov hne Q))

/-- The corner lift, as an element of the ambient bounded product of the
amalgam. -/
def cornerLiftAmbient (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0)
    (y : UniversalCStarHNNAmbient B0 B1 theta) :
    UniversalCStarAmalgamAmbient iA iB :=
  ⟨cornerLiftCoord e he_star he_mul pi u hcov hne y, memℓp_infty ⟨‖y‖, by
    rintro _ ⟨Q, rfl⟩
    exact cornerLiftCoord_norm_le e he_star he_mul pi u hcov hne y Q⟩⟩

/-- The corner lift is a nonunital star-algebra homomorphism of the two
ambient bounded products: every operation is coordinatewise on both sides, and
the coordinate corner inclusions preserve all of them. -/
def cornerLiftHom (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0) :
    UniversalCStarHNNAmbient B0 B1 theta →⋆ₙₐ[ℂ]
      UniversalCStarAmalgamAmbient iA iB where
  toFun := cornerLiftAmbient e he_star he_mul pi u hcov hne
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp] theorem cornerLiftHom_apply (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) (he_mul : e * e = e)
    (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0)
    (y : UniversalCStarHNNAmbient B0 B1 theta) :
    cornerLiftHom e he_star he_mul pi u hcov hne y =
      cornerLiftAmbient e he_star he_mul pi u hcov hne y :=
  rfl

/-! ### The ambient description of the corner -/

/-- The corner projection, in the ambient bounded product. -/
def projectionAmbient (e : UniversalCStarAmalgam iA iB) :
    UniversalCStarAmalgamAmbient iA iB :=
  (universalCStarAmalgamSubalgebra iA iB).subtype e

@[simp] theorem cornerLiftAmbient_one (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) (he_mul : e * e = e)
    (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0) :
    cornerLiftAmbient e he_star he_mul pi u hcov hne 1 = projectionAmbient e := by
  apply lp.ext
  funext Q
  exact rfl

theorem projectionAmbient_star (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) :
    star (projectionAmbient e) = projectionAmbient e :=
  (map_star (universalCStarAmalgamSubalgebra iA iB).subtype e).symm.trans
    (congrArg (universalCStarAmalgamSubalgebra iA iB).subtype he_star)

theorem projectionAmbient_mul (e : UniversalCStarAmalgam iA iB)
    (he_mul : e * e = e) :
    projectionAmbient e * projectionAmbient e = projectionAmbient e :=
  (map_mul (universalCStarAmalgamSubalgebra iA iB).subtype e e).symm.trans
    (congrArg (universalCStarAmalgamSubalgebra iA iB).subtype he_mul)

/-- The ambient elements which come from the corner: those lying in the
amalgam and supported by the projection on both sides. -/
def cornerAmbientSet (e : UniversalCStarAmalgam iA iB) (he_star : star e = e) :
    Set (UniversalCStarAmalgamAmbient iA iB) :=
  (universalCStarAmalgamSubalgebra iA iB :
      Set (UniversalCStarAmalgamAmbient iA iB)) ∩
    (cStarCornerSubalgebra (projectionAmbient e)
        (projectionAmbient_star e he_star) :
      Set (UniversalCStarAmalgamAmbient iA iB))

@[simp] theorem mem_cornerAmbientSet_iff (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) {z : UniversalCStarAmalgamAmbient iA iB} :
    z ∈ cornerAmbientSet e he_star ↔
      z ∈ universalCStarAmalgamSubalgebra iA iB ∧
        z ∈ cStarCornerSubalgebra (projectionAmbient e)
          (projectionAmbient_star e he_star) :=
  Iff.rfl

theorem cornerAmbientSet_isClosed (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) : IsClosed (cornerAmbientSet e he_star) :=
  (universalCStarAmalgam_isClosed iA iB).inter
    (cStarCornerSubalgebra_isClosed (projectionAmbient e)
      (projectionAmbient_star e he_star))

theorem subtype_mem_cornerAmbientSet (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) (he_mul : e * e = e)
    (c : CStarCorner e he_star he_mul) :
    (universalCStarAmalgamSubalgebra iA iB).subtype
        (c : UniversalCStarAmalgam iA iB) ∈ cornerAmbientSet e he_star :=
  (mem_cornerAmbientSet_iff e he_star).mpr
    ⟨(c : UniversalCStarAmalgam iA iB).property,
      (map_mul (universalCStarAmalgamSubalgebra iA iB).subtype e
          (c : UniversalCStarAmalgam iA iB)).symm.trans
        (congrArg (universalCStarAmalgamSubalgebra iA iB).subtype c.property.1),
      (map_mul (universalCStarAmalgamSubalgebra iA iB).subtype
          (c : UniversalCStarAmalgam iA iB) e).symm.trans
        (congrArg (universalCStarAmalgamSubalgebra iA iB).subtype
          c.property.2)⟩

theorem projectionAmbient_mem (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) (he_mul : e * e = e) :
    projectionAmbient e ∈ cornerAmbientSet e he_star :=
  subtype_mem_cornerAmbientSet e he_star he_mul 1

/-! ### The lift carries the universal HNN algebra into the corner -/

@[simp] theorem cornerLiftAmbient_base
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0)
    (d : D) :
    cornerLiftAmbient e he_star he_mul pi u hcov hne
        (universalCStarHNNBaseAmbient B0 B1 theta d) =
      (universalCStarAmalgamSubalgebra iA iB).subtype
        ((pi d : CStarCorner e he_star he_mul) :
          UniversalCStarAmalgam iA iB) := by
  apply lp.ext
  funext Q
  exact rfl

@[simp] theorem cornerLiftAmbient_stable
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0) :
    cornerLiftAmbient e he_star he_mul pi u hcov hne
        ((universalCStarHNNStableAmbient B0 B1 theta :
          UniversalCStarHNNAmbient B0 B1 theta)) =
      (universalCStarAmalgamSubalgebra iA iB).subtype
        ((u : CStarCorner e he_star he_mul) : UniversalCStarAmalgam iA iB) := by
  apply lp.ext
  funext Q
  exact rfl

/-- The ambient elements whose lift lies in the corner. -/
def cornerLiftPreimage (e : UniversalCStarAmalgam iA iB)
    (he_star : star e = e) (he_mul : e * e = e)
    (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0) :
    StarSubalgebra ℂ (UniversalCStarHNNAmbient B0 B1 theta) where
  carrier :=
    cornerLiftAmbient e he_star he_mul pi u hcov hne ⁻¹'
      cornerAmbientSet e he_star
  mul_mem' {y z} hy hz := by
    have hy' : cornerLiftAmbient e he_star he_mul pi u hcov hne y ∈
      cornerAmbientSet e he_star := hy
    have hz' : cornerLiftAmbient e he_star he_mul pi u hcov hne z ∈
      cornerAmbientSet e he_star := hz
    have hy₁ := (mem_cornerAmbientSet_iff e he_star).mp hy'
    have hz₁ := (mem_cornerAmbientSet_iff e he_star).mp hz'
    have h : cornerLiftAmbient e he_star he_mul pi u hcov hne (y * z) =
        cornerLiftAmbient e he_star he_mul pi u hcov hne y *
          cornerLiftAmbient e he_star he_mul pi u hcov hne z :=
      map_mul (cornerLiftHom e he_star he_mul pi u hcov hne) y z
    show cornerLiftAmbient e he_star he_mul pi u hcov hne (y * z) ∈
      cornerAmbientSet e he_star
    rw [h]
    exact (mem_cornerAmbientSet_iff e he_star).mpr
      ⟨mul_mem hy₁.1 hz₁.1, mul_mem hy₁.2 hz₁.2⟩
  add_mem' {y z} hy hz := by
    have hy' : cornerLiftAmbient e he_star he_mul pi u hcov hne y ∈
      cornerAmbientSet e he_star := hy
    have hz' : cornerLiftAmbient e he_star he_mul pi u hcov hne z ∈
      cornerAmbientSet e he_star := hz
    have hy₁ := (mem_cornerAmbientSet_iff e he_star).mp hy'
    have hz₁ := (mem_cornerAmbientSet_iff e he_star).mp hz'
    have h : cornerLiftAmbient e he_star he_mul pi u hcov hne (y + z) =
        cornerLiftAmbient e he_star he_mul pi u hcov hne y +
          cornerLiftAmbient e he_star he_mul pi u hcov hne z :=
      map_add (cornerLiftHom e he_star he_mul pi u hcov hne) y z
    show cornerLiftAmbient e he_star he_mul pi u hcov hne (y + z) ∈
      cornerAmbientSet e he_star
    rw [h]
    exact (mem_cornerAmbientSet_iff e he_star).mpr
      ⟨add_mem hy₁.1 hz₁.1, add_mem hy₁.2 hz₁.2⟩
  algebraMap_mem' r := by
    have hone := (mem_cornerAmbientSet_iff e he_star).mp
      (projectionAmbient_mem e he_star he_mul)
    have h : cornerLiftAmbient e he_star he_mul pi u hcov hne
          (algebraMap ℂ (UniversalCStarHNNAmbient B0 B1 theta) r) =
        r • projectionAmbient e := by
      calc cornerLiftAmbient e he_star he_mul pi u hcov hne
              (algebraMap ℂ (UniversalCStarHNNAmbient B0 B1 theta) r)
          = cornerLiftAmbient e he_star he_mul pi u hcov hne (r • 1) :=
            congrArg (cornerLiftAmbient e he_star he_mul pi u hcov hne)
              (Algebra.algebraMap_eq_smul_one r)
        _ = r • cornerLiftAmbient e he_star he_mul pi u hcov hne 1 :=
            map_smul (cornerLiftHom e he_star he_mul pi u hcov hne) r 1
        _ = r • projectionAmbient e :=
            congrArg (fun x ↦ r • x)
              (cornerLiftAmbient_one e he_star he_mul pi u hcov hne)
    show cornerLiftAmbient e he_star he_mul pi u hcov hne
      (algebraMap ℂ (UniversalCStarHNNAmbient B0 B1 theta) r) ∈
        cornerAmbientSet e he_star
    rw [h]
    exact (mem_cornerAmbientSet_iff e he_star).mpr
      ⟨SMulMemClass.smul_mem r hone.1, SMulMemClass.smul_mem r hone.2⟩
  star_mem' {y} hy := by
    have hy' : cornerLiftAmbient e he_star he_mul pi u hcov hne y ∈
      cornerAmbientSet e he_star := hy
    have hy₁ := (mem_cornerAmbientSet_iff e he_star).mp hy'
    have h : cornerLiftAmbient e he_star he_mul pi u hcov hne (star y) =
        star (cornerLiftAmbient e he_star he_mul pi u hcov hne y) :=
      map_star (cornerLiftHom e he_star he_mul pi u hcov hne) y
    show cornerLiftAmbient e he_star he_mul pi u hcov hne (star y) ∈
      cornerAmbientSet e he_star
    rw [h]
    exact (mem_cornerAmbientSet_iff e he_star).mpr
      ⟨star_mem hy₁.1, star_mem hy₁.2⟩

theorem cornerLiftAmbient_mem_of_mem
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0)
    {y : UniversalCStarHNNAmbient B0 B1 theta}
    (hy : y ∈ universalCStarHNNSubalgebra B0 B1 theta) :
    cornerLiftAmbient e he_star he_mul pi u hcov hne y ∈
      cornerAmbientSet e he_star := by
  have hle : StarAlgebra.adjoin ℂ
        (Set.range (universalCStarHNNBaseAmbient B0 B1 theta) ∪
          {(universalCStarHNNStableAmbient B0 B1 theta :
            UniversalCStarHNNAmbient B0 B1 theta)}) ≤
      cornerLiftPreimage e he_star he_mul pi u hcov hne := by
    refine StarAlgebra.adjoin_le ?_
    rintro x (⟨d, rfl⟩ | hx)
    · show cornerLiftAmbient e he_star he_mul pi u hcov hne
        (universalCStarHNNBaseAmbient B0 B1 theta d) ∈ cornerAmbientSet e he_star
      rw [cornerLiftAmbient_base e he_star he_mul pi u hcov hne d]
      exact subtype_mem_cornerAmbientSet e he_star he_mul (pi d)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      show cornerLiftAmbient e he_star he_mul pi u hcov hne
        ((universalCStarHNNStableAmbient B0 B1 theta :
          UniversalCStarHNNAmbient B0 B1 theta)) ∈ cornerAmbientSet e he_star
      rw [cornerLiftAmbient_stable e he_star he_mul pi u hcov hne]
      exact subtype_mem_cornerAmbientSet e he_star he_mul
        (u : CStarCorner e he_star he_mul)
  have hclosed : IsClosed
      ((cornerLiftPreimage e he_star he_mul pi u hcov hne :
          StarSubalgebra ℂ (UniversalCStarHNNAmbient B0 B1 theta)) :
        Set (UniversalCStarHNNAmbient B0 B1 theta)) :=
    (cornerAmbientSet_isClosed e he_star).preimage
      (map_continuous (cornerLiftHom e he_star he_mul pi u hcov hne))
  exact StarSubalgebra.topologicalClosure_minimal hle hclosed hy

/-- The corner lift of the universal C-star HNN algebra. -/
def cornerLift [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0) :
    UniversalCStarHNN B0 B1 theta →⋆ₐ[ℂ] CStarCorner e he_star he_mul where
  toFun x :=
    ⟨(⟨cornerLiftAmbient e he_star he_mul pi u hcov hne
        (x : UniversalCStarHNNAmbient B0 B1 theta),
        ((mem_cornerAmbientSet_iff e he_star).mp
          (cornerLiftAmbient_mem_of_mem e he_star he_mul pi u hcov hne
            x.property)).1⟩ : UniversalCStarAmalgam iA iB),
      Subtype.ext ((mem_cornerAmbientSet_iff e he_star).mp
        (cornerLiftAmbient_mem_of_mem e he_star he_mul pi u hcov hne
          x.property)).2.1,
      Subtype.ext ((mem_cornerAmbientSet_iff e he_star).mp
        (cornerLiftAmbient_mem_of_mem e he_star he_mul pi u hcov hne
          x.property)).2.2⟩
  map_one' := Subtype.ext (Subtype.ext
    (cornerLiftAmbient_one e he_star he_mul pi u hcov hne))
  map_mul' x y := Subtype.ext (Subtype.ext
    (map_mul (cornerLiftHom e he_star he_mul pi u hcov hne)
      (x : UniversalCStarHNNAmbient B0 B1 theta)
      (y : UniversalCStarHNNAmbient B0 B1 theta)))
  map_zero' := Subtype.ext (Subtype.ext
    (map_zero (cornerLiftHom e he_star he_mul pi u hcov hne)))
  map_add' x y := Subtype.ext (Subtype.ext
    (map_add (cornerLiftHom e he_star he_mul pi u hcov hne)
      (x : UniversalCStarHNNAmbient B0 B1 theta)
      (y : UniversalCStarHNNAmbient B0 B1 theta)))
  commutes' r := by
    have hU : (algebraMap ℂ (UniversalCStarHNN B0 B1 theta) r) =
        r • (1 : UniversalCStarHNN B0 B1 theta) :=
      Algebra.algebraMap_eq_smul_one r
    have hC : (algebraMap ℂ (CStarCorner e he_star he_mul) r) =
        r • (1 : CStarCorner e he_star he_mul) :=
      Algebra.algebraMap_eq_smul_one r
    rw [hU, hC]
    exact Subtype.ext (Subtype.ext
      ((map_smul (cornerLiftHom e he_star he_mul pi u hcov hne) r
          (1 : UniversalCStarHNNAmbient B0 B1 theta)).trans
        (congrArg (fun x ↦ r • x)
          (cornerLiftAmbient_one e he_star he_mul pi u hcov hne))))
  map_star' x := Subtype.ext (Subtype.ext
    (map_star (cornerLiftHom e he_star he_mul pi u hcov hne)
      (x : UniversalCStarHNNAmbient B0 B1 theta)))

@[simp] theorem cornerLift_base
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0)
    (d : D) :
    cornerLift e he_star he_mul pi u hcov hne
        (universalCStarHNNBase B0 B1 theta d) = pi d :=
  Subtype.ext (Subtype.ext
    (cornerLiftAmbient_base e he_star he_mul pi u hcov hne d))

@[simp] theorem cornerLift_stable
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0) :
    cornerLift e he_star he_mul pi u hcov hne
        (universalCStarHNNStable B0 B1 theta : UniversalCStarHNN B0 B1 theta) =
      (u : CStarCorner e he_star he_mul) :=
  Subtype.ext (Subtype.ext
    (cornerLiftAmbient_stable e he_star he_mul pi u hcov hne))

/-- A covariant pair in a corner of the universal full amalgam whose
projection survives every compatible coordinate induces a star-algebra
homomorphism of the universal C-star HNN algebra into that corner. -/
theorem exists_universalCStarHNN_cornerMap
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    (e : UniversalCStarAmalgam iA iB) (he_star : star e = e)
    (he_mul : e * e = e) (pi : D →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (u : unitary (CStarCorner e he_star he_mul))
    (hcov : ∀ b : B0,
      (u : CStarCorner e he_star he_mul) * pi (b : D) =
        pi ((theta b : B1) : D) * (u : CStarCorner e he_star he_mul))
    (hne : ∀ Q : CStarAmalgamRepresentation iA iB, cornerProjectionAt e Q ≠ 0) :
    ∃ f : UniversalCStarHNN B0 B1 theta →⋆ₐ[ℂ] CStarCorner e he_star he_mul,
      (∀ d : D, f (universalCStarHNNBase B0 B1 theta d) = pi d) ∧
        f (universalCStarHNNStable B0 B1 theta :
            UniversalCStarHNN B0 B1 theta) =
          (u : CStarCorner e he_star he_mul) :=
  ⟨cornerLift e he_star he_mul pi u hcov hne,
    cornerLift_base e he_star he_mul pi u hcov hne,
    cornerLift_stable e he_star he_mul pi u hcov hne⟩

end Abstract

/-! ## Instantiation at the corona conjugator -/

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

variable (data : CoronaConjugator G S T phi A X)

/-- A unital homomorphism out of `M₂(D)` does not kill `e₀₀`: it would then
kill `e₁₁ = e₁₀e₀₀e₀₁`, and so the unit `e₀₀ + e₁₁`. -/
theorem map_matrixUnitTwo_zeroZero_ne_zero {D : Type} {K : Type}
    [CStarAlgebra D] [CStarAlgebra K] [Nontrivial K]
    (f : CStarMatrix (Fin 2) (Fin 2) D →⋆ₐ[ℂ] K) :
    f (cStarMatrixUnitTwo 0 0 (1 : D)) ≠ 0 := by
  intro h
  have hmat : cStarMatrixUnitTwo 1 0 (1 : D) * cStarMatrixUnitTwo 0 0 (1 : D) *
      cStarMatrixUnitTwo 0 1 (1 : D) = cStarMatrixUnitTwo 1 1 (1 : D) := by
    rw [matrixUnitOne_mul, matrixUnitOne_mul]
  have h11 : f (cStarMatrixUnitTwo 1 1 (1 : D)) = 0 := by
    rw [← hmat, map_mul, map_mul, h, mul_zero, zero_mul]
  have hone : (1 : K) = 0 := by
    calc (1 : K) = f 1 := (map_one f).symm
      _ = f (cStarMatrixUnitTwo 0 0 (1 : D) +
            cStarMatrixUnitTwo 1 1 (1 : D)) := by rw [cStarMatrixUnitTwo_add]
      _ = 0 := by rw [map_add, h, h11, add_zero]
  exact one_ne_zero hone

/-- Ueda's projection survives every compatible coordinate. -/
theorem cornerUnit_cornerProjectionAt_ne_zero
    (Q : CStarAmalgamRepresentation (amalgamLeftInclusion data)
      (amalgamRightInclusion data)) :
    cornerProjectionAt (cornerUnit data) Q ≠ 0 :=
  map_matrixUnitTwo_zeroZero_ne_zero Q.left

/-- Printed Step 1: the covariant pair `(d ↦ diag(d,0), e₁₂f₂₁)` in `ePe`
induces a star-algebra homomorphism `U → ePe`. -/
def uedaCornerLift : universalHNN data →⋆ₐ[ℂ]
    CStarCorner (cornerUnit data) (cornerUnit_star data)
      (cornerUnit_mul data) :=
  cornerLift (cornerUnit data) (cornerUnit_star data) (cornerUnit_mul data)
    (cornerBaseMap data) (cornerStableUnitary data)
    (cornerStableUnitary_covariance data)
    (cornerUnit_cornerProjectionAt_ne_zero data)

@[simp] theorem uedaCornerLift_base (d : baseAlgebra data) :
    uedaCornerLift data (universalBase data d) = cornerBaseMap data d :=
  cornerLift_base (cornerUnit data) (cornerUnit_star data)
    (cornerUnit_mul data) (cornerBaseMap data) (cornerStableUnitary data)
    (cornerStableUnitary_covariance data)
    (cornerUnit_cornerProjectionAt_ne_zero data) d

@[simp] theorem uedaCornerLift_stable :
    uedaCornerLift data
        ((universalStable data : unitary (universalHNN data)) :
          universalHNN data) =
      (cornerStableUnitary data :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) :=
  cornerLift_stable (cornerUnit data) (cornerUnit_star data)
    (cornerUnit_mul data) (cornerBaseMap data) (cornerStableUnitary data)
    (cornerStableUnitary_covariance data)
    (cornerUnit_cornerProjectionAt_ne_zero data)

/-- The evaluated corner map composed with the lift is the upper-left corner
of the coordinate evaluation.  Both are lifts of the same covariant pair to
the corner of `M₂(R.carrier)`, which is a same-universe codomain, so the
universal property applies and the two agree. -/
theorem evaluatedCornerMap_comp_uedaCornerLift (R : HNNCoordinate data) :
    (evaluatedCornerMap data R).comp (uedaCornerLift data) =
      cStarUpperLeftCornerMap.comp
        (universalCStarHNNEval (sourceEdgeAlgebra data)
          (targetEdgeAlgebra data) (edgeIsomorphism data) R) := by
  haveI : Nontrivial (CStarCorner (cStarUpperLeftCornerUnit (K := R.carrier))
      (cStarUpperLeftCornerUnit_star (K := R.carrier))
      (cStarUpperLeftCornerUnit_mul (K := R.carrier))) :=
    ⟨⟨cStarUpperLeftCornerMap (1 : R.carrier),
      cStarUpperLeftCornerMap (0 : R.carrier),
      fun h ↦ one_ne_zero (cStarUpperLeftCornerMap_injective h)⟩⟩
  refine (universalCStarHNN_existsUnique_lift
    (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data)
    (cornerComp R.base)
    (unitaryMapOfStarAlgHom cStarUpperLeftCornerMap R.stable)
    (fun b ↦ by
      have h := congrArg (cStarUpperLeftCornerMap (K := R.carrier))
        (R.covariance b)
      simpa [cornerComp_apply, coe_unitaryMapOfStarAlgHom, map_mul]
        using h)).unique ?_ ?_
  · constructor
    · intro d
      exact (congrArg (evaluatedCornerMap data R)
        (uedaCornerLift_base data d)).trans
        (evaluatedCornerMap_base data R d)
    · exact (congrArg (evaluatedCornerMap data R)
        (uedaCornerLift_stable data)).trans
        (evaluatedCornerMap_stable data R)
  · constructor
    · intro d
      simp
    · simp

theorem uedaCornerLift_injective :
    Function.Injective (uedaCornerLift data) := by
  intro x y hxy
  refine universalCStarHNN_eq_of_forall_eval_eq _ _ _ fun R ↦ ?_
  apply cStarUpperLeftCornerMap_injective
  have hx : cStarUpperLeftCornerMap (universalCStarHNNEval
        (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
        (edgeIsomorphism data) R x) =
      evaluatedCornerMap data R (uedaCornerLift data x) :=
    (DFunLike.congr_fun (evaluatedCornerMap_comp_uedaCornerLift data R) x).symm
  have hy : cStarUpperLeftCornerMap (universalCStarHNNEval
        (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
        (edgeIsomorphism data) R y) =
      evaluatedCornerMap data R (uedaCornerLift data y) :=
    (DFunLike.congr_fun (evaluatedCornerMap_comp_uedaCornerLift data R) y).symm
  exact hx.trans ((congrArg (evaluatedCornerMap data R) hxy).trans hy.symm)

/-- Printed Step 1, closed: the universal C-star HNN algebra maps injectively
into Ueda's corner of the full amalgam, carrying the base and the stable
unitary to the printed elements. -/
theorem uedaCornerMap_proved : UedaCornerMapStatement := by
  intro G _ S T phi A _ X _ data
  exact ⟨uedaCornerLift data, uedaCornerLift_base data,
    uedaCornerLift_stable data, uedaCornerLift_injective data⟩

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
