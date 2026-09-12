import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaClass
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerGramSequence
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.VectorOmegaAction

/-!
# The corrected-corner corona embedding

The coordinate inclusion of a finite matrix corner is isometric and
multiplicative.  Consequently it preserves and reflects null sequences and
descends to an injective nonunital star homomorphism of matrix coronas.  This
module isolates that construction and its value on the actual polar-corrected
group generators.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix PrintedCornerCompression
open VectorOmegaAction
open CoronaProjectionLifting
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## The coordinate corner embedding as a sequence map -/

theorem cornerEmbed_zero {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian) :
    cornerEmbed hq (0 : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) = 0 := by
  simpa using cornerEmbed_sub hq
    (0 : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) 0

theorem cornerEmbed_neg {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (A : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    cornerEmbed hq (-A) = -cornerEmbed hq A := by
  have h := cornerEmbed_sub hq 0 A
  rw [cornerEmbed_zero hq] at h
  simpa using h

theorem cornerEmbed_add {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (A B : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    cornerEmbed hq (A + B) = cornerEmbed hq A + cornerEmbed hq B := by
  have h := cornerEmbed_sub hq A (-B)
  rw [cornerEmbed_neg hq] at h
  simpa [sub_eq_add_neg] using h

theorem blockExtend_smul {Y : Type*} (p : Y → Prop) [DecidablePred p]
    (c : ℂ) (A : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    blockExtend p (c • A) = c • blockExtend p A := by
  ext i j
  simp [blockExtend]

theorem cornerEmbed_smul {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian) (c : ℂ)
    (A : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    cornerEmbed hq (c • A) = c • cornerEmbed hq A := by
  simp only [cornerEmbed, blockExtend_smul, Matrix.mul_smul,
    Matrix.smul_mul]

/-- Coordinatewise inclusion of corrected corner matrices into their ambient
matrices. -/
def cornerEmbedSequence {H : Type*} [Group H] {model : ℕ → FiniteModel}
    (D : PrintedCornerData H model)
    (a : BoundedMatrixSequence (fun n ↦ D.cornerModel n)) :
    BoundedMatrixSequence (fun n ↦ model n) :=
  ⟨fun n ↦ cornerEmbed (D.qHermitian n) (a n), memℓp_infty ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    change ‖cornerEmbed (D.qHermitian n) (a n)‖ ≤ ‖a‖
    rw [norm_cornerEmbed]
    exact boundedMatrixSequence_coord_norm_le
      (fun n ↦ D.cornerModel n) a n⟩⟩

@[simp] theorem cornerEmbedSequence_apply {H : Type*} [Group H]
    {model : ℕ → FiniteModel} (D : PrintedCornerData H model)
    (a : BoundedMatrixSequence (fun n ↦ D.cornerModel n)) (n : ℕ) :
    cornerEmbedSequence D a n = cornerEmbed (D.qHermitian n) (a n) :=
  rfl

theorem cornerEmbedSequence_zero {H : Type*} [Group H]
    {model : ℕ → FiniteModel} (D : PrintedCornerData H model) :
    cornerEmbedSequence D 0 = 0 := by
  refine lp.ext (funext fun n ↦ ?_)
  simpa using cornerEmbed_zero (D.qHermitian n)

theorem cornerEmbedSequence_add {H : Type*} [Group H]
    {model : ℕ → FiniteModel} (D : PrintedCornerData H model)
    (a b : BoundedMatrixSequence (fun n ↦ D.cornerModel n)) :
    cornerEmbedSequence D (a + b) =
      cornerEmbedSequence D a + cornerEmbedSequence D b := by
  refine lp.ext (funext fun n ↦ ?_)
  simpa using cornerEmbed_add (D.qHermitian n) (a n) (b n)

theorem cornerEmbedSequence_sub {H : Type*} [Group H]
    {model : ℕ → FiniteModel} (D : PrintedCornerData H model)
    (a b : BoundedMatrixSequence (fun n ↦ D.cornerModel n)) :
    cornerEmbedSequence D (a - b) =
      cornerEmbedSequence D a - cornerEmbedSequence D b := by
  refine lp.ext (funext fun n ↦ ?_)
  simpa using cornerEmbed_sub (D.qHermitian n) (a n) (b n)

theorem cornerEmbedSequence_mul {H : Type*} [Group H]
    {model : ℕ → FiniteModel} (D : PrintedCornerData H model)
    (a b : BoundedMatrixSequence (fun n ↦ D.cornerModel n)) :
    cornerEmbedSequence D (a * b) =
      cornerEmbedSequence D a * cornerEmbedSequence D b := by
  refine lp.ext (funext fun n ↦ ?_)
  simpa using cornerEmbed_mul (D.qHermitian n) (a n) (b n)

theorem cornerEmbedSequence_smul {H : Type*} [Group H]
    {model : ℕ → FiniteModel} (D : PrintedCornerData H model)
    (c : ℂ) (a : BoundedMatrixSequence (fun n ↦ D.cornerModel n)) :
    cornerEmbedSequence D (c • a) = c • cornerEmbedSequence D a := by
  refine lp.ext (funext fun n ↦ ?_)
  simpa using cornerEmbed_smul (D.qHermitian n) c (a n)

theorem cornerEmbedSequence_star {H : Type*} [Group H]
    {model : ℕ → FiniteModel} (D : PrintedCornerData H model)
    (a : BoundedMatrixSequence (fun n ↦ D.cornerModel n)) :
    cornerEmbedSequence D (star a) = star (cornerEmbedSequence D a) := by
  refine lp.ext (funext fun n ↦ ?_)
  change cornerEmbed (D.qHermitian n) ((a n)ᴴ) =
    (cornerEmbed (D.qHermitian n) (a n))ᴴ
  exact (cornerEmbed_conjTranspose (D.qHermitian n) (a n)).symm

/-- The coordinate corner inclusion preserves and reflects null sequences at
every filter. -/
theorem isNull_cornerEmbedSequence_iff {H : Type*} [Group H]
    {model : ℕ → FiniteModel} (D : PrintedCornerData H model)
    (l : Filter ℕ) (a : BoundedMatrixSequence (fun n ↦ D.cornerModel n)) :
    IsNullMatrixSequence (fun n ↦ model n) l (cornerEmbedSequence D a) ↔
      IsNullMatrixSequence (fun n ↦ D.cornerModel n) l a := by
  have hfun : (fun n ↦ ‖cornerEmbedSequence D a n‖) = fun n ↦ ‖a n‖ := by
    funext n
    exact norm_cornerEmbed (D.qHermitian n) (a n)
  show Tendsto (fun n ↦ ‖cornerEmbedSequence D a n‖) l (nhds 0) ↔
    Tendsto (fun n ↦ ‖a n‖) l (nhds 0)
  rw [hfun]

/-! ## The induced nonunital star homomorphism of coronas -/

/-- A chosen bounded representative of a corrected-corner corona class. -/
def correctedCornerCoronaLift {H : Type*} [Group H]
    {model : ℕ → FiniteModel} [∀ n, Nonempty (model n)]
    (D : PrintedCornerData H model) (l : Filter ℕ)
    (x : FilterMatrixCStarCorona (fun n ↦ D.cornerModel n) l) :
    BoundedMatrixSequence (fun n ↦ D.cornerModel n) :=
  Function.surjInv
    (filterMatrixCStarCoronaMk_surjective
      (fun n ↦ D.cornerModel n) l) x

theorem correctedCornerCoronaLift_spec {H : Type*} [Group H]
    {model : ℕ → FiniteModel} [∀ n, Nonempty (model n)]
    (D : PrintedCornerData H model) (l : Filter ℕ)
    (x : FilterMatrixCStarCorona (fun n ↦ D.cornerModel n) l) :
    filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l
      (correctedCornerCoronaLift D l x) = x :=
  Function.surjInv_eq _ x

/-- Read a corrected-corner corona class in the retained ambient matrices. -/
def correctedCornerCoronaEmbed {H : Type*} [Group H]
    {model : ℕ → FiniteModel} [∀ n, Nonempty (model n)]
    (D : PrintedCornerData H model) (l : Filter ℕ)
    (x : FilterMatrixCStarCorona (fun n ↦ D.cornerModel n) l) :
    FilterMatrixCStarCorona (fun n ↦ model n) l :=
  filterMatrixCStarCoronaMk (fun n ↦ model n) l
    (cornerEmbedSequence D (correctedCornerCoronaLift D l x))

/-- The chosen-lift definition is independent of the representative. -/
theorem correctedCornerCoronaEmbed_mk {H : Type*} [Group H]
    {model : ℕ → FiniteModel} [∀ n, Nonempty (model n)]
    (D : PrintedCornerData H model) (l : Filter ℕ)
    (a : BoundedMatrixSequence (fun n ↦ D.cornerModel n)) :
    correctedCornerCoronaEmbed D l
        (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a) =
      filterMatrixCStarCoronaMk (fun n ↦ model n) l
        (cornerEmbedSequence D a) := by
  have hb := correctedCornerCoronaLift_spec D l
    (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a)
  have hnull : IsNullMatrixSequence (fun n ↦ D.cornerModel n) l
      (correctedCornerCoronaLift D l
        (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a) - a) := by
    rw [← filterMatrixCStarCoronaMk_eq_zero_iff]
    let qC := filterMatrixCStarCoronaQuotient
      (fun n ↦ D.cornerModel n) l
    change qC (correctedCornerCoronaLift D l
      (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a)) =
        qC a at hb
    have hmap : qC
        (correctedCornerCoronaLift D l
          (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a) - a) =
        qC (correctedCornerCoronaLift D l
          (filterMatrixCStarCoronaMk
            (fun n ↦ D.cornerModel n) l a)) - qC a :=
      map_sub qC _ _
    change qC
      (correctedCornerCoronaLift D l
        (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a) - a) = 0
    rw [hmap, hb, sub_self]
  have hnull' : IsNullMatrixSequence (fun n ↦ model n) l
      (cornerEmbedSequence D
        (correctedCornerCoronaLift D l
          (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a)) -
        cornerEmbedSequence D a) := by
    rw [← cornerEmbedSequence_sub]
    exact (isNull_cornerEmbedSequence_iff D l _).mpr hnull
  have hzero : filterMatrixCStarCoronaMk (fun n ↦ model n) l
      (cornerEmbedSequence D
        (correctedCornerCoronaLift D l
          (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a)) -
        cornerEmbedSequence D a) = 0 :=
    (filterMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ model n) l _).mpr hnull'
  let qA := filterMatrixCStarCoronaQuotient (fun n ↦ model n) l
  have hmap : qA
      (cornerEmbedSequence D
        (correctedCornerCoronaLift D l
          (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a)) -
        cornerEmbedSequence D a) =
      qA (cornerEmbedSequence D
        (correctedCornerCoronaLift D l
          (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a))) -
        qA (cornerEmbedSequence D a) :=
    map_sub qA _ _
  change qA
    (cornerEmbedSequence D
      (correctedCornerCoronaLift D l
        (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a)) -
      cornerEmbedSequence D a) = 0 at hzero
  rw [hmap, sub_eq_zero] at hzero
  exact hzero

/-- The coordinate corner inclusion descends to a nonunital star homomorphism
of coronas. -/
def correctedCornerCoronaEmbedHom {H : Type*} [Group H]
    {model : ℕ → FiniteModel} [∀ n, Nonempty (model n)]
    (D : PrintedCornerData H model) (l : Filter ℕ) :
    FilterMatrixCStarCorona (fun n ↦ D.cornerModel n) l →⋆ₙₐ[ℂ]
      FilterMatrixCStarCorona (fun n ↦ model n) l where
  toFun := correctedCornerCoronaEmbed D l
  map_smul' c x := by
    obtain ⟨a, rfl⟩ :=
      filterMatrixCStarCoronaMk_surjective
        (fun n ↦ D.cornerModel n) l x
    let qC := filterMatrixCStarCoronaQuotient
      (fun n ↦ D.cornerModel n) l
    let qA := filterMatrixCStarCoronaQuotient (fun n ↦ model n) l
    have hsmulC :
        filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l (c • a) =
          c • filterMatrixCStarCoronaMk
            (fun n ↦ D.cornerModel n) l a := by
      calc
        qC (c • a) = qC
            ((algebraMap ℂ (BoundedMatrixSequence
              (fun n ↦ D.cornerModel n)) c) * a) :=
            congrArg qC (Algebra.smul_def c a)
        _ = qC (algebraMap ℂ (BoundedMatrixSequence
              (fun n ↦ D.cornerModel n)) c) * qC a := map_mul qC _ _
        _ = (algebraMap ℂ (FilterMatrixCStarCorona
              (fun n ↦ D.cornerModel n) l) c) * qC a :=
            congrArg (fun z ↦ z * qC a) (qC.commutes c)
        _ = c • qC a := (Algebra.smul_def c (qC a)).symm
    have hsmulA : filterMatrixCStarCoronaMk (fun n ↦ model n) l
          (c • cornerEmbedSequence D a) =
        c • filterMatrixCStarCoronaMk (fun n ↦ model n) l
          (cornerEmbedSequence D a) := by
      calc
        qA (c • cornerEmbedSequence D a) = qA
            ((algebraMap ℂ (BoundedMatrixSequence
              (fun n ↦ model n)) c) * cornerEmbedSequence D a) :=
            congrArg qA (Algebra.smul_def c (cornerEmbedSequence D a))
        _ = qA (algebraMap ℂ (BoundedMatrixSequence
              (fun n ↦ model n)) c) * qA (cornerEmbedSequence D a) :=
            map_mul qA _ _
        _ = (algebraMap ℂ (FilterMatrixCStarCorona
              (fun n ↦ model n) l) c) * qA (cornerEmbedSequence D a) :=
            congrArg (fun z ↦ z * qA (cornerEmbedSequence D a))
              (qA.commutes c)
        _ = c • qA (cornerEmbedSequence D a) :=
            (Algebra.smul_def c (qA (cornerEmbedSequence D a))).symm
    change correctedCornerCoronaEmbed D l
        (c • filterMatrixCStarCoronaMk
          (fun n ↦ D.cornerModel n) l a) =
      c • correctedCornerCoronaEmbed D l
        (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a)
    rw [← hsmulC, correctedCornerCoronaEmbed_mk,
      correctedCornerCoronaEmbed_mk, cornerEmbedSequence_smul, hsmulA]
  map_zero' := by
    have hzero := correctedCornerCoronaEmbed_mk D l
      (0 : BoundedMatrixSequence (fun n ↦ D.cornerModel n))
    simpa [cornerEmbedSequence_zero] using hzero
  map_add' x y := by
    obtain ⟨a, rfl⟩ :=
      filterMatrixCStarCoronaMk_surjective
        (fun n ↦ D.cornerModel n) l x
    obtain ⟨b, rfl⟩ :=
      filterMatrixCStarCoronaMk_surjective
        (fun n ↦ D.cornerModel n) l y
    let qC := filterMatrixCStarCoronaQuotient
      (fun n ↦ D.cornerModel n) l
    let qA := filterMatrixCStarCoronaQuotient (fun n ↦ model n) l
    have haddC : filterMatrixCStarCoronaMk
          (fun n ↦ D.cornerModel n) l (a + b) =
        filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a +
          filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l b := by
      change qC (a + b) = qC a + qC b
      exact qC.map_add a b
    have haddA : filterMatrixCStarCoronaMk (fun n ↦ model n) l
          (cornerEmbedSequence D a + cornerEmbedSequence D b) =
        filterMatrixCStarCoronaMk (fun n ↦ model n) l
            (cornerEmbedSequence D a) +
          filterMatrixCStarCoronaMk (fun n ↦ model n) l
            (cornerEmbedSequence D b) := by
      change qA (cornerEmbedSequence D a + cornerEmbedSequence D b) =
        qA (cornerEmbedSequence D a) + qA (cornerEmbedSequence D b)
      exact qA.map_add (cornerEmbedSequence D a) (cornerEmbedSequence D b)
    rw [← haddC, correctedCornerCoronaEmbed_mk,
      correctedCornerCoronaEmbed_mk, correctedCornerCoronaEmbed_mk,
      cornerEmbedSequence_add, haddA]
  map_mul' x y := by
    obtain ⟨a, rfl⟩ :=
      filterMatrixCStarCoronaMk_surjective
        (fun n ↦ D.cornerModel n) l x
    obtain ⟨b, rfl⟩ :=
      filterMatrixCStarCoronaMk_surjective
        (fun n ↦ D.cornerModel n) l y
    let qC := filterMatrixCStarCoronaQuotient
      (fun n ↦ D.cornerModel n) l
    let qA := filterMatrixCStarCoronaQuotient (fun n ↦ model n) l
    have hmulC : filterMatrixCStarCoronaMk
          (fun n ↦ D.cornerModel n) l (a * b) =
        filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l a *
          filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l b := by
      change qC (a * b) = qC a * qC b
      exact qC.map_mul a b
    have hmulA : filterMatrixCStarCoronaMk (fun n ↦ model n) l
          (cornerEmbedSequence D a * cornerEmbedSequence D b) =
        filterMatrixCStarCoronaMk (fun n ↦ model n) l
            (cornerEmbedSequence D a) *
          filterMatrixCStarCoronaMk (fun n ↦ model n) l
            (cornerEmbedSequence D b) := by
      change qA (cornerEmbedSequence D a * cornerEmbedSequence D b) =
        qA (cornerEmbedSequence D a) * qA (cornerEmbedSequence D b)
      exact qA.map_mul (cornerEmbedSequence D a) (cornerEmbedSequence D b)
    rw [← hmulC, correctedCornerCoronaEmbed_mk,
      correctedCornerCoronaEmbed_mk, correctedCornerCoronaEmbed_mk,
      cornerEmbedSequence_mul, hmulA]
  map_star' x := by
    obtain ⟨a, rfl⟩ :=
      filterMatrixCStarCoronaMk_surjective
        (fun n ↦ D.cornerModel n) l x
    rw [filterMatrixCStarCorona_star_mk, correctedCornerCoronaEmbed_mk,
      correctedCornerCoronaEmbed_mk, cornerEmbedSequence_star,
      filterMatrixCStarCorona_star_mk]

/-- The induced nonunital star homomorphism is injective. -/
theorem correctedCornerCoronaEmbedHom_injective {H : Type*} [Group H]
    {model : ℕ → FiniteModel} [∀ n, Nonempty (model n)]
    (D : PrintedCornerData H model) (l : Filter ℕ) :
    Function.Injective (correctedCornerCoronaEmbedHom D l) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ :=
    filterMatrixCStarCoronaMk_surjective
      (fun n ↦ D.cornerModel n) l x
  obtain ⟨b, rfl⟩ :=
    filterMatrixCStarCoronaMk_surjective
      (fun n ↦ D.cornerModel n) l y
  change correctedCornerCoronaEmbed D l _ =
    correctedCornerCoronaEmbed D l _ at hxy
  rw [correctedCornerCoronaEmbed_mk,
    correctedCornerCoronaEmbed_mk] at hxy
  have hzeroAmbient :
      (filterMatrixCStarCoronaQuotient (fun n ↦ model n) l)
        (cornerEmbedSequence D a - cornerEmbedSequence D b) = 0 := by
    let qA := filterMatrixCStarCoronaQuotient (fun n ↦ model n) l
    change qA (cornerEmbedSequence D a) =
      qA (cornerEmbedSequence D b) at hxy
    have hmap : qA (cornerEmbedSequence D a - cornerEmbedSequence D b) =
        qA (cornerEmbedSequence D a) - qA (cornerEmbedSequence D b) :=
      map_sub qA _ _
    rw [hmap, hxy, sub_self]
  have hnullAmbient : IsNullMatrixSequence (fun n ↦ model n) l
      (cornerEmbedSequence D (a - b)) := by
    rw [cornerEmbedSequence_sub]
    exact (filterMatrixCStarCoronaMk_eq_zero_iff
      (fun n ↦ model n) l _).mp hzeroAmbient
  have hnullCorner : IsNullMatrixSequence (fun n ↦ D.cornerModel n) l
      (a - b) :=
    (isNull_cornerEmbedSequence_iff D l (a - b)).mp hnullAmbient
  change (filterMatrixCStarCoronaQuotient
      (fun n ↦ D.cornerModel n) l) a =
    (filterMatrixCStarCoronaQuotient
      (fun n ↦ D.cornerModel n) l) b
  let qC := filterMatrixCStarCoronaQuotient
    (fun n ↦ D.cornerModel n) l
  have hmap : qC (a - b) = qC a - qC b := map_sub qC a b
  rw [← sub_eq_zero, ← hmap]
  exact (filterMatrixCStarCoronaMk_eq_zero_iff
    (fun n ↦ D.cornerModel n) l _).mpr hnullCorner

/-! ## The corrected generator class -/

/-- The corona class of the raw printed corrected maps.  This definition does
not construct the surrounding omega representation, avoiding unnecessary
normalization of its proof fields. -/
def correctedCornerCoronaGeneratorClass {H : Type*} [Group H]
    {model : ℕ → FiniteModel} [∀ n, Nonempty (model n)]
    (D : PrintedCornerData H model)
    (omega : Ultrafilter ℕ) (g : H) :
    FilterMatrixCStarCorona
      (fun n ↦ D.cornerModel n) (omega : Filter ℕ) :=
  filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)
    (omega : Filter ℕ)
    (unitarySeq (fun n ↦ D.cornerModel n)
      (fun n g ↦ D.cornerMap n g) g)

/-- On the actual corrected representation, the corona embedding is exactly
the class of the ambient corner matrices used by `CornerCoronaClass`. -/
theorem correctedCornerCoronaEmbed_coronaRep {H : Type*} [Group H]
    {model : ℕ → FiniteModel} [∀ n, Nonempty (model n)]
    (D : PrintedCornerData H model)
    (omega : Ultrafilter ℕ) (g : H) :
    correctedCornerCoronaEmbedHom D (omega : Filter ℕ)
        (correctedCornerCoronaGeneratorClass D omega g) =
      filterMatrixCStarCoronaMk (fun n ↦ model n) (omega : Filter ℕ)
        (ambientCornerSeq D g) := by
  change correctedCornerCoronaEmbed D (omega : Filter ℕ)
      (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)
        (omega : Filter ℕ)
        (unitarySeq (fun n ↦ D.cornerModel n)
          (fun n g ↦ D.cornerMap n g) g)) = _
  rw [correctedCornerCoronaEmbed_mk]
  congr 1

end


end OneSidedMFRadical
end Manuscript
end GroupApproximation
