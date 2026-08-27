import GroupApproximation.Analysis.MFAlgebraDimensionNormalization

/-!
# Two norm coronas as complementary corners of one norm corona

Given two model sequences `Z` and `W`, the coordinatewise block sum
`n ↦ Z n ⊕ W n` carries both coronas as complementary corners:

* `leftCoronaHom` sends the class of `a` to the class of `diag(a, 0)`;
* `rightCoronaHom` sends the class of `b` to the class of `diag(0, b)`.

Both are isometric, their ranges multiply to zero in either order, and the two
images of the unit add up to the unit.  A joined element therefore dominates
each leg in norm: `‖a‖ ≤ ‖jZ a + jW b‖` and `‖b‖ ≤ ‖jZ a + jW b‖`.

This is the closure property that turns approximation of *one* element into
approximation of a finite set: two compatible corona pairs can be replaced by
a single compatible pair on the joined models that is at least as good on both
of the elements they were chosen for.  Nothing here mentions amalgams.

The construction copies the corner-descent pattern of
`Analysis/MFAlgebraDimensionNormalization` — coordinate map, bounded sequence
map, null-sequence characterization, descent to the corona along a chosen
lift — at the binary block sum instead of the cumulative one.

The norm identity `‖diag(A, B)‖ = max ‖A‖ ‖B‖` is `l2_opNorm_blockDiag` of
`Sofic/NormMFUniversalCorona`; the reverse bound `‖jZ a + jW b‖ ≤ max ‖a‖ ‖b‖`
is not proved here because no consumer needs it: the point of the join is that
it is *at least* as large as each leg.

This module is not in the root import list.  It was authored while builds were
suspended, so it is kept out of the closure until it has been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFillCoronaJoin

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Z W : ℕ → FiniteModel)

/-! ## The joined model sequence -/

/-- The coordinatewise block sum of two model sequences. -/
abbrev joinModel (n : ℕ) : FiniteModel := blockSumModel (Z n) (W n)

theorem nonempty_joinModel (hZ : ∀ n, Nonempty (Z n)) (n : ℕ) :
    Nonempty (joinModel Z W n) :=
  Nonempty.elim (hZ n) fun z ↦ ⟨Sum.inl z⟩

instance instNonemptyJoinModel [h : ∀ n, Nonempty (Z n)] (n : ℕ) :
    Nonempty (joinModel Z W n) :=
  nonempty_joinModel Z W h n

/-! ## The join on bounded matrix sequences -/

/-- The coordinatewise block diagonal of two bounded matrix sequences. -/
def joinSeq (a : BoundedMatrixSequence (fun n ↦ Z n))
    (b : BoundedMatrixSequence (fun n ↦ W n)) :
    BoundedMatrixSequence (fun n ↦ joinModel Z W n) :=
  ⟨fun n ↦ blockDiagMatrix (Z n) (W n) (a n) (b n), memℓp_infty ⟨max ‖a‖ ‖b‖, by
    rintro _ ⟨n, rfl⟩
    exact le_of_eq_of_le (l2_opNorm_blockDiag (Z n) (W n) (a n) (b n))
      (max_le_max (boundedMatrixSequence_coord_norm_le (fun n ↦ Z n) a n)
        (boundedMatrixSequence_coord_norm_le (fun n ↦ W n) b n))⟩⟩

@[simp] theorem joinSeq_apply (a : BoundedMatrixSequence (fun n ↦ Z n))
    (b : BoundedMatrixSequence (fun n ↦ W n)) (n : ℕ) :
    joinSeq Z W a b n = blockDiagMatrix (Z n) (W n) (a n) (b n) := rfl

/-- Each coordinate of a join is a block diagonal, so its operator norm is the
maximum of the two coordinate norms. -/
theorem norm_joinSeq_apply (a : BoundedMatrixSequence (fun n ↦ Z n))
    (b : BoundedMatrixSequence (fun n ↦ W n)) (n : ℕ) :
    ‖joinSeq Z W a b n‖ = max ‖a n‖ ‖b n‖ :=
  l2_opNorm_blockDiag (Z n) (W n) (a n) (b n)

theorem joinSeq_zero : joinSeq Z W 0 0 = 0 := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_zero, Pi.zero_apply]
  exact MFAlgebraDimension.blockDiagMatrix_zero (Z n) (W n)

theorem joinSeq_one : joinSeq Z W 1 1 = 1 := by
  refine lp.ext (funext fun n ↦ ?_)
  have h : blockDiagMatrix (Z n) (W n) 1 1 = 1 := blockDiagMatrix_one (Z n) (W n)
  simpa using h

theorem joinSeq_add (a c : BoundedMatrixSequence (fun n ↦ Z n))
    (b d : BoundedMatrixSequence (fun n ↦ W n)) :
    joinSeq Z W (a + c) (b + d) = joinSeq Z W a b + joinSeq Z W c d := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_add, Pi.add_apply]
  exact (MFAlgebraDimension.blockDiagMatrix_add (Z n) (W n)
    (a n) (c n) (b n) (d n)).symm

theorem joinSeq_sub (a c : BoundedMatrixSequence (fun n ↦ Z n))
    (b d : BoundedMatrixSequence (fun n ↦ W n)) :
    joinSeq Z W (a - c) (b - d) = joinSeq Z W a b - joinSeq Z W c d := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_sub, Pi.sub_apply]
  exact (blockDiagMatrix_sub (Z n) (W n) (a n) (c n) (b n) (d n)).symm

theorem joinSeq_mul (a c : BoundedMatrixSequence (fun n ↦ Z n))
    (b d : BoundedMatrixSequence (fun n ↦ W n)) :
    joinSeq Z W (a * c) (b * d) = joinSeq Z W a b * joinSeq Z W c d := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.infty_coeFn_mul, Pi.mul_apply]
  exact (blockDiagMatrix_mul (Z n) (W n) (a n) (c n) (b n) (d n)).symm

theorem joinSeq_smul (c : ℂ) (a : BoundedMatrixSequence (fun n ↦ Z n))
    (b : BoundedMatrixSequence (fun n ↦ W n)) :
    joinSeq Z W (c • a) (c • b) = c • joinSeq Z W a b := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_smul, Pi.smul_apply]
  exact (MFAlgebraDimension.blockDiagMatrix_smul (Z n) (W n) c (a n) (b n)).symm

theorem joinSeq_star (a : BoundedMatrixSequence (fun n ↦ Z n))
    (b : BoundedMatrixSequence (fun n ↦ W n)) :
    joinSeq Z W (star a) (star b) = star (joinSeq Z W a b) := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [lp.coeFn_star, Pi.star_apply]
  exact (blockDiagMatrix_conjTranspose (Z n) (W n) (a n) (b n)).symm

/-- A join is null exactly when both of its legs are. -/
theorem isNull_joinSeq_iff (l : Filter ℕ)
    (a : BoundedMatrixSequence (fun n ↦ Z n))
    (b : BoundedMatrixSequence (fun n ↦ W n)) :
    IsNullMatrixSequence (fun n ↦ joinModel Z W n) l (joinSeq Z W a b) ↔
      IsNullMatrixSequence (fun n ↦ Z n) l a ∧
        IsNullMatrixSequence (fun n ↦ W n) l b := by
  show Tendsto (fun n ↦ ‖joinSeq Z W a b n‖) l (nhds 0) ↔
    Tendsto (fun n ↦ ‖a n‖) l (nhds 0) ∧ Tendsto (fun n ↦ ‖b n‖) l (nhds 0)
  constructor
  · intro h
    have hleft : ∀ n, ‖a n‖ ≤ ‖joinSeq Z W a b n‖ := by
      intro n
      rw [norm_joinSeq_apply]
      exact le_max_left _ _
    have hright : ∀ n, ‖b n‖ ≤ ‖joinSeq Z W a b n‖ := by
      intro n
      rw [norm_joinSeq_apply]
      exact le_max_right _ _
    exact ⟨squeeze_zero (fun n ↦ norm_nonneg _) hleft h,
      squeeze_zero (fun n ↦ norm_nonneg _) hright h⟩
  · rintro ⟨ha, hb⟩
    have hmax := ha.max hb
    rw [max_self] at hmax
    exact Filter.Tendsto.congr (fun n ↦ (norm_joinSeq_apply Z W a b n).symm) hmax

/-! ## The two legs at the level of sequences -/

/-- The left leg `a ↦ diag(a, 0)`. -/
def leftSeq (a : BoundedMatrixSequence (fun n ↦ Z n)) :
    BoundedMatrixSequence (fun n ↦ joinModel Z W n) :=
  joinSeq Z W a 0

/-- The right leg `b ↦ diag(0, b)`. -/
def rightSeq (b : BoundedMatrixSequence (fun n ↦ W n)) :
    BoundedMatrixSequence (fun n ↦ joinModel Z W n) :=
  joinSeq Z W 0 b

theorem leftSeq_zero : leftSeq Z W 0 = 0 := joinSeq_zero Z W

theorem rightSeq_zero : rightSeq Z W 0 = 0 := joinSeq_zero Z W

theorem leftSeq_add (a c : BoundedMatrixSequence (fun n ↦ Z n)) :
    leftSeq Z W (a + c) = leftSeq Z W a + leftSeq Z W c := by
  have h := joinSeq_add Z W a c 0 0
  rw [add_zero] at h
  exact h

theorem rightSeq_add (b d : BoundedMatrixSequence (fun n ↦ W n)) :
    rightSeq Z W (b + d) = rightSeq Z W b + rightSeq Z W d := by
  have h := joinSeq_add Z W 0 0 b d
  rw [add_zero] at h
  exact h

theorem leftSeq_sub (a c : BoundedMatrixSequence (fun n ↦ Z n)) :
    leftSeq Z W (a - c) = leftSeq Z W a - leftSeq Z W c := by
  have h := joinSeq_sub Z W a c 0 0
  rw [sub_zero] at h
  exact h

theorem rightSeq_sub (b d : BoundedMatrixSequence (fun n ↦ W n)) :
    rightSeq Z W (b - d) = rightSeq Z W b - rightSeq Z W d := by
  have h := joinSeq_sub Z W 0 0 b d
  rw [sub_zero] at h
  exact h

theorem leftSeq_mul (a c : BoundedMatrixSequence (fun n ↦ Z n)) :
    leftSeq Z W (a * c) = leftSeq Z W a * leftSeq Z W c := by
  have h := joinSeq_mul Z W a c 0 0
  rw [mul_zero] at h
  exact h

theorem rightSeq_mul (b d : BoundedMatrixSequence (fun n ↦ W n)) :
    rightSeq Z W (b * d) = rightSeq Z W b * rightSeq Z W d := by
  have h := joinSeq_mul Z W 0 0 b d
  rw [mul_zero] at h
  exact h

theorem leftSeq_smul (c : ℂ) (a : BoundedMatrixSequence (fun n ↦ Z n)) :
    leftSeq Z W (c • a) = c • leftSeq Z W a := by
  have h := joinSeq_smul Z W c a 0
  rw [smul_zero] at h
  exact h

theorem rightSeq_smul (c : ℂ) (b : BoundedMatrixSequence (fun n ↦ W n)) :
    rightSeq Z W (c • b) = c • rightSeq Z W b := by
  have h := joinSeq_smul Z W c 0 b
  rw [smul_zero] at h
  exact h

theorem leftSeq_star (a : BoundedMatrixSequence (fun n ↦ Z n)) :
    leftSeq Z W (star a) = star (leftSeq Z W a) := by
  have h := joinSeq_star Z W a 0
  rw [star_zero] at h
  exact h

theorem rightSeq_star (b : BoundedMatrixSequence (fun n ↦ W n)) :
    rightSeq Z W (star b) = star (rightSeq Z W b) := by
  have h := joinSeq_star Z W 0 b
  rw [star_zero] at h
  exact h

/-- The left leg of a sequence is null exactly when the sequence is. -/
theorem isNull_leftSeq_iff (l : Filter ℕ)
    (a : BoundedMatrixSequence (fun n ↦ Z n)) :
    IsNullMatrixSequence (fun n ↦ joinModel Z W n) l (leftSeq Z W a) ↔
      IsNullMatrixSequence (fun n ↦ Z n) l a := by
  have h := isNull_joinSeq_iff Z W l a 0
  constructor
  · intro hl
    exact (h.mp hl).1
  · intro ha
    exact h.mpr ⟨ha, IsNullMatrixSequence.zero (fun n ↦ W n) l⟩

/-- The right leg of a sequence is null exactly when the sequence is. -/
theorem isNull_rightSeq_iff (l : Filter ℕ)
    (b : BoundedMatrixSequence (fun n ↦ W n)) :
    IsNullMatrixSequence (fun n ↦ joinModel Z W n) l (rightSeq Z W b) ↔
      IsNullMatrixSequence (fun n ↦ W n) l b := by
  have h := isNull_joinSeq_iff Z W l 0 b
  constructor
  · intro hl
    exact (h.mp hl).2
  · intro hb
    exact h.mpr ⟨IsNullMatrixSequence.zero (fun n ↦ Z n) l, hb⟩

/-! ## The two legs on coronas -/

variable [∀ n, Nonempty (Z n)] [∀ n, Nonempty (W n)]

/-- The left corner map on coronas, defined on a chosen lift. -/
def leftCorona (x : NormMatrixCStarCorona (fun n ↦ Z n)) :
    NormMatrixCStarCorona (fun n ↦ joinModel Z W n) :=
  normMatrixCStarCoronaMk (fun n ↦ joinModel Z W n)
    (leftSeq Z W (MFAlgebraDimension.coronaLift Z x))

/-- The right corner map on coronas, defined on a chosen lift. -/
def rightCorona (y : NormMatrixCStarCorona (fun n ↦ W n)) :
    NormMatrixCStarCorona (fun n ↦ joinModel Z W n) :=
  normMatrixCStarCoronaMk (fun n ↦ joinModel Z W n)
    (rightSeq Z W (MFAlgebraDimension.coronaLift W y))

/-- Two lifts of the same class differ by a null sequence, whose left leg is
null, so the choice of lift does not matter. -/
theorem leftCorona_mk (a : BoundedMatrixSequence (fun n ↦ Z n)) :
    leftCorona Z W (normMatrixCStarCoronaMk (fun n ↦ Z n) a) =
      normMatrixCStarCoronaMk (fun n ↦ joinModel Z W n) (leftSeq Z W a) := by
  have hb : normMatrixCStarCoronaMk (fun n ↦ Z n)
      (MFAlgebraDimension.coronaLift Z
        (normMatrixCStarCoronaMk (fun n ↦ Z n) a))
      = normMatrixCStarCoronaMk (fun n ↦ Z n) a :=
    MFAlgebraDimension.coronaLift_spec Z _
  have hnull : IsNullMatrixSequence (fun n ↦ Z n) cofinite
      (MFAlgebraDimension.coronaLift Z
        (normMatrixCStarCoronaMk (fun n ↦ Z n) a) - a) := by
    rw [← normMatrixCStarCoronaMk_eq_zero_iff, map_sub, hb, sub_self]
  have hnull' : IsNullMatrixSequence (fun n ↦ joinModel Z W n) cofinite
      (leftSeq Z W (MFAlgebraDimension.coronaLift Z
        (normMatrixCStarCoronaMk (fun n ↦ Z n) a)) - leftSeq Z W a) := by
    rw [← leftSeq_sub]
    exact (isNull_leftSeq_iff Z W cofinite _).mpr hnull
  have hzero : normMatrixCStarCoronaMk (fun n ↦ joinModel Z W n)
      (leftSeq Z W (MFAlgebraDimension.coronaLift Z
        (normMatrixCStarCoronaMk (fun n ↦ Z n) a)) - leftSeq Z W a) = 0 :=
    (normMatrixCStarCoronaMk_eq_zero_iff _ _).mpr hnull'
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- The right-hand analogue of `leftCorona_mk`. -/
theorem rightCorona_mk (b : BoundedMatrixSequence (fun n ↦ W n)) :
    rightCorona Z W (normMatrixCStarCoronaMk (fun n ↦ W n) b) =
      normMatrixCStarCoronaMk (fun n ↦ joinModel Z W n) (rightSeq Z W b) := by
  have hb : normMatrixCStarCoronaMk (fun n ↦ W n)
      (MFAlgebraDimension.coronaLift W
        (normMatrixCStarCoronaMk (fun n ↦ W n) b))
      = normMatrixCStarCoronaMk (fun n ↦ W n) b :=
    MFAlgebraDimension.coronaLift_spec W _
  have hnull : IsNullMatrixSequence (fun n ↦ W n) cofinite
      (MFAlgebraDimension.coronaLift W
        (normMatrixCStarCoronaMk (fun n ↦ W n) b) - b) := by
    rw [← normMatrixCStarCoronaMk_eq_zero_iff, map_sub, hb, sub_self]
  have hnull' : IsNullMatrixSequence (fun n ↦ joinModel Z W n) cofinite
      (rightSeq Z W (MFAlgebraDimension.coronaLift W
        (normMatrixCStarCoronaMk (fun n ↦ W n) b)) - rightSeq Z W b) := by
    rw [← rightSeq_sub]
    exact (isNull_rightSeq_iff Z W cofinite _).mpr hnull
  have hzero : normMatrixCStarCoronaMk (fun n ↦ joinModel Z W n)
      (rightSeq Z W (MFAlgebraDimension.coronaLift W
        (normMatrixCStarCoronaMk (fun n ↦ W n) b)) - rightSeq Z W b) = 0 :=
    (normMatrixCStarCoronaMk_eq_zero_iff _ _).mpr hnull'
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- The left corner map on coronas, as a nonunital `⋆`-homomorphism. -/
def leftCoronaHom :
    NormMatrixCStarCorona (fun n ↦ Z n) →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ joinModel Z W n) where
  toFun := leftCorona Z W
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) x
    show leftCorona Z W (c • normMatrixCStarCoronaMk (fun n ↦ Z n) a)
      = c • leftCorona Z W (normMatrixCStarCoronaMk (fun n ↦ Z n) a)
    have hsmul : c • normMatrixCStarCoronaMk (fun n ↦ Z n) a
        = normMatrixCStarCoronaMk (fun n ↦ Z n) (c • a) :=
      (MFAlgebraDimension.normMatrixCStarCoronaMk_smul (fun n ↦ Z n) c a).symm
    rw [hsmul, leftCorona_mk, leftCorona_mk, leftSeq_smul,
      MFAlgebraDimension.normMatrixCStarCoronaMk_smul]
  map_zero' := by
    have h0 : leftCorona Z W (normMatrixCStarCoronaMk (fun n ↦ Z n) 0) = 0 := by
      rw [leftCorona_mk, leftSeq_zero, map_zero]
    rwa [map_zero] at h0
  map_add' x y := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) x
    obtain ⟨c, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) y
    have hsum : normMatrixCStarCoronaMk (fun n ↦ Z n) a
          + normMatrixCStarCoronaMk (fun n ↦ Z n) c
        = normMatrixCStarCoronaMk (fun n ↦ Z n) (a + c) :=
      (map_add (normMatrixCStarCoronaMk (fun n ↦ Z n)) a c).symm
    rw [hsum, leftCorona_mk, leftCorona_mk, leftCorona_mk, leftSeq_add, map_add]
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) x
    obtain ⟨c, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) y
    have hprod : normMatrixCStarCoronaMk (fun n ↦ Z n) a
          * normMatrixCStarCoronaMk (fun n ↦ Z n) c
        = normMatrixCStarCoronaMk (fun n ↦ Z n) (a * c) :=
      (map_mul (normMatrixCStarCoronaMk (fun n ↦ Z n)) a c).symm
    rw [hprod, leftCorona_mk, leftCorona_mk, leftCorona_mk, leftSeq_mul, map_mul]
  map_star' x := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) x
    rw [normMatrixCStarCorona_star_mk, leftCorona_mk, leftCorona_mk,
      leftSeq_star, normMatrixCStarCorona_star_mk]

/-- The right corner map on coronas, as a nonunital `⋆`-homomorphism. -/
def rightCoronaHom :
    NormMatrixCStarCorona (fun n ↦ W n) →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ joinModel Z W n) where
  toFun := rightCorona Z W
  map_smul' c y := by
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) y
    show rightCorona Z W (c • normMatrixCStarCoronaMk (fun n ↦ W n) b)
      = c • rightCorona Z W (normMatrixCStarCoronaMk (fun n ↦ W n) b)
    have hsmul : c • normMatrixCStarCoronaMk (fun n ↦ W n) b
        = normMatrixCStarCoronaMk (fun n ↦ W n) (c • b) :=
      (MFAlgebraDimension.normMatrixCStarCoronaMk_smul (fun n ↦ W n) c b).symm
    rw [hsmul, rightCorona_mk, rightCorona_mk, rightSeq_smul,
      MFAlgebraDimension.normMatrixCStarCoronaMk_smul]
  map_zero' := by
    have h0 : rightCorona Z W (normMatrixCStarCoronaMk (fun n ↦ W n) 0) = 0 := by
      rw [rightCorona_mk, rightSeq_zero, map_zero]
    rwa [map_zero] at h0
  map_add' x y := by
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) x
    obtain ⟨d, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) y
    have hsum : normMatrixCStarCoronaMk (fun n ↦ W n) b
          + normMatrixCStarCoronaMk (fun n ↦ W n) d
        = normMatrixCStarCoronaMk (fun n ↦ W n) (b + d) :=
      (map_add (normMatrixCStarCoronaMk (fun n ↦ W n)) b d).symm
    rw [hsum, rightCorona_mk, rightCorona_mk, rightCorona_mk, rightSeq_add,
      map_add]
  map_mul' x y := by
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) x
    obtain ⟨d, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) y
    have hprod : normMatrixCStarCoronaMk (fun n ↦ W n) b
          * normMatrixCStarCoronaMk (fun n ↦ W n) d
        = normMatrixCStarCoronaMk (fun n ↦ W n) (b * d) :=
      (map_mul (normMatrixCStarCoronaMk (fun n ↦ W n)) b d).symm
    rw [hprod, rightCorona_mk, rightCorona_mk, rightCorona_mk, rightSeq_mul,
      map_mul]
  map_star' y := by
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) y
    rw [normMatrixCStarCorona_star_mk, rightCorona_mk, rightCorona_mk,
      rightSeq_star, normMatrixCStarCorona_star_mk]

@[simp] theorem leftCoronaHom_apply (x : NormMatrixCStarCorona (fun n ↦ Z n)) :
    leftCoronaHom Z W x = leftCorona Z W x := rfl

@[simp] theorem rightCoronaHom_apply (y : NormMatrixCStarCorona (fun n ↦ W n)) :
    rightCoronaHom Z W y = rightCorona Z W y := rfl

/-! ## Faithfulness, orthogonality, complementarity -/

theorem leftCoronaHom_injective : Function.Injective (leftCoronaHom Z W) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) x
  obtain ⟨c, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) y
  rw [leftCoronaHom_apply, leftCoronaHom_apply, leftCorona_mk, leftCorona_mk,
    ← sub_eq_zero, ← map_sub, normMatrixCStarCoronaMk_eq_zero_iff,
    ← leftSeq_sub] at hxy
  rw [← sub_eq_zero, ← map_sub, normMatrixCStarCoronaMk_eq_zero_iff]
  exact (isNull_leftSeq_iff Z W cofinite (a - c)).mp hxy

theorem rightCoronaHom_injective : Function.Injective (rightCoronaHom Z W) := by
  intro x y hxy
  obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) x
  obtain ⟨d, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) y
  rw [rightCoronaHom_apply, rightCoronaHom_apply, rightCorona_mk,
    rightCorona_mk, ← sub_eq_zero, ← map_sub, normMatrixCStarCoronaMk_eq_zero_iff,
    ← rightSeq_sub] at hxy
  rw [← sub_eq_zero, ← map_sub, normMatrixCStarCoronaMk_eq_zero_iff]
  exact (isNull_rightSeq_iff Z W cofinite (b - d)).mp hxy

/-- The left leg is isometric: an injective star homomorphism of C-star
algebras preserves norms. -/
theorem norm_leftCoronaHom (x : NormMatrixCStarCorona (fun n ↦ Z n)) :
    ‖leftCoronaHom Z W x‖ = ‖x‖ :=
  (NonUnitalStarAlgHom.isometry (leftCoronaHom Z W)
    (leftCoronaHom_injective Z W)).norm_map_of_map_zero (map_zero _) x

/-- The right leg is isometric. -/
theorem norm_rightCoronaHom (y : NormMatrixCStarCorona (fun n ↦ W n)) :
    ‖rightCoronaHom Z W y‖ = ‖y‖ :=
  (NonUnitalStarAlgHom.isometry (rightCoronaHom Z W)
    (rightCoronaHom_injective Z W)).norm_map_of_map_zero (map_zero _) y

theorem leftCoronaHom_mul_rightCoronaHom
    (x : NormMatrixCStarCorona (fun n ↦ Z n))
    (y : NormMatrixCStarCorona (fun n ↦ W n)) :
    leftCoronaHom Z W x * rightCoronaHom Z W y = 0 := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) x
  obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) y
  have hz : leftSeq Z W a * rightSeq Z W b = 0 := by
    have h := joinSeq_mul Z W a 0 0 b
    rw [mul_zero, zero_mul, joinSeq_zero] at h
    exact h.symm
  rw [leftCoronaHom_apply, rightCoronaHom_apply, leftCorona_mk, rightCorona_mk,
    ← map_mul, hz, map_zero]

theorem rightCoronaHom_mul_leftCoronaHom
    (x : NormMatrixCStarCorona (fun n ↦ Z n))
    (y : NormMatrixCStarCorona (fun n ↦ W n)) :
    rightCoronaHom Z W y * leftCoronaHom Z W x = 0 := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) x
  obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ W n) y
  have hz : rightSeq Z W b * leftSeq Z W a = 0 := by
    have h := joinSeq_mul Z W 0 a b 0
    rw [zero_mul, mul_zero, joinSeq_zero] at h
    exact h.symm
  rw [leftCoronaHom_apply, rightCoronaHom_apply, leftCorona_mk, rightCorona_mk,
    ← map_mul, hz, map_zero]

/-- The two corners are complementary: their units add up to the unit. -/
theorem leftCoronaHom_one_add_rightCoronaHom_one :
    leftCoronaHom Z W 1 + rightCoronaHom Z W 1 = 1 := by
  have hsum : leftSeq Z W 1 + rightSeq Z W 1 = 1 := by
    have h := joinSeq_add Z W 1 0 0 1
    rw [add_zero, zero_add, joinSeq_one] at h
    exact h.symm
  have hZone : (1 : NormMatrixCStarCorona (fun n ↦ Z n))
      = normMatrixCStarCoronaMk (fun n ↦ Z n) 1 :=
    (map_one (normMatrixCStarCoronaMk (fun n ↦ Z n))).symm
  have hWone : (1 : NormMatrixCStarCorona (fun n ↦ W n))
      = normMatrixCStarCoronaMk (fun n ↦ W n) 1 :=
    (map_one (normMatrixCStarCoronaMk (fun n ↦ W n))).symm
  rw [hZone, hWone, leftCoronaHom_apply, rightCoronaHom_apply, leftCorona_mk,
    rightCorona_mk, ← map_add, hsum, map_one]

/-! ## Domination -/

/-- The image of the unit under the left leg is a projection of norm at most
one. -/
theorem norm_leftCoronaHom_one_le_one : ‖leftCoronaHom Z W 1‖ ≤ 1 := by
  have hstar : star (leftCoronaHom Z W 1) = leftCoronaHom Z W 1 := by
    rw [← map_star, star_one]
  have hidem : leftCoronaHom Z W 1 * leftCoronaHom Z W 1 = leftCoronaHom Z W 1 := by
    rw [← map_mul, one_mul]
  have hcstar : ‖star (leftCoronaHom Z W 1) * leftCoronaHom Z W 1‖
      = ‖leftCoronaHom Z W 1‖ * ‖leftCoronaHom Z W 1‖ :=
    CStarRing.norm_star_mul_self
  rw [hstar, hidem] at hcstar
  nlinarith [norm_nonneg (leftCoronaHom Z W 1), hcstar]

/-- The image of the unit under the right leg is a projection of norm at most
one. -/
theorem norm_rightCoronaHom_one_le_one : ‖rightCoronaHom Z W 1‖ ≤ 1 := by
  have hstar : star (rightCoronaHom Z W 1) = rightCoronaHom Z W 1 := by
    rw [← map_star, star_one]
  have hidem :
      rightCoronaHom Z W 1 * rightCoronaHom Z W 1 = rightCoronaHom Z W 1 := by
    rw [← map_mul, one_mul]
  have hcstar : ‖star (rightCoronaHom Z W 1) * rightCoronaHom Z W 1‖
      = ‖rightCoronaHom Z W 1‖ * ‖rightCoronaHom Z W 1‖ :=
    CStarRing.norm_star_mul_self
  rw [hstar, hidem] at hcstar
  nlinarith [norm_nonneg (rightCoronaHom Z W 1), hcstar]

/-- **The join dominates its left leg.**  Compressing by the left unit kills
the right summand and returns the left one. -/
theorem norm_le_norm_join_left (x : NormMatrixCStarCorona (fun n ↦ Z n))
    (y : NormMatrixCStarCorona (fun n ↦ W n)) :
    ‖x‖ ≤ ‖leftCoronaHom Z W x + rightCoronaHom Z W y‖ := by
  have hcompress :
      leftCoronaHom Z W 1 *
          (leftCoronaHom Z W x + rightCoronaHom Z W y) *
        leftCoronaHom Z W 1 = leftCoronaHom Z W x := by
    have h1 : leftCoronaHom Z W 1 * leftCoronaHom Z W x * leftCoronaHom Z W 1
        = leftCoronaHom Z W x := by
      rw [← map_mul, ← map_mul, one_mul, mul_one]
    have h2 : leftCoronaHom Z W 1 * rightCoronaHom Z W y * leftCoronaHom Z W 1
        = 0 := by
      rw [leftCoronaHom_mul_rightCoronaHom, zero_mul]
    rw [mul_add, add_mul, h1, h2, add_zero]
  have hbound : ‖leftCoronaHom Z W x‖ ≤
      ‖leftCoronaHom Z W x + rightCoronaHom Z W y‖ := by
    rw [← hcompress]
    have h1 : ‖leftCoronaHom Z W 1 *
          (leftCoronaHom Z W x + rightCoronaHom Z W y) *
        leftCoronaHom Z W 1‖ ≤
        ‖leftCoronaHom Z W 1 *
          (leftCoronaHom Z W x + rightCoronaHom Z W y)‖ *
          ‖leftCoronaHom Z W 1‖ := norm_mul_le _ _
    have h2 : ‖leftCoronaHom Z W 1 *
          (leftCoronaHom Z W x + rightCoronaHom Z W y)‖ ≤
        ‖leftCoronaHom Z W 1‖ *
          ‖leftCoronaHom Z W x + rightCoronaHom Z W y‖ := norm_mul_le _ _
    nlinarith [norm_leftCoronaHom_one_le_one Z W,
      norm_nonneg (leftCoronaHom Z W 1),
      norm_nonneg (leftCoronaHom Z W x + rightCoronaHom Z W y),
      norm_nonneg (leftCoronaHom Z W 1 *
        (leftCoronaHom Z W x + rightCoronaHom Z W y)), h1, h2]
  rw [← norm_leftCoronaHom Z W x]
  exact hbound

/-- **The join dominates its right leg.** -/
theorem norm_le_norm_join_right (x : NormMatrixCStarCorona (fun n ↦ Z n))
    (y : NormMatrixCStarCorona (fun n ↦ W n)) :
    ‖y‖ ≤ ‖leftCoronaHom Z W x + rightCoronaHom Z W y‖ := by
  have hcompress :
      rightCoronaHom Z W 1 *
          (leftCoronaHom Z W x + rightCoronaHom Z W y) *
        rightCoronaHom Z W 1 = rightCoronaHom Z W y := by
    have h1 : rightCoronaHom Z W 1 * rightCoronaHom Z W y * rightCoronaHom Z W 1
        = rightCoronaHom Z W y := by
      rw [← map_mul, ← map_mul, one_mul, mul_one]
    have h2 : rightCoronaHom Z W 1 * leftCoronaHom Z W x * rightCoronaHom Z W 1
        = 0 := by
      rw [rightCoronaHom_mul_leftCoronaHom, zero_mul]
    rw [mul_add, add_mul, h1, h2, zero_add]
  have hbound : ‖rightCoronaHom Z W y‖ ≤
      ‖leftCoronaHom Z W x + rightCoronaHom Z W y‖ := by
    rw [← hcompress]
    have h1 : ‖rightCoronaHom Z W 1 *
          (leftCoronaHom Z W x + rightCoronaHom Z W y) *
        rightCoronaHom Z W 1‖ ≤
        ‖rightCoronaHom Z W 1 *
          (leftCoronaHom Z W x + rightCoronaHom Z W y)‖ *
          ‖rightCoronaHom Z W 1‖ := norm_mul_le _ _
    have h2 : ‖rightCoronaHom Z W 1 *
          (leftCoronaHom Z W x + rightCoronaHom Z W y)‖ ≤
        ‖rightCoronaHom Z W 1‖ *
          ‖leftCoronaHom Z W x + rightCoronaHom Z W y‖ := norm_mul_le _ _
    nlinarith [norm_rightCoronaHom_one_le_one Z W,
      norm_nonneg (rightCoronaHom Z W 1),
      norm_nonneg (leftCoronaHom Z W x + rightCoronaHom Z W y),
      norm_nonneg (rightCoronaHom Z W 1 *
        (leftCoronaHom Z W x + rightCoronaHom Z W y)), h1, h2]
  rw [← norm_rightCoronaHom Z W y]
  exact hbound

end

/-! ## The packaged statement -/

noncomputable section

/-- **Two norm coronas are complementary corners of one norm corona.**  The
joined model sequence is the coordinatewise block sum; the two legs are
isometric, orthogonal in either order, complementary at the unit, and the join
dominates each leg in norm. -/
theorem exists_complementary_corona_join
    (Z W : ℕ → FiniteModel) (hZ : ∀ n, Nonempty (Z n))
    (hW : ∀ n, Nonempty (W n)) :
    ∃ V : ℕ → FiniteModel, ∃ hV : ∀ n, Nonempty (V n),
      letI : ∀ n, Nonempty (V n) := hV
      letI : ∀ n, Nonempty (Z n) := hZ
      letI : ∀ n, Nonempty (W n) := hW
      ∃ jZ : NormMatrixCStarCorona (fun n ↦ Z n) →⋆ₙₐ[ℂ]
          NormMatrixCStarCorona (fun n ↦ V n),
        ∃ jW : NormMatrixCStarCorona (fun n ↦ W n) →⋆ₙₐ[ℂ]
            NormMatrixCStarCorona (fun n ↦ V n),
          (∀ a, ‖jZ a‖ = ‖a‖) ∧ (∀ b, ‖jW b‖ = ‖b‖) ∧
            Function.Injective jZ ∧ Function.Injective jW ∧
              (∀ a b, jZ a * jW b = 0) ∧ (∀ a b, jW b * jZ a = 0) ∧
                jZ 1 + jW 1 = 1 ∧
                  (∀ a b, ‖a‖ ≤ ‖jZ a + jW b‖) ∧
                    (∀ a b, ‖b‖ ≤ ‖jZ a + jW b‖) := by
  letI : ∀ n, Nonempty (Z n) := hZ
  letI : ∀ n, Nonempty (W n) := hW
  refine ⟨joinModel Z W, fun n ↦ nonempty_joinModel Z W hZ n, ?_⟩
  refine ⟨leftCoronaHom Z W, rightCoronaHom Z W, norm_leftCoronaHom Z W,
    norm_rightCoronaHom Z W, leftCoronaHom_injective Z W,
    rightCoronaHom_injective Z W, leftCoronaHom_mul_rightCoronaHom Z W,
    fun a b ↦ rightCoronaHom_mul_leftCoronaHom Z W a b,
    leftCoronaHom_one_add_rightCoronaHom_one Z W,
    norm_le_norm_join_left Z W, norm_le_norm_join_right Z W⟩

end

end ShulmanFillCoronaJoin
end GroupApproximation
