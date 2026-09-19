import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import GroupApproximation.Analysis.MatrixCoronaDedekindFinite

/-!
# Order comparison of equivalent projections in a norm matrix corona

`non_mf_groups_exist.tex`, Lemma `lem:stable-finite`:

> For every sequence `(m_n)`, the norm matrix corona
> `∏_n M_{m_n}(ℂ) / ⊕_n M_{m_n}(ℂ)` is stably finite.  Consequently, unitarily
> equivalent projections in a norm matrix corona are equal whenever one is
> dominated by the other.

and, from its proof, the abstract half:

> If `A` is a stably finite unital C-star algebra, equivalent projections
> `p ≤ q` satisfy `p = q`: if `w*w = q` and `ww* = p`, then `w ∈ qAq` is an
> isometry in the corner.  The corner is finite because `w + (1 - q)` is an
> isometry in `A`.  Consequently `ww* = q`, and hence `p = q`.

## What was already in the repository, and what this file adds

Half (i) — stable finiteness of the corona itself — is already proved, by
`MatrixCoronaFinite.mul_eq_one_symm_matrixCorona`: a one-sided inverse in
`Matrix I I (NormMatrixCStarCorona X)` is two-sided, proved there by assembling
lifts into an amplified coordinate matrix and running KT.06's Neumann
correction at the index `I × X n`.  Specialized to `I = Fin k` this is exactly
the manuscript's "every matrix amplification of the corona is finite".  Nothing
has to be added for half (i); it is re-exported below only so that the
manuscript lemma can be stated as a single proposition.

It is worth recording why the corona is *not* routed through
`MatrixCoronaFinite.mfAlgebra_isStablyFinite`, "every MF algebra is stably
finite", even though the corona is MF.  The witness
`normMatrixCStarCorona_hasMFEmbedding` carries two side conditions on the
coordinate sizes — `∀ n, 0 < Fintype.card (X n)` and
`StrictMono (fun n ↦ Fintype.card (X n))` — which the manuscript's "for every
sequence `(m_n)`" does not impose.  Going through the direct route keeps the
statement for *every* sequence, which is the printed one.

Half (ii) is where this file does work.  The repository already had
`eq_of_murrayVonNeumannEquiv_of_absorbs`, which proves the same conclusion but
carries a *C-star* hypothesis

> `hproper : ∀ x, star x * x = 0 → x = 0`

used at exactly two steps, to derive the manuscript's two range statements
`w = wq` and `w = pw`.  Its module docstring records the resulting question as
open: "Whether the generic statement nevertheless holds in a bare star ring is
not settled here; no counterexample is claimed."

**It does hold in a bare star ring**, and `eq_of_isometryPair_of_absorbs`
below proves it.  The observation is that one never needs `w` itself to sit in
the corner: the *corrected* element

  `u := w * q`

satisfies the same two defining identities `u*u = q` and `uu* = p`, and it lies
in `qAq` for purely algebraic reasons.  The single computation that makes this
work is

  `w * q = w * (w* w) = (w w*) * w = p * w`   (`mul_right_eq_left_mul_of_isometryPair`),

after which `u q = u` is idempotence of `q` and `q u = q p w = p w = u` is the
containment `qp = p`.  So the corner-membership obligation the manuscript
discharges analytically is discharged here by replacing `w`, and the C-star
input disappears.  The remaining `σ = u + (1 - q)` computation is not repeated:
it is `MFStablyFinite.mul_star_eq_of_corner_isometry`, already factored out as
a star-ring lemma.

For fidelity to the printed proof, the genuine corner membership
`q w q = w` *is* also proved, as `cstar_corner_eq_of_isometryPair`; that one
does consume the C-star identity, through `CStarRing.star_mul_self_eq_zero_iff`,
exactly as the printed argument does.  It is not used by anything below.

## What is proved

* `mul_right_eq_left_mul_of_isometryPair` — the corner-correction identity.
* `eq_of_isometryPair_of_absorbs` — half (ii) in a bare star ring, with the
  containment in its ring form `q * p = p`.
* `eq_of_isometryPair_of_le` — the same with the genuine C-star order `p ≤ q`,
  converted by Mathlib's `IsStarProjection.le_iff_mul_eq_right`.
* `eq_of_murrayVonNeumannEquiv_of_absorbs_of_finite` — the same statement in
  the repository's Murray--von Neumann vocabulary, strictly stronger than
  `eq_of_murrayVonNeumannEquiv_of_absorbs` (no `hproper`).
* `normMatrixCStarCorona_eq_of_isometryPair` and
  `matrixNormMatrixCStarCorona_eq_of_isometryPair` — the corona and its
  amplifications, with finiteness supplied by KT.06 and by
  `MatrixCoronaFinite.mul_eq_one_symm_matrixCorona`.
* `Manuscript.OneSidedMFRadical.manuscriptStableFinite` — `lem:stable-finite`
  whole, as one closed proposition.

## The containment hypothesis

`p ≤ q` is carried in the ring form `q * p = p` everywhere except
`eq_of_isometryPair_of_le`.  Two reasons: it is the form the algebra consumes,
and it keeps the corona statements free of the `[PartialOrder]`
`[StarOrderedRing]` side instances, which for a C-star algebra are supplied by
`CStarAlgebra.spectralOrder` rather than found by instance search.  Only
`q * p = p` is ever used; the mirrored `p * q = p` is its star and is never
needed.
-/

namespace GroupApproximation

/-! ## The corner correction -/

section StarRing

variable {A : Type*} [Ring A] [StarRing A]

/-- **The corner-correction identity.**  If `w` implements an equivalence of
`q` with `p` — `w*w = q` and `ww* = p` — then `w q = p w`.

This is the whole of the extra content needed to run the manuscript's corner
argument without any C-star input: it says that the corrected element `w q`,
which manifestly absorbs `q` on the right, also absorbs `q` on the left as soon
as `q` dominates `p`. -/
theorem mul_right_eq_left_mul_of_isometryPair {p q w : A}
    (hw₁ : star w * w = q) (hw₂ : w * star w = p) :
    w * q = p * w := by
  rw [← hw₁, ← mul_assoc, hw₂]

/-- The corrected element `w q` is an isometry of the corner cut by `q`. -/
theorem star_mul_self_mul_right_of_isometryPair {q w : A}
    (hq : IsStarProjection q) (hw₁ : star w * w = q) :
    star (w * q) * (w * q) = q := by
  have hstar : star (w * q) = q * star w := by
    rw [star_mul, hq.isSelfAdjoint.star_eq]
  rw [hstar]
  calc q * star w * (w * q) = q * (star w * w) * q := by noncomm_ring
    _ = q * q * q := by rw [hw₁]
    _ = q := by rw [hq.isIdempotentElem.eq, hq.isIdempotentElem.eq]

/-- The corrected element `w q` has the same range projection `p` as `w`. -/
theorem mul_right_mul_star_of_isometryPair {p q w : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hw₁ : star w * w = q) (hw₂ : w * star w = p) :
    w * q * star (w * q) = p := by
  have hstar : star (w * q) = q * star w := by
    rw [star_mul, hq.isSelfAdjoint.star_eq]
  have hswap : w * q = p * w :=
    mul_right_eq_left_mul_of_isometryPair hw₁ hw₂
  rw [hstar]
  calc w * q * (q * star w) = w * (q * q) * star w := by noncomm_ring
    _ = w * q * star w := by rw [hq.isIdempotentElem.eq]
    _ = p * w * star w := by rw [hswap]
    _ = p * (w * star w) := by noncomm_ring
    _ = p * p := by rw [hw₂]
    _ = p := hp.isIdempotentElem.eq

/-! ## Half (ii): comparison of equivalent projections -/

/-- **Equivalent projections `p ≤ q` in a finite ring are equal.**

The manuscript's sentence

> if `w*w = q` and `ww* = p`, then `w ∈ qAq` is an isometry in the corner.  The
> corner is finite because `w + (1 - q)` is an isometry in `A`.  Consequently
> `ww* = q`, and hence `p = q`.

Finiteness enters in the manuscript's own words, as
`hfinite : ∀ x, star x * x = 1 → x * star x = 1`, which is also the shape
`Analysis/MatrixCoronaDedekindFinite.lean` consumes.  The containment `p ≤ q`
is in its ring form `q * p = p`.

**No C-star input is used.**  The printed proof puts `w` in the corner `qAq`
by a range argument, which formally costs `x*x = 0 → x = 0`.  That obligation
is avoided here by running the `σ`-computation on the corrected element
`w q` instead of on `w`: it satisfies the same two identities
(`star_mul_self_mul_right_of_isometryPair`,
`mul_right_mul_star_of_isometryPair`) and sits in the corner by
`mul_right_eq_left_mul_of_isometryPair` together with `q p = p`.  The genuine
corner membership of `w` itself is `cstar_corner_eq_of_isometryPair` below and
is not needed.

This is therefore strictly stronger than
`eq_of_murrayVonNeumannEquiv_of_absorbs`, whose `hproper` hypothesis it
removes. -/
theorem eq_of_isometryPair_of_absorbs
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {p q w : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q * p = p) (hw₁ : star w * w = q) (hw₂ : w * star w = p) :
    p = q := by
  have hswap : w * q = p * w :=
    mul_right_eq_left_mul_of_isometryPair hw₁ hw₂
  -- the corrected element absorbs `q` on both sides
  have hvq : w * q * q = w * q := by
    rw [mul_assoc, hq.isIdempotentElem.eq]
  have hqv : q * (w * q) = w * q := by
    rw [hswap, ← mul_assoc, hqp]
  have hiso : star (w * q) * (w * q) = q :=
    star_mul_self_mul_right_of_isometryPair hq hw₁
  have hrange : w * q * star (w * q) = p :=
    mul_right_mul_star_of_isometryPair hp hq hw₁ hw₂
  have hmain : w * q * star (w * q) = q :=
    mul_star_eq_of_corner_isometry hfinite hq hqv hvq hiso
  rw [hrange] at hmain
  exact hmain

/-- **Half (ii) in the repository's Murray--von Neumann vocabulary.**

`MurrayVonNeumannEquiv p q` supplies `v` with `v*v = p` and `vv* = q`; the
manuscript's `w` is `v*`, which is why the proof opens `hmvn.symm`.  This is
`eq_of_murrayVonNeumannEquiv_of_absorbs` with its C-star hypothesis
`hproper` deleted rather than discharged. -/
theorem eq_of_murrayVonNeumannEquiv_of_absorbs_of_finite
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hqp : q * p = p) (hmvn : MurrayVonNeumannEquiv p q) :
    p = q := by
  obtain ⟨w, hw₁, hw₂⟩ := hmvn.symm
  exact eq_of_isometryPair_of_absorbs hfinite hp hq hqp hw₁ hw₂

end StarRing

/-! ## The printed corner membership

The two statements below are the printed proof's own route.  They are recorded
for fidelity and are used by nothing above. -/

section CornerMembership

variable {A : Type*} [CStarAlgebra A]

/-- **`w ∈ qAq`, the manuscript's corner membership, proved as printed.**

Unlike everything in the previous section this consumes the C-star identity, in
the form `CStarRing.star_mul_self_eq_zero_iff`, which is what turns the printed
range statements into algebra:

* `w = w q` because `(w - wq)*(w - wq) = q - q - q + q = 0`;
* `w = p w` follows from `w q = p w` and the previous identity;
* `q w = q p w = p w = w` is the only use of the containment `q p = p`.

The point of stating it is that `eq_of_isometryPair_of_absorbs` does *not* need
it. -/
theorem cstar_corner_eq_of_isometryPair {p q w : A}
    (hq : IsStarProjection q) (hqp : q * p = p)
    (hw₁ : star w * w = q) (hw₂ : w * star w = p) :
    q * w * q = w := by
  have hproper : ∀ x : A, star x * x = 0 → x = 0 := fun x hx ↦
    (CStarRing.star_mul_self_eq_zero_iff x).mp hx
  have hstarx : star (w - w * q) = star w - q * star w := by
    rw [star_sub, star_mul, hq.isSelfAdjoint.star_eq]
  have hzero : star (w - w * q) * (w - w * q) = 0 := by
    rw [hstarx]
    calc (star w - q * star w) * (w - w * q)
        = star w * w - star w * w * q - q * (star w * w)
            + q * (star w * w) * q := by noncomm_ring
      _ = q - q * q - q * q + q * q * q := by rw [hw₁]
      _ = q - q - q + q := by
            rw [hq.isIdempotentElem.eq, hq.isIdempotentElem.eq]
      _ = 0 := by abel
  have hwq : w * q = w := (sub_eq_zero.mp (hproper _ hzero)).symm
  have hswap : w * q = p * w :=
    mul_right_eq_left_mul_of_isometryPair hw₁ hw₂
  have hpw : p * w = w := by rw [← hswap, hwq]
  have hqw : q * w = w := by
    calc q * w = q * (p * w) := by rw [hpw]
      _ = q * p * w := by rw [← mul_assoc]
      _ = p * w := by rw [hqp]
      _ = w := hpw
  rw [hqw, hwq]

end CornerMembership

/-! ## The genuine order relation -/

section Order

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Half (ii) with the genuine C-star order.**  Let `A` be a finite unital
C-star algebra and let `p, q` be projections with `p ≤ q`, `w*w = q` and
`ww* = p`.  Then `p = q`.

The passage from `p ≤ q` to the ring form `q p = p` is Mathlib's
`IsStarProjection.le_iff_mul_eq_right`.  The order instances are side inputs,
as everywhere in Mathlib's C-star order API; for a concrete algebra they are
installed by `CStarAlgebra.spectralOrder` and `CStarAlgebra.spectralOrderedRing`.
Note that the underlying argument (`eq_of_isometryPair_of_absorbs`) uses no
C-star structure at all; the C-star algebra appears here only because the order
does. -/
theorem eq_of_isometryPair_of_le
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {p q w : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hle : p ≤ q) (hw₁ : star w * w = q) (hw₂ : w * star w = p) :
    p = q :=
  eq_of_isometryPair_of_absorbs hfinite hp hq
    ((hp.le_iff_mul_eq_right hq).mp hle) hw₁ hw₂

end Order

/-! ## The norm matrix corona -/

section Corona

/-- **Half (ii) in the norm matrix corona.**  Finiteness is KT.06,
`normMatrixCStarCorona_isDedekindFiniteMonoid`: Dedekind finiteness is formally
stronger than the manuscript's "every isometry is unitary", so it discharges
`hfinite` directly. -/
theorem normMatrixCStarCorona_eq_of_isometryPair (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)]
    {p q w : NormMatrixCStarCorona (fun n ↦ X n)}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q * p = p)
    (hw₁ : star w * w = q) (hw₂ : w * star w = p) :
    p = q :=
  eq_of_isometryPair_of_absorbs (fun _ hx ↦ mul_eq_one_symm hx) hp hq hqp
    hw₁ hw₂

/-- **Half (ii) in every matrix amplification of the norm matrix corona.**
This is the statement the manuscript's word *stably* asks for: the same
comparison holds in `M_I(Q_X)`, with finiteness supplied by
`MatrixCoronaFinite.mul_eq_one_symm_matrixCorona`.

The bare-star-ring form of `eq_of_isometryPair_of_absorbs` is what makes this
available: `Matrix I I (NormMatrixCStarCorona X)` is a star ring, and the
repository does not equip it with a C-star norm, so a proof routed through the
C-star identity would not apply here. -/
theorem matrixNormMatrixCStarCorona_eq_of_isometryPair {I : Type} [Fintype I]
    [DecidableEq I] (hI : Nonempty I) (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)]
    {p q w : Matrix I I (NormMatrixCStarCorona (fun n ↦ X n))}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqp : q * p = p)
    (hw₁ : star w * w = q) (hw₂ : w * star w = p) :
    p = q :=
  eq_of_isometryPair_of_absorbs
    (fun _ hx ↦ MatrixCoronaFinite.mul_eq_one_symm_matrixCorona hI X hx) hp hq
    hqp hw₁ hw₂

end Corona

/-! ## The manuscript lemma -/

namespace Manuscript
namespace OneSidedMFRadical

/-- **Lemma `lem:stable-finite`, as one closed proposition.**

Positive matrix sizes are represented by `Fin k` with `0 < k`; the manuscript's
`(m_n)` is a sequence of finite nonempty models.  The three clauses are, in the
printed order:

1. every norm matrix corona is stably finite — every isometry of `M_k` of it is
   a unitary, for every `k ≥ 1`;
2. the consequence in the corona: unitarily equivalent projections are equal
   whenever one is dominated by the other, with the domination `p ≤ q` written
   in its ring form `q p = p` and the equivalence written by its implementer
   `w`, `w*w = q` and `ww* = p`;
3. the same consequence in every matrix amplification, which is what clause 1
   is for.

Clause 2 is stated with `w` explicit rather than existentially quantified
because that is the printed formulation; the existential form is
`eq_of_murrayVonNeumannEquiv_of_absorbs_of_finite`. -/
def NormMatrixCoronaStableFiniteOrder : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)],
    (∀ k : ℕ, 0 < k →
        ∀ v : Matrix (Fin k) (Fin k) (NormMatrixCStarCorona (fun n ↦ X n)),
          star v * v = 1 → v * star v = 1) ∧
      (∀ p q w : NormMatrixCStarCorona (fun n ↦ X n),
          IsStarProjection p → IsStarProjection q → q * p = p →
          star w * w = q → w * star w = p → p = q) ∧
      (∀ k : ℕ, 0 < k →
        ∀ p q w : Matrix (Fin k) (Fin k) (NormMatrixCStarCorona (fun n ↦ X n)),
          IsStarProjection p → IsStarProjection q → q * p = p →
          star w * w = q → w * star w = p → p = q)

/-- Closed proof of `lem:stable-finite`. -/
theorem manuscriptStableFinite : NormMatrixCoronaStableFiniteOrder := by
  intro X _
  refine ⟨?_, ?_, ?_⟩
  · intro k hk v hv
    exact MatrixCoronaFinite.mul_eq_one_symm_matrixCorona ⟨⟨0, hk⟩⟩ X hv
  · intro p q w hp hq hqp hw₁ hw₂
    exact normMatrixCStarCorona_eq_of_isometryPair X hp hq hqp hw₁ hw₂
  · intro k hk p q w hp hq hqp hw₁ hw₂
    exact matrixNormMatrixCStarCorona_eq_of_isometryPair ⟨⟨0, hk⟩⟩ X hp hq hqp
      hw₁ hw₂

end OneSidedMFRadical
end Manuscript

end GroupApproximation
