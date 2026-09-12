import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerCoronaEmbedding
import GroupApproximation.Manuscript.OneSidedMFRadical.RetainedCoronaHom

/-!
# The corner-corona class of the printed `W_n(g)` is `q Θ(g) q`

`non_mf_groups_exist.tex`, printed proof of `thm:normal-kazhdan`, defines

    `b = |S|⁻¹ ∑_{s∈S} (q Θ(s) q - q)^* (q Θ(s) q - q)`

from the *ambient* corona representation `Θ` compressed by the projection `q`,
and two displays later asserts that the coordinate elements

    `b_n = |S|⁻¹ ∑_{s∈S} (W_n(s) - q_n)^* (W_n(s) - q_n)`

*represent* `b`.  `Manuscript/OneSidedMFRadical/PartialClosureAnalysisTwo.lean`
attaches to that sentence the identity

    `[ (b_n) ]  =  ∑_{s∈S} ([W_·(s)] - 1)^* ([W_·(s)] - 1)`

in the **corner** corona, and records, verbatim, that the further step

    `[ W_·(s) ]  =  q Θ(s) q`

"is not proved here and is not in the tree".  This file proves it.

## What has to be said, and in which algebra

The two sides do not literally live in one algebra, and the printed sentence
does not pretend otherwise: `[W_·(s)]` is a class in the corona over the
*corner* models `q_n M_{d_n}(ℂ) q_n`, while `q Θ(s) q` is an element of the
ambient corona.  The printed identification `q_n M_{d_n}(ℂ) q_n ≅ M_{r_n}(ℂ)`
is what relates them, and `CorrectedCornerCoronaEmbedding.lean` already has it
at the level of coronas: `correctedCornerCoronaEmbedHom D l` is the induced
**injective** nonunital `⋆`-homomorphism from the corner corona to the ambient
corona over the retained coordinates.  The statement proved here is therefore

    `ι [ W_·(s) ]  =  q Θ(s) q`     (`ι` the corner-corona embedding),

together with the two facts that make it a statement *about the corner*:

* `ι` is injective (`correctedCornerCoronaEmbedHom_injective`), so the equation
  determines `[W_·(s)]`;
* `ι 1 = q`, i.e. `ι` carries the unit of the corner corona to the printed
  projection `q`;
* the range of `ι` is exactly `{x | q x q = x}`, the corner `q 𝒬 q` of the
  retained ambient corona.

The last two together say that `ι` is an isomorphism of the corner corona onto
the printed corner, so the displayed equation is an equation *of corner
classes* and not merely of their images.

"After passing to a subsequence" and "along the ultrafilter" are the two
coordinate passages the printed proof makes; both are already homomorphisms in
this repository, and their composite is `retainedCoronaToOmega`, which is where
the printed `q Θ(s) q` is read.

## The proof, in one line each

* `manuscriptCornerCoronaClass` (Lemma `lem:central-corona-corner`, composed)
  gives `[k ↦ cornerEmbed (W_k g)] = q ρ(g)` in the retained corona.  That is
  the *ambient* class equation, and it is one of the two halves the audit
  found.
* `cornerEmbed_cornerCut`: an embedded corner matrix is unchanged by cutting
  with `q_n` on both sides.  Hence the class of `(cornerEmbed (W_k g))` is
  unchanged by cutting with the class of `(q_k)`, which is `q`.  Combining,
  `q ρ(g) = q (q ρ(g)) q = q ρ(g) q`, so the ambient class equation *is* the
  printed `q Θ(g) q` with no centrality of `q` used at this step.
* `cornerEmbed_one`: `cornerEmbed q_n 1 = q_n`, which is `ι 1 = q`.

## What is not claimed

Nothing here derives the printed *order* inequality `b ≥ (κ²/|S|) q`, nor the
absence of `K`-fixed vectors in the corner.  Those are separate printed
sentences with their own declarations; this file supplies only the
identification of the corner class, which those sentences had been quantified
over rather than connected to.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open KazhdanCornerMatrices
open PrintedCornerCompression
open CoronaProjectionLifting
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## The corner embedding lands exactly in the corner -/

section Coordinates

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {q : Matrix Y Y ℂ}

omit [Fintype Y] in
/-- The principal block of a coordinate projection on its own coordinates is
the identity. -/
theorem principalBlock_coordinateProjection (p : Y → Prop) [DecidablePred p] :
    principalBlock p (coordinateProjection p)
      = (1 : Matrix {i : Y // p i} {i : Y // p i} ℂ) := by
  ext i j
  show coordinateProjection p (i : Y) (j : Y)
      = (1 : Matrix {i : Y // p i} {i : Y // p i} ℂ) i j
  rw [coordinateProjection, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [i.2]
  · have h' : (i : Y) ≠ (j : Y) := fun hc ↦ h (Subtype.ext hc)
    simp [h, h']

/-- **The corner embedding is a section of the corner compression.**
Compressing an embedded corner matrix returns it unchanged, because the
eigenbasis conjugations cancel and a principal block of a zero extension is the
original block. -/
theorem cornerCompression_cornerEmbed (hq : q.IsHermitian)
    (C : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    cornerCompression hq (cornerEmbed hq C) = C := by
  have hconj : eigenbasisConj hq (cornerEmbed hq C)
      = blockExtend (cornerPredicate hq) C := by
    rw [eigenbasisConj, cornerEmbed,
      show (eigenUnitary hq)ᴴ *
            (eigenUnitary hq * blockExtend (cornerPredicate hq) C *
              (eigenUnitary hq)ᴴ) * eigenUnitary hq
          = ((eigenUnitary hq)ᴴ * eigenUnitary hq) *
              blockExtend (cornerPredicate hq) C *
              ((eigenUnitary hq)ᴴ * eigenUnitary hq) by noncomm_ring,
      eigenUnitary_conjTranspose_mul, Matrix.one_mul, Matrix.mul_one]
  rw [cornerCompression, hconj, principalBlock_blockExtend]

/-- **An embedded corner matrix is its own two-sided cut by `q`.**  This is the
statement that `cornerEmbed` really lands in `q M q`, and it is what makes the
printed `q Θ(g) q` and the ambient class `q Θ(g)` the same element. -/
theorem cornerEmbed_cornerCut (hq : q.IsHermitian) (hidem : q * q = q)
    (C : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    q * cornerEmbed hq C * q = cornerEmbed hq C := by
  have h := cornerEmbed_cornerCompression hq hidem (cornerEmbed hq C)
  rw [cornerCompression_cornerEmbed] at h
  exact h.symm

/-- The compression of a Hermitian idempotent to its own corner is the corner
identity. -/
theorem cornerCompression_self (hq : q.IsHermitian) (hidem : q * q = q) :
    cornerCompression hq q = 1 := by
  rw [cornerCompression, eigenbasisConj_eq_coordinateProjection hq hidem,
    principalBlock_coordinateProjection]

/-- **The corner embedding carries the corner identity to `q`.** -/
theorem cornerEmbed_one (hq : q.IsHermitian) (hidem : q * q = q) :
    cornerEmbed hq 1 = q := by
  have h := cornerEmbed_cornerCompression hq hidem q
  rw [cornerCompression_self hq hidem] at h
  rw [h, hidem, hidem]

end Coordinates

/-! ## The same three facts, for sequences -/

section Sequences

variable {H : Type*} [Group H] {model : ℕ → FiniteModel}

/-- The printed projections `q_n`, as one bounded sequence: the image under the
coordinate corner inclusion of the unit of the corner numerator algebra. -/
def cornerUnitSequence (D : PrintedCornerData H model) :
    BoundedMatrixSequence (fun n ↦ model n) :=
  cornerEmbedSequence D 1

theorem cornerEmbedSequence_one (D : PrintedCornerData H model) :
    cornerEmbedSequence D 1 = cornerUnitSequence D := rfl

@[simp] theorem cornerUnitSequence_apply (D : PrintedCornerData H model)
    (n : ℕ) : cornerUnitSequence D n = D.q n := by
  change cornerEmbed (D.qHermitian n)
      (1 : Matrix (D.cornerModel n) (D.cornerModel n) ℂ) = D.q n
  exact cornerEmbed_one (D.qHermitian n) (D.qIdem n)

/-- The coordinate corner inclusion carries the printed `(W_n(g))` to the
printed `(q_n V_n(g) q_n)`-corrected ambient corner sequence. -/
theorem cornerEmbedSequence_correctedCornerMapSequence
    (D : PrintedCornerData H model) (g : H) :
    cornerEmbedSequence D (correctedCornerMapSequence D g)
      = ambientCornerSeq D g := by
  refine lp.ext (funext fun n ↦ ?_)
  rfl

/-- The coordinatewise compression to the corner, as a bounded sequence.  This
is the inverse direction of `cornerEmbedSequence` on the corner. -/
def cornerCompressSequence (D : PrintedCornerData H model)
    (a : BoundedMatrixSequence (fun n ↦ model n)) :
    BoundedMatrixSequence (fun n ↦ D.cornerModel n) :=
  ⟨fun n ↦ cornerCompression (D.qHermitian n) (a n), memℓp_infty ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    letI : Nonempty (model n) := D.model_nonempty n
    change ‖cornerCompression (D.qHermitian n) (a n)‖ ≤ ‖a‖
    exact (norm_cornerCompression_le (D.qHermitian n) (a n)).trans
      (boundedMatrixSequence_coord_norm_le (fun n ↦ model n) a n)⟩⟩

/-- **The corner embedding of a compression is the two-sided cut.**  This is
the surjectivity half of the printed identification of the corner. -/
theorem cornerEmbedSequence_cornerCompressSequence
    (D : PrintedCornerData H model)
    (a : BoundedMatrixSequence (fun n ↦ model n)) :
    cornerEmbedSequence D (cornerCompressSequence D a)
      = cornerUnitSequence D * a * cornerUnitSequence D := by
  refine lp.ext (funext fun n ↦ ?_)
  have hmul : ((cornerUnitSequence D * a * cornerUnitSequence D :
        BoundedMatrixSequence (fun n ↦ model n)) :
        ∀ n, Matrix (model n) (model n) ℂ) n
      = cornerUnitSequence D n * a n * cornerUnitSequence D n := rfl
  rw [hmul, cornerUnitSequence_apply]
  exact cornerEmbed_cornerCompression (D.qHermitian n) (D.qIdem n) (a n)

/-- **The embedded corner sequence is its own two-sided cut by `(q_n)`.** -/
theorem cornerUnitSequence_mul_ambientCornerSeq_mul
    (D : PrintedCornerData H model) (g : H) :
    cornerUnitSequence D * ambientCornerSeq D g * cornerUnitSequence D
      = ambientCornerSeq D g := by
  refine lp.ext (funext fun n ↦ ?_)
  have hmul : ((cornerUnitSequence D * ambientCornerSeq D g *
        cornerUnitSequence D : BoundedMatrixSequence (fun n ↦ model n)) :
        ∀ n, Matrix (model n) (model n) ℂ) n
      = cornerUnitSequence D n * ambientCornerSeq D g n *
        cornerUnitSequence D n := rfl
  rw [hmul, cornerUnitSequence_apply, ambientCornerSeq_apply, ambientCornerMap]
  exact cornerEmbed_cornerCut (D.qHermitian n) (D.qIdem n) _

end Sequences

/-! ## The identification in the corner corona -/

section CoronaClass

variable {G : Type} [Group G] {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The printed `(q_n)` on the retained coordinates is the restriction of the
projection lift `Q`. -/
theorem cornerUnitSequence_eq_restrictSeq {φ : ℕ → ℕ}
    (Q : BoundedMatrixSequence (fun n ↦ X n))
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (hDq : ∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k)) :
    cornerUnitSequence D = restrictSeq X φ Q := by
  refine lp.ext (funext fun k ↦ ?_)
  rw [cornerUnitSequence_apply, hDq k]
  rfl

/-- The class of the printed `(q_n)` is the printed `q`, read on the retained
coordinates and along the ultrafilter. -/
theorem cornerUnitSequence_class {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (Q : BoundedMatrixSequence (fun n ↦ X n))
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (q : NormMatrixCStarCorona (fun n ↦ X n))
    (hQ : normMatrixCStarCoronaMk (fun n ↦ X n) Q = q)
    (hDq : ∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k))
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    filterMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ω : Filter ℕ)
        (cornerUnitSequence D)
      = retainedCoronaToOmega X φ hφ ω hω q := by
  rw [cornerUnitSequence_eq_restrictSeq Q D hDq, ← hQ, retainedCoronaToOmega_mk]

/-- **`ι 1 = q`.**  The corner-corona embedding carries the unit of the corner
corona to the printed projection `q`, read on the retained coordinates and
along the ultrafilter. -/
theorem correctedCornerCoronaEmbedHom_one_eq {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (Q : BoundedMatrixSequence (fun n ↦ X n))
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (q : NormMatrixCStarCorona (fun n ↦ X n))
    (hQ : normMatrixCStarCoronaMk (fun n ↦ X n) Q = q)
    (hDq : ∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k))
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    correctedCornerCoronaEmbedHom D (ω : Filter ℕ) 1
      = retainedCoronaToOmega X φ hφ ω hω q := by
  have hone : (1 : FilterMatrixCStarCorona
        (fun n ↦ D.cornerModel n) (ω : Filter ℕ))
      = filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ) 1 :=
    (map_one (filterMatrixCStarCoronaMk
      (fun n ↦ D.cornerModel n) (ω : Filter ℕ))).symm
  rw [hone]
  change correctedCornerCoronaEmbed D (ω : Filter ℕ)
    (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ) 1) = _
  rw [correctedCornerCoronaEmbed_mk, cornerEmbedSequence_one,
    cornerUnitSequence_eq_restrictSeq Q D hDq, ← hQ, retainedCoronaToOmega_mk]

/-- **The missing link.**  The corona class of the printed `(W_n(g))`, read in
the ambient corona through the printed identification of the corner, is the
printed `q Θ(g) q`.

`hclass` is the conclusion of `manuscriptCornerCoronaClass` — the ambient class
equation of Lemma `lem:central-corona-corner`, with `z` the ambient `Θ(g)`.
The passage from `q z` to `q z q` costs nothing and uses no centrality: the
embedded corner sequence is its own two-sided cut by `(q_n)`, so its class is
its own two-sided cut by `q`. -/
theorem correctedCornerCoronaEmbedHom_class_eq {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (Q : BoundedMatrixSequence (fun n ↦ X n))
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (q : NormMatrixCStarCorona (fun n ↦ X n)) (hqid : q * q = q)
    (hQ : normMatrixCStarCoronaMk (fun n ↦ X n) Q = q)
    (hDq : ∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k))
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (z : NormMatrixCStarCorona (fun n ↦ X n)) (g : G)
    (hclass : normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
      = coronaRestrict X φ hφ (q * z)) :
    correctedCornerCoronaEmbedHom D (ω : Filter ℕ)
        (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ)
          (correctedCornerMapSequence D g))
      = retainedCoronaToOmega X φ hφ ω hω (q * z * q) := by
  have hL : correctedCornerCoronaEmbedHom D (ω : Filter ℕ)
        (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ)
          (correctedCornerMapSequence D g))
      = filterMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ω : Filter ℕ)
          (ambientCornerSeq D g) := by
    change correctedCornerCoronaEmbed D (ω : Filter ℕ) _ = _
    rw [correctedCornerCoronaEmbed_mk,
      cornerEmbedSequence_correctedCornerMapSequence]
  have hA : filterMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ω : Filter ℕ)
        (ambientCornerSeq D g)
      = retainedCoronaToOmega X φ hφ ω hω (q * z) := by
    have h := congrArg (cofiniteCoronaToOmega (fun k ↦ X (φ k)) ω hω) hclass
    rw [cofiniteCoronaToOmega_mk] at h
    rw [h, retainedCoronaToOmega, StarAlgHom.comp_apply]
    rfl
  have hU := cornerUnitSequence_class hφ Q D q hQ hDq ω hω
  have hcut := congrArg
    (filterMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ω : Filter ℕ))
    (cornerUnitSequence_mul_ambientCornerSeq_mul D g)
  rw [map_mul, map_mul, hU, hA] at hcut
  rw [hL, hA, ← hcut, ← map_mul, ← map_mul]
  congr 1
  rw [show q * (q * z) * q = q * q * z * q by noncomm_ring, hqid]

/-- **The corner corona *is* the corner `q 𝒬 q`.**  The image of the
corner-corona embedding is exactly the set of elements fixed by the two-sided
cut with `q`, which is the corner of the retained ambient corona.  Together
with `correctedCornerCoronaEmbedHom_injective` this makes `ι` an isomorphism
onto the printed corner, so an equation in the image is an equation of corner
classes. -/
theorem correctedCornerCoronaEmbedHom_range {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (Q : BoundedMatrixSequence (fun n ↦ X n))
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (q : NormMatrixCStarCorona (fun n ↦ X n))
    (hQ : normMatrixCStarCoronaMk (fun n ↦ X n) Q = q)
    (hDq : ∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k))
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    Set.range (correctedCornerCoronaEmbedHom D (ω : Filter ℕ))
      = {x : FilterMatrixCStarCorona (fun k ↦ X (φ k)) (ω : Filter ℕ) |
          retainedCoronaToOmega X φ hφ ω hω q * x *
            retainedCoronaToOmega X φ hφ ω hω q = x} := by
  have hone := correctedCornerCoronaEmbedHom_one_eq hφ Q D q hQ hDq ω hω
  have hunit := cornerUnitSequence_class hφ Q D q hQ hDq ω hω
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, rfl⟩
    rw [← hone, ← map_mul, ← map_mul, one_mul, mul_one]
  · intro hx
    obtain ⟨a, ha⟩ :=
      filterMatrixCStarCoronaMk_surjective (fun k ↦ X (φ k)) (ω : Filter ℕ) x
    refine ⟨filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ)
      (cornerCompressSequence D a), ?_⟩
    change correctedCornerCoronaEmbed D (ω : Filter ℕ) _ = x
    rw [correctedCornerCoronaEmbed_mk,
      cornerEmbedSequence_cornerCompressSequence, map_mul, map_mul, hunit, ha]
    exact hx

end CoronaClass

/-! ## The printed sentence as one closed proposition -/

/-- **"The coordinate elements represent `b`", with `b` written through `Θ`.**

Under the hypotheses of Lemma `lem:central-corona-corner` — a countable group,
a norm-matrix-corona representation `ρ`, and a nonzero projection `q`
commuting with `ρ(G)` — and for any ultrafilter refining `cofinite`, the
printed corner data `D` exists and:

1. the corner corona embeds **injectively** into the ambient corona over the
   retained coordinates, by the printed identification
   `q_n M_{d_n}(ℂ) q_n ≅ M_{r_n}(ℂ)`;
2. that embedding carries the unit of the corner corona to the printed `q`;
3. the class of the printed `(W_n(g))` in the *corner* corona is carried to
   `q ρ(g) q`.

Clause 3 is the sentence the audit found missing between
`manuscriptPrintedCoordinateGramRepresents` (which produces the Gram element of
the classes `[W_·(s)]`) and the printed definition of `b` (which is the Gram
element of the `q Θ(s) q`).  Clauses 1 and 2 are what make clause 3 an
identification *of the corner class* rather than merely of its image: `ι` is
injective, so `[W_·(g)]` is determined by clause 3, and `ι 1 = q`, so the
target sits in a corner with unit `q`.

Both sides of clause 3 live in the corona over the retained coordinates along
`ω`; `retainedCoronaToOmega` is the composite of the two coordinate passages
the printed proof makes ("after passing to a subsequence" and "along `ω`"),
each of which is already a `⋆`-homomorphism in this repository. -/
def CornerCoronaClassIdentification : Prop :=
  ∀ (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (q : NormMatrixCStarCorona (fun n ↦ X n)),
    star q = q → q * q = q → q ≠ 0 →
    (∀ g : G, ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * q =
      q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) →
    ∀ (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite),
      ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
        (D : PrintedCornerData G (fun k ↦ X (φ k))),
        (∀ k, 0 < Fintype.card (D.cornerModel k)) ∧
        (∀ k g, HEq (D.cornerRepresentation.map k g) (D.cornerMap k g)) ∧
        Function.Injective (correctedCornerCoronaEmbedHom D (ω : Filter ℕ)) ∧
        correctedCornerCoronaEmbedHom D (ω : Filter ℕ) 1
          = retainedCoronaToOmega X φ hφ ω hω q ∧
        Set.range (correctedCornerCoronaEmbedHom D (ω : Filter ℕ))
          = {x : FilterMatrixCStarCorona (fun k ↦ X (φ k)) (ω : Filter ℕ) |
              retainedCoronaToOmega X φ hφ ω hω q * x *
                retainedCoronaToOmega X φ hφ ω hω q = x} ∧
        (∀ g : G,
          correctedCornerCoronaEmbedHom D (ω : Filter ℕ)
              (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)
                (ω : Filter ℕ) (correctedCornerMapSequence D g))
            = retainedCoronaToOmega X φ hφ ω hω
                (q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                  NormMatrixCStarCorona (fun n ↦ X n)) * q))

/-- Closed proof that the corona class of the printed `(W_n(g))` is the printed
`q Θ(g) q`. -/
theorem manuscriptCornerCoronaClassIdentification :
    CornerCoronaClassIdentification := by
  intro G _ _ X _ rho q hqstar hqid hqne hcentral ω hω
  obtain ⟨φ, hφ, Q, D, hQproj, hQmk, hDq, hDqne, hcard, hHEq, hclass⟩ :=
    manuscriptCornerCoronaClass G X rho q hqstar hqid hqne hcentral
  exact ⟨φ, hφ, D, hcard, hHEq,
    correctedCornerCoronaEmbedHom_injective D (ω : Filter ℕ),
    correctedCornerCoronaEmbedHom_one_eq hφ Q D q hQmk hDq ω hω,
    correctedCornerCoronaEmbedHom_range hφ Q D q hQmk hDq ω hω,
    fun g ↦ correctedCornerCoronaEmbedHom_class_eq hφ Q D q hqid hQmk hDq ω hω
      _ g (hclass g)⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
