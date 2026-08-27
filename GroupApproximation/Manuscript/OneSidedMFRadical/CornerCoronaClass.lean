import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCorner
import GroupApproximation.Analysis.CornerMatrixEmbedding
import GroupApproximation.Analysis.FilterMatrixCStarCorona

/-!
# The corona class of the corner representation

`non_mf_groups_exist.tex`, Lemma `lem:central-corona-corner`, last clause:

> ... after passing to an infinite coordinate subsequence, there are nonzero
> projections `q_n ∈ M_{d_n}(ℂ)` and an operator-norm asymptotic
> representation `W_n : G → U(q_n M_{d_n}(ℂ) q_n)` **whose corona class is the
> corner representation `g ↦ q rho(g)`**.

`Manuscript/OneSidedMFRadical/CentralCoronaCorner` delivers that last clause
as two facts stated over *different* index sets: an identity
`[Q V_g Q] = q rho(g)` in the corona over all coordinates `n`, and a
convergence `‖W_k(g) − q_k V_k(g) q_k‖ → 0` along the retained subsequence
`φ`.  Neither one, nor the pair, is the printed sentence: nothing there names
a corona class of `(W_n)`.

This file composes them.  Two constructions are needed, and both are the
identifications the printed proof itself makes.

## The corner is `q_n M_{d_n}(ℂ) q_n`, not an abstract `M_{r_n}(ℂ)`

`PrintedCornerCompression` realizes the corner as the principal block of the
eigenbasis of `q_n`, so the corner unitaries `W_n(g)` are matrices over a
coordinate subtype.  `cornerEmbed` puts them back where the print has them:
zero-extend the block and conjugate back by the eigenbasis unitary.  It is an
isometric star-embedding (`norm_cornerEmbed`, `cornerEmbed_mul`,
`cornerEmbed_conjTranspose`) whose image is the corner, and it carries the
uncorrected compression to the printed `q_n V_n(g) q_n`
(`cornerEmbed_cornerCompression`).  That is the printed identification
`q_n M_{d_n}(ℂ) q_n ≅ M_{r_n}(ℂ)`, used in the direction the sentence needs.

## "After passing to a subsequence" is a map of coronas

Retaining an infinite set of coordinates replaces the corona over `(d_n)` by
the corona over `(d_{φ k})`.  `coronaRestrict` is the induced star-epimorphism
between them: precomposition with `φ` preserves boundedness and carries null
sequences to null sequences because `φ` tends to infinity.  The printed
`q rho(g)`, read after the coordinates are discarded, is
`coronaRestrict (q rho(g))`.

## What is proved

`manuscriptCornerCoronaClass` is the printed sentence with its final clause a
single equation in one algebra:

    [k ↦ cornerEmbed (W_k g)]  =  coronaRestrict (q rho(g))

in the corona over the retained coordinates.  Its proof consumes
`manuscriptCentralCoronaCorner` unchanged; the new content is exactly the
bridge that the two uncomposed facts were missing.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix Topology
open KazhdanCornerMatrices
open PrintedCornerCompression
open scoped Matrix.Norms.L2Operator

noncomputable section
/-! ## The corner representation, read inside the ambient matrices -/

/-- **The printed `W_n(g)`, viewed in `q_n M_{d_n}(ℂ) q_n ⊆ M_{d_n}(ℂ)`.** -/
def ambientCornerMap {G : Type*} [Group G] {model : ℕ → FiniteModel}
    (D : PrintedCornerData G model) (n : ℕ) (g : G) :
    Matrix (model n) (model n) ℂ :=
  cornerEmbed (D.qHermitian n)
    ((D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ))

theorem norm_ambientCornerMap_le_one {G : Type*} [Group G]
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model) (n : ℕ)
    (g : G) : ‖ambientCornerMap D n g‖ ≤ 1 := by
  rw [ambientCornerMap, norm_cornerEmbed]
  exact D.norm_cornerMap_le_one n g

/-- **The printed estimate, moved into the ambient matrices.**  The embedded
corner unitary differs from the printed compression `q_n V_{g,n} q_n` by
exactly the polar correction, whose norm is unchanged by the embedding. -/
theorem norm_ambientCornerMap_sub_compress_le {G : Type*} [Group G]
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model) (n : ℕ)
    (g : G) :
    ‖ambientCornerMap D n g -
        D.q n * (D.V n g : Matrix (model n) (model n) ℂ) * D.q n‖
      ≤ ‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
          - D.compress n g‖ := by
  have hcompress : cornerEmbed (D.qHermitian n) (D.compress n g)
      = D.q n * (D.V n g : Matrix (model n) (model n) ℂ) * D.q n :=
    cornerEmbed_cornerCompression (D.qHermitian n) (D.qIdem n)
      ((D.V n g : Matrix (model n) (model n) ℂ))
  rw [← hcompress, ambientCornerMap, ← cornerEmbed_sub]
  exact le_of_eq (norm_cornerEmbed (D.qHermitian n) _)

/-- **The corner representation as a bounded matrix sequence.**  Its class is
the corona class the printed lemma names. -/
def ambientCornerSeq {G : Type*} [Group G] {model : ℕ → FiniteModel}
    (D : PrintedCornerData G model) (g : G) :
    BoundedMatrixSequence (fun n ↦ model n) :=
  ⟨fun n ↦ ambientCornerMap D n g, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact norm_ambientCornerMap_le_one D n g⟩⟩

theorem ambientCornerSeq_apply {G : Type*} [Group G]
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model) (g : G)
    (n : ℕ) : ambientCornerSeq D g n = ambientCornerMap D n g := rfl

/-! ## Discarding coordinates, as a map of coronas -/

/-- Restriction of a bounded matrix sequence to a coordinate subsequence. -/
def restrictSeq (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (φ : ℕ → ℕ) :
    BoundedMatrixSequence (fun n ↦ X n) →⋆ₐ[ℂ]
      BoundedMatrixSequence (fun k ↦ X (φ k)) where
  toFun a := ⟨fun k ↦ a (φ k), memℓp_infty ⟨‖a‖, by
    rintro _ ⟨k, rfl⟩
    exact boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a (φ k)⟩⟩
  map_one' := by ext k i j; rfl
  map_mul' a b := by ext k i j; rfl
  map_zero' := by ext k i j; rfl
  map_add' a b := by ext k i j; rfl
  commutes' z := by ext k i j; rfl
  map_star' a := by ext k i j; rfl

theorem restrictSeq_apply (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (φ : ℕ → ℕ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) (k : ℕ) :
    restrictSeq X φ a k = a (φ k) := rfl

theorem restrictSeq_star (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (φ : ℕ → ℕ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    restrictSeq X φ (star a) = star (restrictSeq X φ a) :=
  map_star (restrictSeq X φ) a

/-- A subsequence of a sequence that is null along `cofinite` is null along
`cofinite`, because a strictly monotone reindexing tends to infinity.  This is
the only place the subsequence hypothesis is used. -/
theorem isNullMatrixSequence_restrictSeq (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] {φ : ℕ → ℕ}
    (hφ : StrictMono φ) {a : BoundedMatrixSequence (fun n ↦ X n)}
    (ha : IsNullMatrixSequence (fun n ↦ X n) cofinite a) :
    IsNullMatrixSequence (fun k ↦ X (φ k)) cofinite (restrictSeq X φ a) := by
  rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop] at ha ⊢
  exact (ha.comp hφ.tendsto_atTop).congr fun k ↦ rfl

/-- Restriction followed by the quotient map on the retained coordinates. -/
def restrictSeqCoronaQuotient (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (φ : ℕ → ℕ) :
    BoundedMatrixSequence (fun n ↦ X n) →⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun k ↦ X (φ k)) :=
  (normMatrixCStarCoronaQuotient (fun k ↦ X (φ k))).comp (restrictSeq X φ)

@[simp] theorem restrictSeqCoronaQuotient_apply
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (φ : ℕ → ℕ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    restrictSeqCoronaQuotient X φ a =
      normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (restrictSeq X φ a) :=
  rfl

theorem restrictSeqCoronaQuotient_eq_zero_of_null
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (a : BoundedMatrixSequence (fun n ↦ X n))
    (ha : IsNullMatrixSequence (fun n ↦ X n) cofinite a) :
    restrictSeqCoronaQuotient X φ a = 0 := by
  rw [restrictSeqCoronaQuotient_apply]
  apply (normMatrixCStarCoronaMk_eq_zero_iff (fun k ↦ X (φ k)) _).mpr
  exact isNullMatrixSequence_restrictSeq X hφ ha

/-- **"Retain those coordinates", as a homomorphism of coronas.**  Discarding
all coordinates outside the range of `φ` replaces the corona over `(d_n)` by
the corona over `(d_{φ k})`, and the replacement is induced by restriction of
sequences.  `coronaRestrict_star` records that it is a star-homomorphism. -/
def coronaRestrict (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (φ : ℕ → ℕ)
    (hφ : StrictMono φ) :
    NormMatrixCStarCorona (fun n ↦ X n) →+*
      NormMatrixCStarCorona (fun k ↦ X (φ k)) := by
  change FilterMatrixCStarCorona (fun n ↦ X n) cofinite →+*
    NormMatrixCStarCorona (fun k ↦ X (φ k))
  exact (filterMatrixCStarCoronaLift (fun n ↦ X n) cofinite
    (restrictSeqCoronaQuotient X φ)
    (fun a ha ↦ restrictSeqCoronaQuotient_eq_zero_of_null X hφ a ha)).toRingHom

@[simp] theorem coronaRestrict_mk (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    coronaRestrict X φ hφ (normMatrixCStarCoronaMk (fun n ↦ X n) a)
      = normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (restrictSeq X φ a) :=
  by
    change filterMatrixCStarCoronaLift (fun n ↦ X n) cofinite
      (restrictSeqCoronaQuotient X φ)
      (fun b hb ↦ restrictSeqCoronaQuotient_eq_zero_of_null X hφ b hb)
      (filterMatrixCStarCoronaMk (fun n ↦ X n) cofinite a) = _
    rw [filterMatrixCStarCoronaLift_mk, restrictSeqCoronaQuotient_apply]

theorem coronaRestrict_star (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    coronaRestrict X φ hφ (star x) = star (coronaRestrict X φ hφ x) := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
  rw [normMatrixCStarCorona_star_mk, coronaRestrict_mk, restrictSeq_star,
    coronaRestrict_mk, normMatrixCStarCorona_star_mk]

/-! ## The printed lemma, with its final clause composed -/

/-- **Lemma `lem:central-corona-corner`, whole.**

> Let `rho : G → U(𝒬_d)` be a homomorphism from a countable group, and let
> `q ∈ 𝒬_d` be a nonzero projection commuting with `rho(G)`.  Then, after
> passing to an infinite coordinate subsequence, there are nonzero
> projections `q_n ∈ M_{d_n}(ℂ)` and an operator-norm asymptotic
> representation `W_n : G → U(q_n M_{d_n}(ℂ) q_n)` whose corona class is the
> corner representation `g ↦ q rho(g)`.

`φ` is the infinite coordinate subsequence, `Q` the projection lift of `q`,
`D.q` the printed `q_n` — nonzero at every retained stage — and
`D.cornerRepresentation` the printed `(W_n)`, an `OpAlmostRepresentation`
whose maps are `D.cornerMap`.

The final clause is one equation, in the corona over the retained
coordinates: the class of the sequence of corner unitaries, read inside
`q_n M_{d_n}(ℂ) q_n` by the printed identification, is the image of
`q rho(g)` under the restriction map that discarding coordinates induces.
Both sides are elements of `NormMatrixCStarCorona (fun k ↦ X (φ k))`; no
clause of this statement is a limit over one index set compared with an
identity over another. -/
def CornerCoronaClass : Prop :=
  ∀ (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (q : NormMatrixCStarCorona (fun n ↦ X n)),
    star q = q → q * q = q → q ≠ 0 →
    (∀ g : G, ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * q =
      q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) →
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (Q : BoundedMatrixSequence (fun n ↦ X n))
      (D : PrintedCornerData G (fun k ↦ X (φ k))),
      (∀ n, IsOrthogonalProjectionMatrix
        ((Q : ∀ n, Matrix (X n) (X n) ℂ) n)) ∧
      normMatrixCStarCoronaMk (fun n ↦ X n) Q = q ∧
      (∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k)) ∧
      (∀ k, D.q k ≠ 0) ∧
      (∀ k, 0 < Fintype.card (D.cornerModel k)) ∧
      (∀ k g, HEq (D.cornerRepresentation.map k g) (D.cornerMap k g)) ∧
      (∀ g : G,
        normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
          = coronaRestrict X φ hφ
              (q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n))))

/-- Closed proof of the composed central-corona-corner lemma. -/
theorem manuscriptCornerCoronaClass : CornerCoronaClass := by
  intro G _ _ X _ rho q hqstar hqid hqne hcentral
  obtain ⟨Q, φ, D, hφmono, hQproj, hQmk, hDq, hDV, _, hcard, hHEq, _, _, hpair⟩ :=
    manuscriptCentralCoronaCorner G X rho q hqstar hqid hqne hcentral
  refine ⟨φ, hφmono, Q, D, hQproj, hQmk, hDq, D.q_ne_zero, hcard, hHEq, ?_⟩
  intro g
  obtain ⟨hclass, hcorr⟩ := hpair g
  set Wg : BoundedMatrixSequence (fun n ↦ X n) :=
    Q * unitarySequenceBounded X (CollapseUnitaryLift.liftFam X rho g) * Q
    with hWg
  have hW : ∀ k, restrictSeq X φ Wg k
      = D.q k * (D.V k g : Matrix (X (φ k)) (X (φ k)) ℂ) * D.q k := by
    intro k
    rw [hWg, hDq k, hDV k g]
    ext i j
    rfl
  have hbound : ∀ k, ‖((ambientCornerSeq D g :
        BoundedMatrixSequence (fun k ↦ X (φ k))) - restrictSeq X φ Wg) k‖
      ≤ ‖(D.cornerMap k g : Matrix (D.cornerModel k) (D.cornerModel k) ℂ)
          - D.compress k g‖ := by
    intro k
    rw [lp.coeFn_sub, Pi.sub_apply, hW k]
    exact norm_ambientCornerMap_sub_compress_le D k g
  have hnull : IsNullMatrixSequence (fun k ↦ X (φ k)) cofinite
      ((ambientCornerSeq D g : BoundedMatrixSequence (fun k ↦ X (φ k)))
        - restrictSeq X φ Wg) := by
    rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop]
    exact squeeze_zero' (Eventually.of_forall fun k ↦ norm_nonneg _)
      (Eventually.of_forall hbound) hcorr
  calc normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
      = normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (restrictSeq X φ Wg) := by
        rw [← sub_eq_zero, ← map_sub]
        exact (normMatrixCStarCoronaMk_eq_zero_iff (fun k ↦ X (φ k)) _).mpr
          hnull
    _ = coronaRestrict X φ hφmono
          (normMatrixCStarCoronaMk (fun n ↦ X n) Wg) :=
        (coronaRestrict_mk X φ hφmono Wg).symm
    _ = coronaRestrict X φ hφmono
          (q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))) := by rw [hclass]

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
