import GroupApproximation.GGT.OsinTheorem54Family
import GroupApproximation.GGT.OsinTheorem54SepCommSet
import GroupApproximation.GGT.OsinTheorem54SepGapY
import GroupApproximation.GGT.OsinTheorem54SepEnum
import GroupApproximation.GGT.OsinTheorem54SepLetterCount
import GroupApproximation.GGT.OsinTheorem54SepLemma55

/-!
# Inhabiting `SepDataFam`

Osin's Theorem 5.4 at a general family reduces to `SepDataStatementFam`, and
this module assembles that statement from what the tree now has, leaving the
open leaves as leading binders so that an audit can read them off by name.

`enlarged` is the relative generating set on

  `Y = {y | ∀ λ, S(1,y;D) = ∅}`,

and `sep` is the Λ-sum `∑ λ, sepCard D λ Dc`.  Both choices are forced rather
than convenient: Osin's separating set runs over all `λ` at once, so the
enlargement must be blind to `λ` and the count must be a sum, which is also why
Lemma 4.9 is needed in its global form below.

## What is assembled and what is assumed

Discharged from landed lemmas, per `λ` and then summed: `sep_self`
(`sepCard_self`), `sep_comm` (`sepCard_comm`, and the only place the symmetric
base is spent), `sep_smul` (`sepCard_smul`), `base_subset`
(`sepSet_eq_empty_of_mem_base`, whence the hypothesis `1 ≤ Dc`), and `fam_eq`.

`sep_le_dist` is **not** assumed: it follows from `h49` and
`sepCard_le_one_of_mem_alphabet`, the constant `3` falling out as `1 + 2` from
the defect-two triangle inequality iterated along an enlarged geodesic.

The rest are binders, listed one per line at the theorem so each is visible by
name.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## From a larger base back to the original -/

/-- **A `SepDataFam` for a larger base is one for the original.**

Stated first because the symmetric base is threaded exactly once: the general
case is reduced to the symmetric one by `exists_symmetric_base'`, which produces
`D'` with `D.base ⊆ D'.base` and `D'.fam = D.fam`, and this carries the data
back.  `enlarged` is untouched, so `AcylindricalCore` is literally the same
statement on both sides. -/
def sepDataFam_of_base_subset {D D' : RelGenSet G Λ}
    (hbase : D.base ⊆ D'.base) (hfam : D'.fam = D.fam) (S : SepDataFam D') :
    SepDataFam D where
  sep := S.sep
  enlarged := S.enlarged
  base_subset := hbase.trans S.base_subset
  fam_eq := S.fam_eq.trans hfam
  emb := S.emb
  sep_self := S.sep_self
  sep_comm := S.sep_comm
  sep_triangle := S.sep_triangle
  sep_smul := S.sep_smul
  dist_le_sep := S.dist_le_sep
  sep_le_dist := S.sep_le_dist

/-- The residue is unchanged by the reduction, `enlarged` being the same. -/
theorem acylindricalCore_of_base_subset {D D' : RelGenSet G Λ}
    (hbase : D.base ⊆ D'.base) (hfam : D'.fam = D.fam) (S : SepDataFam D') :
    (sepDataFam_of_base_subset hbase hfam S).AcylindricalCore
      ↔ S.AcylindricalCore := Iff.rfl

/-! ## Osin's `Y`, and that it is a relative generating set -/

/-- **`Y` is closed under inversion.**  By left-invariance and symmetry of the
separating set --- the two landed halves `sepSet_smul` and `sepSet_comm`. -/
theorem memY_inv (D : RelGenSet G Λ) (Dc : ℕ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {y : G}
    (hy : ∀ lam : Λ, sepSet D lam Dc 1 y = ∅) :
    ∀ lam : Λ, sepSet D lam Dc 1 y⁻¹ = ∅ := by
  intro lam
  have h1 := sepSet_smul D lam Dc y⁻¹ 1 y
  rw [mul_one, inv_mul_cancel] at h1
  rw [sepSet_comm D lam Dc hsymm 1 y⁻¹, h1, hy lam, Set.image_empty]

/-- **`X ⊆ Y`**, the first half of Osin's Lemma 5.6. -/
theorem base_subset_Y (D : RelGenSet G Λ) {Dc : ℕ} (hDc : 1 ≤ Dc) :
    D.base ⊆ {y : G | ∀ lam : Λ, sepSet D lam Dc 1 y = ∅} := fun _ hx _ =>
  sepSet_eq_empty_of_mem_base D _ hDc hx

/-- **`Y ⊔ ℋ` is a symmetric generating set**, so it carries a `RelGenSet`. -/
theorem isSymmetricGeneratingSet_Y (D : RelGenSet G Λ) {Dc : ℕ} (hDc : 1 ≤ Dc)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) :
    IsSymmetricGeneratingSet
      ({y : G | ∀ lam : Λ, sepSet D lam Dc 1 y = ∅} ∪
        (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))) := by
  constructor
  · rintro y (hy | hy)
    · exact Or.inl (memY_inv D Dc hsymm hy)
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
      have hlam' : y ∈ D.fam lam := hlam
      exact Or.inr (Set.mem_iUnion.mpr ⟨lam, inv_mem hlam'⟩)
  · have hsub : D.base ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
        ⊆ {y : G | ∀ lam : Λ, sepSet D lam Dc 1 y = ∅} ∪
          (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) := by
      rintro z (hz | hz)
      · exact Or.inl (base_subset_Y D hDc hz)
      · exact Or.inr hz
    have hmono := Subgroup.closure_mono hsub
    rw [D.symmetricGenerating.closure_eq] at hmono
    exact top_le_iff.mp hmono

/-- **Osin's enlarged relative generating set**, on `Y` over the same family. -/
def enlargedY (D : RelGenSet G Λ) {Dc : ℕ} (hDc : 1 ≤ Dc)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) : RelGenSet G Λ :=
  ⟨{y : G | ∀ lam : Λ, sepSet D lam Dc 1 y = ∅}, D.fam,
    isSymmetricGeneratingSet_Y D hDc hsymm⟩

/-! ## The assembly -/

/-- **`SepDataStatementFam` at one `D`, modulo its leading binders.**

The binders, one per line and each visible by name:

* `h48` --- Osin's Lemma 4.8 at each `λ`, without which `sepCard` is not known
  to count a finite set at all.
* `h49` --- **Osin's Lemma 4.9 in GLOBAL form**: the defect-two triangle
  inequality for the Λ-SUM, at most two exceptional cosets across all `λ`
  together.  It is stated on the sum and not per `λ` because a per-`λ` version
  summed over `Λ` gives defect `2|Λ|`, and the field would then be false at
  `|Λ| ≥ 2`.  It reduces to fp-geometry's `isolatedComponentBound_le_six` ---
  the §4.2 bound at `n ≤ 6` --- with nothing else between, and is a theorem by
  that route (`lemmaFourNine_of_bound`), as is `h48`.
* `h55`, `hM`, `hloc` --- Osin's Lemma 5.5, the bounded-detour condition of his
  Lemma 5.6, and the local finiteness of his Lemma 5.8.  These are exactly the
  inputs of `isHyperbolicallyEmbedded_of_lemma55`, which discharges `emb`.  The
  first two are theorems now --- `GuessingGeodesicsCriterion.osinLemma55` and
  `OsinLemma56Inheritance.exists_boundedDetour` --- and are supplied downstream
  rather than assumed.
* `hdist`, `hsle` --- Lemma 5.10's two halves.  **Neither is a leaf.**  Each is
  provable from what is already landed: `hdist` by induction on the cardinality
  of `sepIndexSet` via its minimum, with the gap letters supplied by
  `sepSet_gap_one_eq_empty` and the crossing letters by a component's span lying
  in `H_lam`; `hsle` by iterating `h49` along an enlarged geodesic against
  `sepCard_le_one_of_mem_alphabet`, the constant `3` falling out as `1 + 2`.
  They appear as binders only because each is a word induction that belongs in
  its own file; both of those files exist now, and this is the context they were
  proved against.
* `h511` --- Osin's Lemma 5.11, the residue `AcylindricalCore`. -/
theorem sepDataFam_of_binders [Fintype Λ] (D : RelGenSet G Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (_h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (h49 : ∀ f g h : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ (∑ lam : Λ, sepCard D lam Dc f h)
        + (∑ lam : Λ, sepCard D lam Dc g h) + 2)
    (h55 : OsinLemma55.{u}) (hemb : D.IsHyperbolicallyEmbedded)
    (hM : ∃ M : ℕ, ∀ b ∈ (enlargedY D hDc hsymm).alphabet.carrier,
      ∀ w : List G, (∀ x ∈ w, x ∈ D.alphabet.carrier) → w.prod = b →
      w.length = wordDist D.alphabet.carrier 1 b →
      ∀ i ≤ w.length,
        wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 (w.take i).prod ≤ M)
    (hloc : ∀ (lam : Λ) (n : ℕ),
      ((enlargedY D hDc hsymm).relBall lam n).Finite)
    (hdist : ∀ f g : G,
      wordDist (enlargedY D hDc hsymm).alphabet.carrier f g
        ≤ 2 * (∑ lam : Λ, sepCard D lam Dc f g) + 1)
    (hsle : ∀ f g : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ 3 * wordDist (enlargedY D hDc hsymm).alphabet.carrier f g)
    (h511 : ∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
      wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 z = R →
        {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
            wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
              (z⁻¹ * k * z) ≤ m}.Finite ∧
          {k : G | wordDist (enlargedY D hDc hsymm).alphabet.carrier 1 k ≤ m ∧
            wordDist (enlargedY D hDc hsymm).alphabet.carrier 1
              (z⁻¹ * k * z) ≤ m}.ncard ≤ N) :
    ∃ S : SepDataFam D, S.AcylindricalCore := by
  refine ⟨{ sep := fun f g => ∑ lam : Λ, sepCard D lam Dc f g
            enlarged := enlargedY D hDc hsymm
            base_subset := base_subset_Y D hDc
            fam_eq := rfl
            emb := isHyperbolicallyEmbedded_of_lemma55 h55 D
              (enlargedY D hDc hsymm) hemb ?_ hM hloc
            sep_self := fun f =>
              Finset.sum_eq_zero (fun lam _ => sepCard_self D lam Dc f)
            sep_comm := fun f g =>
              Finset.sum_congr rfl
                (fun lam _ => sepCard_comm D lam Dc hsymm f g)
            sep_triangle := h49
            sep_smul := fun a f g =>
              Finset.sum_congr rfl
                (fun lam _ => sepCard_smul D lam Dc a f g)
            dist_le_sep := hdist
            sep_le_dist := hsle }, h511⟩
  rintro z (hz | hz)
  · exact Or.inl (base_subset_Y D hDc hz)
  · exact Or.inr hz

end OsinEnlargement
end GGT
end GroupApproximation
