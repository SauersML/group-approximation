import GroupApproximation.KunThom.FixedPointNormalizationPatching
import GroupApproximation.KunThom.FixedPointNormalizationScaleSums
import GroupApproximation.KunThom.CentralizerNormalizationClusterSystem
import GroupApproximation.Matching.FiniteGroupoidBisection

/-!
# Patched bisections of a scaled cluster groupoid

`FixedPointNormalizationBisection` patches a bisection of a cluster groupoid
with one radius.  This file does the same for a groupoid with a radius for
each pair of objects (`ScaledFinitePartialClusterData`), where the candidate
threshold of an arrow depends on the pair of objects it joins.

* Over an arbitrary `ScaledFinitePartialClusterData`,
  `card_commutationDefect_scaledBisectionPatch_le` bounds how far a patched
  bisection is from commuting with a label.  The hypothesis is a bound `τ X`
  on the equivariance defect of every candidate out of `X`.
* For a `ScaledPartialClusterSystem`, every candidate from `X` to `X'` has
  forward defect below `h * min (scale X) (scale X') / 2`, and
  `scale X = |model X| / 18`.  So `card_commutationDefect_systemBisectionPatch_le`
  bounds the threshold total by `h / 36` times the ambient size
  (`BlockEmbedding.sum_scaleThreshold_le`).

This is the converse half of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4), at
per-object scales.
-/

namespace GroupApproximation
namespace BlockPatching

open CategoryTheory

universe u

variable {I : Type u} [Fintype I] {Y : FiniteModel}

/-- The objects of scaled cluster data as disjoint blocks of an ambient
model. -/
def scaledClusterEmbedding (D : ScaledFinitePartialClusterData I)
    (ι : ∀ X, D.model X → Y) (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      ι X x = ι X' z → X = X') :
    BlockEmbedding Y I where
  model := D.model
  embed := ι
  embed_injective := hinj
  embed_disjoint := hdisj

/-- The object permutation of a bisection, read on indices. -/
def scaledBisectionIndexEquiv {D : ScaledFinitePartialClusterData I}
    (b : FiniteGroupoid.Bisection D.presentation.Obj) : I ≃ I where
  toFun X := (b.objEquiv ⟨X⟩).val
  invFun X := (b.objEquiv.symm ⟨X⟩).val
  left_inv X := by
    change (b.objEquiv.symm (b.objEquiv ⟨X⟩)).val = X
    rw [Equiv.symm_apply_apply]
  right_inv X := by
    change (b.objEquiv (b.objEquiv.symm ⟨X⟩)).val = X
    rw [Equiv.apply_symm_apply]

/-- A chosen representative of the arrow of a bisection at an object. -/
noncomputable def scaledBisectionRep {D : ScaledFinitePartialClusterData I}
    (b : FiniteGroupoid.Bisection D.presentation.Obj) (X : I) :
    D.Rep X (scaledBisectionIndexEquiv b X) :=
  Quotient.out (b.hom ⟨X⟩ : Quotient (D.nearSetoid X (scaledBisectionIndexEquiv b X)))

/-- The block arrows of a bisection: one chosen candidate per object. -/
noncomputable def scaledBisectionArrows {D : ScaledFinitePartialClusterData I}
    (ι : ∀ X, D.model X → Y) (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      ι X x = ι X' z → X = X')
    (b : FiniteGroupoid.Bisection D.presentation.Obj) :
    BlockArrows (scaledClusterEmbedding D ι hinj hdisj) where
  objEquiv := scaledBisectionIndexEquiv b
  arrow X := (scaledBisectionRep b X).1

/-- An ambient labelled action together with labelled actions on the objects
of scaled cluster data. -/
def scaledClusterAction {L : Type*} {D : ScaledFinitePartialClusterData I}
    (ι : ∀ X, D.model X → Y) (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      ι X x = ι X' z → X = X')
    (act : L → Equiv.Perm Y) (blockAct : ∀ X, L → Equiv.Perm (D.model X)) :
    BlockAction (scaledClusterEmbedding D ι hinj hdisj) L where
  act := act
  blockAct := blockAct

/-- **Patched bisections of scaled cluster data almost commute with the
labels.**  If every candidate out of `X` has equivariance defect at most
`τ X`, the commutation defect of a patched bisection with a label is at most
twice the mass off the glued domain, twice the compatibility failures of the
block actions, and `∑ X, τ X`. -/
theorem card_commutationDefect_scaledBisectionPatch_le {L : Type*} [Fintype L]
    {D : ScaledFinitePartialClusterData I}
    (ι : ∀ X, D.model X → Y) (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      ι X x = ι X' z → X = X')
    (b : FiniteGroupoid.Bisection D.presentation.Obj)
    (act : L → Equiv.Perm Y) (blockAct : ∀ X, L → Equiv.Perm (D.model X))
    (τ : I → ℝ)
    (hτ : ∀ (X X' : I) (f : D.Rep X X'),
      ((f.1.equivarianceDefect (blockAct X) (blockAct X')).card : ℝ) ≤ τ X)
    (s : L) :
    ((hammingDisagreement
        ((scaledBisectionArrows ι hinj hdisj b).patch * act s)
        (act s * (scaledBisectionArrows ι hinj hdisj b).patch)).card : ℝ) ≤
      2 * ((Finset.univ \ (scaledBisectionArrows ι hinj hdisj b).domain).card : ℝ) +
        2 * ((scaledClusterAction ι hinj hdisj act blockAct).globalCompatFailure s).card +
        ∑ X, τ X := by
  set β := scaledBisectionArrows ι hinj hdisj b
  set A := scaledClusterAction ι hinj hdisj act blockAct
  have hcount := β.card_commutationDefect_patch_le A s
  have hdef : ∀ X : I,
      (((β.arrow X).equivarianceDefect (A.blockAct X)
        (A.blockAct (β.objEquiv X))).card : ℝ) ≤ τ X :=
    fun X ↦ hτ X (scaledBisectionIndexEquiv b X) (scaledBisectionRep b X)
  calc ((hammingDisagreement (β.patch * A.act s) (A.act s * β.patch)).card : ℝ)
      ≤ ((2 * (Finset.univ \ β.domain).card + 2 * (A.globalCompatFailure s).card +
          ∑ X, ((β.arrow X).equivarianceDefect (A.blockAct X)
            (A.blockAct (β.objEquiv X))).card : ℕ) : ℝ) := by
        exact_mod_cast hcount
    _ = 2 * ((Finset.univ \ β.domain).card : ℝ) +
          2 * ((A.globalCompatFailure s).card : ℝ) +
          ∑ X, (((β.arrow X).equivarianceDefect (A.blockAct X)
            (A.blockAct (β.objEquiv X))).card : ℝ) := by
        push_cast
        ring
    _ ≤ 2 * ((Finset.univ \ β.domain).card : ℝ) +
          2 * ((A.globalCompatFailure s).card : ℝ) + ∑ X, τ X := by
        gcongr with X
        exact hdef X

/-- **Patched bisections of a scaled cluster system.**  The candidate
thresholds `h * min (scale X) (scale X') / 2` sum to at most `h / 36` times
the ambient size, so the commutation defect of a patched bisection with a
label is at most twice the mass off the glued domain, twice the compatibility
failures, and `h / 36 * |Y|`. -/
theorem card_commutationDefect_systemBisectionPatch_le
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      ι X x = ι X' z → X = X')
    (b : FiniteGroupoid.Bisection D.presentation.Obj)
    (act : L → Equiv.Perm Y) (s : L) :
    ((hammingDisagreement
        ((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).patch * act s)
        (act s * (scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).patch)
      ).card : ℝ) ≤
      2 * ((Finset.univ \
        (scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).domain).card : ℝ) +
        2 * ((scaledClusterAction (D := D.clusterData) ι hinj hdisj act
          D.act).globalCompatFailure s).card +
        D.h / 36 * Fintype.card Y := by
  have hτ : ∀ (X X' : I) (f : D.clusterData.Rep X X'),
      ((f.1.equivarianceDefect (D.act X) (D.act X')).card : ℝ) ≤
        D.h * ((Fintype.card (D.model X) / 18 : ℕ) : ℝ) / 2 := by
    intro X X' f
    have hcand := (FinitePartialBijection.mem_clusterCandidates (D.act X) (D.act X')
      D.h (min (D.scale X) (D.scale X')) f.1).mp f.2
    have hmin : ((min (D.scale X) (D.scale X') : ℕ) : ℝ) ≤
        ((Fintype.card (D.model X) / 18 : ℕ) : ℝ) := by
      rw [← D.scale_eq X]
      exact_mod_cast min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_left hmin D.h_pos.le
    have hfwd := hcand.forwardSmall
    linarith
  have hsum : ∑ X, D.h * ((Fintype.card (D.model X) / 18 : ℕ) : ℝ) / 2 ≤
      D.h / 36 * Fintype.card Y :=
    (scaledClusterEmbedding D.clusterData ι hinj hdisj).sum_scaleThreshold_le D.h_pos.le
  refine (card_commutationDefect_scaledBisectionPatch_le (D := D.clusterData) ι hinj hdisj
    b act D.act (fun X ↦ D.h * ((Fintype.card (D.model X) / 18 : ℕ) : ℝ) / 2) hτ s).trans ?_
  exact add_le_add le_rfl hsum

end BlockPatching
end GroupApproximation
