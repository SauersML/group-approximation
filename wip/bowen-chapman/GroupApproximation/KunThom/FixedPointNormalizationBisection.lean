import GroupApproximation.KunThom.FixedPointNormalizationPatching
import GroupApproximation.Matching.PartialClusterPresentation
import GroupApproximation.Matching.FiniteGroupoidBisection

/-!
# Patched bisections of a cluster groupoid

The objects of a finite cluster system are finite models; place them as
disjoint blocks inside one ambient model.  A bisection of the cluster groupoid
then gives a permutation of the blocks and, by choosing a representative of
every arrow, one candidate partial bijection per block.  Patching these
arrows (`BlockPatching.BlockArrows.patch`) gives a permutation of the ambient
model.

Every representative is a cluster candidate, so its forward equivariance
defect is below `h * scale / 2`.  With the commutation count of
`BlockPatching` this bounds how far a patched bisection is from commuting
with the labelled action: the converse half of Kun--Thom, arXiv:2608.06222v3,
Lemma 4.2(4).
-/

namespace GroupApproximation
namespace BlockPatching

open CategoryTheory

universe u

variable {I : Type u} [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
variable (D : PartialClusterSystem I L) {Y : FiniteModel}

/-- The objects of a cluster system as disjoint blocks of an ambient model. -/
def clusterEmbedding (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      ι X x = ι X' z → X = X') :
    BlockEmbedding Y I where
  model := D.model
  embed := ι
  embed_injective := hinj
  embed_disjoint := hdisj

variable {D}

/-- The object permutation of a bisection, read on indices. -/
def bisectionIndexEquiv (b : FiniteGroupoid.Bisection D.presentation.Obj) :
    I ≃ I where
  toFun X := (b.objEquiv ⟨X⟩).val
  invFun X := (b.objEquiv.symm ⟨X⟩).val
  left_inv X := by
    change (b.objEquiv.symm (b.objEquiv ⟨X⟩)).val = X
    rw [Equiv.symm_apply_apply]
  right_inv X := by
    change (b.objEquiv (b.objEquiv.symm ⟨X⟩)).val = X
    rw [Equiv.apply_symm_apply]

variable {ι : ∀ X, D.model X → Y} {hinj : ∀ X, Function.Injective (ι X)}
  {hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
    ι X x = ι X' z → X = X'}

/-- A chosen representative of the arrow of a bisection at an object. -/
noncomputable def bisectionRep (b : FiniteGroupoid.Bisection D.presentation.Obj)
    (X : I) : D.clusterData.Rep X (bisectionIndexEquiv b X) :=
  Quotient.out (b.hom ⟨X⟩ : Quotient (D.clusterData.nearSetoid X
    (bisectionIndexEquiv b X)))

/-- The block arrows of a bisection: one chosen candidate per object. -/
noncomputable def bisectionArrows
    (b : FiniteGroupoid.Bisection D.presentation.Obj) :
    BlockArrows (clusterEmbedding D ι hinj hdisj) where
  objEquiv := bisectionIndexEquiv b
  arrow X := (bisectionRep b X).1

theorem bisectionArrows_isClusterCandidate
    (b : FiniteGroupoid.Bisection D.presentation.Obj) (X : I) :
    ((bisectionArrows (ι := ι) (hinj := hinj) (hdisj := hdisj) b).arrow X
      ).IsClusterCandidate (D.act X) (D.act (bisectionIndexEquiv b X))
        D.h D.scale := by
  exact (FinitePartialBijection.mem_clusterCandidates (D.act X)
    (D.act (bisectionIndexEquiv b X)) D.h D.scale _).mp (bisectionRep b X).2

/-- The labelled action of a cluster system on its blocks, together with an
ambient labelled action. -/
def clusterAction (act : L → Equiv.Perm Y) :
    BlockAction (clusterEmbedding D ι hinj hdisj) L where
  act := act
  blockAct := D.act

/-- **Patched bisections almost commute with the labels.**  The commutation
defect of a patched bisection with a label is at most twice the mass off the
glued domain, twice the compatibility failures of the block actions, and the
forward candidate threshold summed over the objects. -/
theorem card_commutationDefect_bisectionPatch_le
    (b : FiniteGroupoid.Bisection D.presentation.Obj)
    (act : L → Equiv.Perm Y) (s : L) :
    ((hammingDisagreement
        ((bisectionArrows (ι := ι) (hinj := hinj) (hdisj := hdisj) b).patch *
          act s)
        (act s *
          (bisectionArrows (ι := ι) (hinj := hinj) (hdisj := hdisj) b).patch)
      ).card : ℝ) ≤
      2 * ((Finset.univ \
        (bisectionArrows (ι := ι) (hinj := hinj) (hdisj := hdisj) b).domain
          ).card : ℝ) +
        2 * ((clusterAction (ι := ι) (hinj := hinj) (hdisj := hdisj) (D := D)
          act).globalCompatFailure s).card +
        ∑ _X : I, D.h * D.scale / 2 := by
  set β := bisectionArrows (ι := ι) (hinj := hinj) (hdisj := hdisj) b
  set A := clusterAction (ι := ι) (hinj := hinj) (hdisj := hdisj) (D := D) act
  have hcount := β.card_commutationDefect_patch_le A s
  have hdef : ∀ X : I,
      (((β.arrow X).equivarianceDefect (A.blockAct X)
        (A.blockAct (β.objEquiv X))).card : ℝ) ≤ D.h * D.scale / 2 :=
    fun X ↦ le_of_lt
      (bisectionArrows_isClusterCandidate (ι := ι) (hinj := hinj)
        (hdisj := hdisj) b X).forwardSmall
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
          2 * ((A.globalCompatFailure s).card : ℝ) +
          ∑ _X : I, D.h * D.scale / 2 := by
        gcongr with X
        exact hdef X

/-- Disjointly embedded objects of a cluster system carry at most `|Y|`
points in total. -/
theorem sum_card_model_le (e : ∀ X, D.model X → Y)
    (he : ∀ X, Function.Injective (e X))
    (hd : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      e X x = e X' z → X = X') :
    ∑ X, Fintype.card (D.model X) ≤ Fintype.card Y := by
  classical
  have hinjSigma : Function.Injective (fun p : Σ X, D.model X ↦ e p.1 p.2) := by
    rintro ⟨X, x⟩ ⟨X', z⟩ h
    have hXX : X = X' := hd X X' x z h
    subst hXX
    have hxz : x = z := he X h
    subst hxz
    rfl
  have hcard := Fintype.card_le_of_injective _ hinjSigma
  simpa only [Fintype.card_sigma] using hcard

/-- **The candidate threshold is negligible once `h` is.**  Every object has
at least `17 * scale` points, so the per-object threshold `h * scale / 2`,
summed over disjointly embedded objects, is at most `h / 34` times the
ambient size.  With the cluster expansion constant `h = h_n → 0`, as the
Alekseev--Thom scale choice requires, the error term of
`card_commutationDefect_bisectionPatch_le` is `o(|Y|)`. -/
theorem sum_candidateThreshold_le (e : ∀ X, D.model X → Y)
    (he : ∀ X, Function.Injective (e X))
    (hd : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      e X x = e X' z → X = X') :
    ∑ _X : I, D.h * D.scale / 2 ≤ D.h / 34 * Fintype.card Y := by
  have hnn : 0 ≤ D.h / 34 := div_nonneg D.h_pos.le (by norm_num)
  have hsize : ∀ X, (17 * D.scale : ℝ) ≤ Fintype.card (D.model X) :=
    fun X ↦ by exact_mod_cast D.size X
  have hsum : ((∑ X, Fintype.card (D.model X) : ℕ) : ℝ) ≤ Fintype.card Y := by
    exact_mod_cast sum_card_model_le e he hd
  calc ∑ _X : I, D.h * D.scale / 2
      = ∑ _X : I, D.h / 34 * (17 * D.scale : ℝ) := by
        refine Finset.sum_congr rfl fun _ _ ↦ ?_
        ring
    _ ≤ ∑ X : I, D.h / 34 * (Fintype.card (D.model X) : ℝ) :=
        Finset.sum_le_sum fun X _ ↦ mul_le_mul_of_nonneg_left (hsize X) hnn
    _ = D.h / 34 * ((∑ X, Fintype.card (D.model X) : ℕ) : ℝ) := by
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ D.h / 34 * Fintype.card Y := mul_le_mul_of_nonneg_left hsum hnn

end BlockPatching
end GroupApproximation
