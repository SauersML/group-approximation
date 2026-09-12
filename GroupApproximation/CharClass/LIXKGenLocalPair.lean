import GroupApproximation.CharClass.LIXKGenBaseChart
import GroupApproximation.CharClass.BundleTotalOn
import GroupApproximation.CharClass.RelativeProdContractible
import GroupApproximation.CharClass.RelativeLocal
import GroupApproximation.CharClass.RelativeLocalModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The bundle pair over a contractible neighbourhood of the `i`-th zero, at rank `n`

Lane `lix-oddside-n` (chart side of `KGenLocalNonzero`, lead ruling of 2026-09-12).

This is the rank-`n`, `k`-zero counterpart of `CharClass/LIXBaseBall.lean`,
`CharClass/LIXLocalPair.lean` and `CharClass/LIXLocalPairClosed.lean`, at the `i`-th zero
`KGen.lixKZero n k dd i` of the `k`-section, over `CharClass/LIXKGenBaseChart.lean`'s
`lixKBC n k dd i`.

The one change of substance is the neighbourhood.  `KGenLocalNonzero` (lane `lix-oddside`)
asks, at each zero, for a set containing **no other zero**, so the trivialising set of the
mapping torus at `z_i` is cut by the complement of the other `k` zeros before the ball is
chosen inside it.  The other zeros form a finite, hence closed, set, so the cut set is still an
open neighbourhood of `z_i`, and the ball inside it avoids them (`lixKZero_notMem_lixKTrivBall`).

## Main declarations

* `KGen.otherZeros`, `isClosed_otherZeros`, `lixKZero_mem_compl_otherZeros`.
* `KGen.lixKTrivSet n k dd i hGc hGu` — the trivialising set at `z_i`, minus the other zeros.
* `KGen.lixKBaseBall`, `lixKBallChart`, `contractibleSpace_lixKBallChart_target`.
* `KGen.lixKTrivBall n k dd i hGc hGu` — **the contractible open neighbourhood of `z_i`**, with
  `lixKTrivBall_subset`, `isOpen_lixKTrivBall`, `lixKZero_mem_lixKTrivBall`,
  `lixKZero_notMem_lixKTrivBall`, `lixKTrivBall_subset_target`, `contractibleSpace_lixKTrivBall`.
* `KGen.lixKBundlePairIso` — the bundle pair over it, as a product pair.
* `KGen.lixKLocalPairIsoClosed` — **the identification with the local model**, unconditional.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open Set Metric CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 1. The other zeros -/

/-- The zeros of the `k`-section other than the `i`-th. -/
def otherZeros (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    Set (↥sphereOne × Gen.baseM n dd) :=
  lixKZero n k dd '' {j | j ≠ i}

theorem isClosed_otherZeros (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    IsClosed (otherZeros n k dd i) :=
  ((Set.toFinite {j : Fin (k + 1) | j ≠ i}).image (lixKZero n k dd)).isClosed

theorem lixKZero_mem_compl_otherZeros (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    lixKZero n k dd i ∈ (otherZeros n k dd i)ᶜ := by
  rintro ⟨j, hj, hji⟩
  exact hj (lixKZero_injective n k dd hji)

/-! ## 2. The trivialising set at the `i`-th zero, minus the other zeros -/

/-- The trivialising set of the mapping torus at `z_i`, cut by the complement of the other
zeros. -/
def lixKTrivSet (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Set (↥sphereOne × Gen.baseM n dd) :=
  Bundle.trivSet (lixBundle n G hGc hGu) (lixKZero n k dd i) ∩ (otherZeros n k dd i)ᶜ

theorem isOpen_lixKTrivSet (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    IsOpen (lixKTrivSet n k dd i hGc hGu) :=
  (Bundle.isOpen_trivSet _ _).inter (isClosed_otherZeros n k dd i).isOpen_compl

theorem lixKZero_mem_lixKTrivSet (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKZero n k dd i ∈ lixKTrivSet n k dd i hGc hGu :=
  ⟨Bundle.self_mem_trivSet _ _, lixKZero_mem_compl_otherZeros n k dd i⟩

/-! ## 3. A ball in chart coordinates whose image lands in a prescribed open set -/

theorem exists_ball_image_subset (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    ∃ ε > 0, ball (0 : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ε ⊆
      (lixKBC n k dd i).source ∩ (lixKBC n k dd i) ⁻¹' U := by
  refine Metric.isOpen_iff.mp ?_ _ ⟨zero_mem_lixKBC_source n k dd i, ?_⟩
  · exact (lixKBC n k dd i).continuousOn.isOpen_inter_preimage (lixKBC n k dd i).open_source hU
  · show lixKBC n k dd i ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ U
    rw [show lixKBC n k dd i ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = lixKZero n k dd i from lixKBaseChart_zero n k dd i]
    exact hzU

/-- The radius of a ball whose chart image lies inside `U`. -/
def lixKBaseEps (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    ℝ :=
  (exists_ball_image_subset n k dd i U hU hzU).choose

theorem lixKBaseEps_pos (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    0 < lixKBaseEps n k dd i U hU hzU :=
  (exists_ball_image_subset n k dd i U hU hzU).choose_spec.1

theorem lixKBaseBallPre_subset (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    ball (0 : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) (lixKBaseEps n k dd i U hU hzU) ⊆
      (lixKBC n k dd i).source ∩ (lixKBC n k dd i) ⁻¹' U :=
  (exists_ball_image_subset n k dd i U hU hzU).choose_spec.2

/-- **An open neighbourhood of `z_i` inside `U`**, the chart image of a ball. -/
def lixKBaseBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    Set (↥sphereOne × Gen.baseM n dd) :=
  (lixKBC n k dd i) '' ball 0 (lixKBaseEps n k dd i U hU hzU)

theorem lixKBaseBall_subset (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    lixKBaseBall n k dd i U hU hzU ⊆ U := by
  rintro _ ⟨w, hw, rfl⟩
  exact (lixKBaseBallPre_subset n k dd i U hU hzU hw).2

theorem isOpen_lixKBaseBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    IsOpen (lixKBaseBall n k dd i U hU hzU) :=
  ((lixKBC n k dd i).isOpen_image_iff_of_subset_source
    (fun _ hw => (lixKBaseBallPre_subset n k dd i U hU hzU hw).1)).mpr isOpen_ball

theorem lixKZero_mem_lixKBaseBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    lixKZero n k dd i ∈ lixKBaseBall n k dd i U hU hzU :=
  ⟨(0, 0), mem_ball_self (lixKBaseEps_pos n k dd i U hU hzU), lixKBaseChart_zero n k dd i⟩

/-- The neighbourhood sits inside the chart's target. -/
theorem lixKBaseBall_subset_target (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    lixKBaseBall n k dd i U hU hzU ⊆ (lixKBC n k dd i).target := by
  rw [lixKBaseBall, ← (lixKBC n k dd i).image_source_eq_target]
  exact Set.image_mono fun _ hw => (lixKBaseBallPre_subset n k dd i U hU hzU hw).1

/-- The chart cut down to the ball. -/
def lixKBallChart (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    OpenPartialHomeomorph (ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (↥sphereOne × Gen.baseM n dd) :=
  (lixKBC n k dd i).restrOpen (ball 0 (lixKBaseEps n k dd i U hU hzU)) isOpen_ball

theorem lixKBallChart_source (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    (lixKBallChart n k dd i U hU hzU).source
      = ball (0 : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
          (lixKBaseEps n k dd i U hU hzU) := by
  rw [lixKBallChart, OpenPartialHomeomorph.restrOpen_source]
  exact inter_eq_right.mpr fun _ hw => (lixKBaseBallPre_subset n k dd i U hU hzU hw).1

theorem lixKBallChart_target_eq (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    (lixKBallChart n k dd i U hU hzU).target = lixKBaseBall n k dd i U hU hzU := by
  rw [← (lixKBallChart n k dd i U hU hzU).image_source_eq_target, lixKBallChart_source]
  rfl

/-- **The neighbourhood is contractible**, being homeomorphic to a ball. -/
theorem contractibleSpace_lixKBallChart_target (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (U : Set (↥sphereOne × Gen.baseM n dd)) (hU : IsOpen U) (hzU : lixKZero n k dd i ∈ U) :
    ContractibleSpace ↥(lixKBallChart n k dd i U hU hzU).target := by
  haveI : ContractibleSpace
      ↥(ball (0 : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
        (lixKBaseEps n k dd i U hU hzU)) :=
    (convex_ball _ _).contractibleSpace ⟨_, mem_ball_self (lixKBaseEps_pos n k dd i U hU hzU)⟩
  haveI : ContractibleSpace ↥(lixKBallChart n k dd i U hU hzU).source :=
    (Homeomorph.setCongr (lixKBallChart_source n k dd i U hU hzU)).contractibleSpace
  exact (lixKBallChart n k dd i U hU hzU).toHomeomorphSourceTarget.symm.contractibleSpace

/-! ## 4. The neighbourhood the local argument runs over -/

/-- **The contractible open neighbourhood of `z_i`**, inside the trivialising set at `z_i` and
containing no other zero. -/
def lixKTrivBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Set (↥sphereOne × Gen.baseM n dd) :=
  lixKBaseBall n k dd i (lixKTrivSet n k dd i hGc hGu) (isOpen_lixKTrivSet n k dd i hGc hGu)
    (lixKZero_mem_lixKTrivSet n k dd i hGc hGu)

theorem lixKTrivBall_subset (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKTrivBall n k dd i hGc hGu ⊆ Bundle.trivSet (lixBundle n G hGc hGu) (lixKZero n k dd i) :=
  fun _ hp => (lixKBaseBall_subset n k dd i _ _ _ hp).1

theorem isOpen_lixKTrivBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    IsOpen (lixKTrivBall n k dd i hGc hGu) :=
  isOpen_lixKBaseBall n k dd i _ _ _

theorem lixKZero_mem_lixKTrivBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKZero n k dd i ∈ lixKTrivBall n k dd i hGc hGu :=
  lixKZero_mem_lixKBaseBall n k dd i _ _ _

/-- **The neighbourhood contains no other zero.** -/
theorem lixKZero_notMem_lixKTrivBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (j : Fin (k + 1))
    (hj : j ≠ i) : lixKZero n k dd j ∉ lixKTrivBall n k dd i hGc hGu :=
  fun hmem => (lixKBaseBall_subset n k dd i _ _ _ hmem).2 ⟨j, hj, rfl⟩

theorem lixKTrivBall_subset_target (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKTrivBall n k dd i hGc hGu ⊆ (lixKBC n k dd i).target :=
  lixKBaseBall_subset_target n k dd i _ _ _

theorem contractibleSpace_lixKTrivBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ContractibleSpace ↥(lixKTrivBall n k dd i hGc hGu) := by
  have h := contractibleSpace_lixKBallChart_target n k dd i (lixKTrivSet n k dd i hGc hGu)
    (isOpen_lixKTrivSet n k dd i hGc hGu) (lixKZero_mem_lixKTrivSet n k dd i hGc hGu)
  rwa [lixKBallChart_target_eq] at h

/-- The `i`-th zero, as a point of its neighbourhood. -/
def lixKZeroInBall (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ↥(lixKTrivBall n k dd i hGc hGu) :=
  ⟨lixKZero n k dd i, lixKZero_mem_lixKTrivBall n k dd i hGc hGu⟩

/-! ## 5. The bundle pair over the neighbourhood, and the local model -/

/-- **The bundle pair over the neighbourhood of `z_i` is a product pair.** -/
def lixKBundlePairIso (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (q : ℕ) :
    relCohomology (ZMod 2)
        (TopCat.of (Bundle.Total
          ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))))
        {w : Bundle.Total ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu)) |
          (w : ↥(lixKTrivBall n k dd i hGc hGu) × (Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))} q
      ≅ relCohomology (ZMod 2)
        (TopCat.of (↥(lixKTrivBall n k dd i hGc hGu) × (Fin (lixRank n dd) → ℂ)))
        {p : ↥(lixKTrivBall n k dd i hGc hGu) × (Fin (lixRank n dd) → ℂ) | p.2 ≠ 0} q :=
  relCohomologyCongr
    (Bundle.totalTrivStdOn (lixBundle n G hGc hGu) (lixKZero n k dd i)
      (lixKTrivBall n k dd i hGc hGu) (lixKTrivBall_subset n k dd i hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu _)) _ _
    (Bundle.totalTrivStdOn_image_punctured (lixBundle n G hGc hGu) (lixKZero n k dd i)
      (lixKTrivBall n k dd i hGc hGu) (lixKTrivBall_subset n k dd i hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu _)) q

theorem two_le_two_mul_lixRank (n : ℕ) (dd : Fin ℓ → ℕ) : 2 ≤ 2 * lixRank n dd := by
  rw [lixRank]
  omega

/-- **The bundle pair over the neighbourhood of `z_i`, identified with the local model**, with
no hypotheses. -/
def lixKLocalPairIsoClosed (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    relCohomology (ZMod 2)
        (TopCat.of (Bundle.Total
          ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))))
        {w : Bundle.Total ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu)) |
          (w : ↥(lixKTrivBall n k dd i hGc hGu) × (Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ))
            ∈ Bundle.puncturedSet
              ((lixBundle n G hGc hGu).restrictTo (lixKTrivBall n k dd i hGc hGu))}
        (2 * lixRank n dd)
      ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank n dd) → ℂ))
        (puncturedSet (lixRank n dd)) (2 * lixRank n dd) :=
  (lixKBundlePairIso n k dd i hGc hGu (2 * lixRank n dd)).trans
    (RelativeSupport.relCohomologyProdIso (contractibleSpace_lixKTrivBall n k dd i hGc hGu)
      (lixKZeroInBall n k dd i hGc hGu) (lixRank n dd) (2 * lixRank n dd)
      (two_le_two_mul_lixRank n dd))

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixKZero_notMem_lixKTrivBall
#audit_axioms KGen.contractibleSpace_lixKTrivBall
#audit_axioms KGen.lixKTrivBall_subset_target

end GroupApproximation.CharClass
