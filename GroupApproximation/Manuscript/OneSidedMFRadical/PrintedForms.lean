import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Manuscript.OneSidedMFRadical.CanonicalSector

/-!
# Theorem A, Lemma 2.1, Corollary 2.5 and Theorem 2.7, in their printed forms

`non_mf_groups_exist.tex` states four results whose printed conclusions are
phrased without the MF radical:

* **Theorem A** (`thm:compression-criterion`): "every homomorphism from `G`
  to an MF group is trivial on `K`";
* **Lemma 2.1** (`prop:mf-residual-calculus`): "every homomorphism from `G`
  to an MF group is trivial on `K` if and only if every corona homomorphism
  from `G` is trivial on `K`";
* **Corollary 2.5** (`cor:defect-hs`): for every operator norm asymptotic
  representation `(V_n)`, `‖V_n(d) − 1‖₂ → 0` for all `d ∈ 𝔇_G(L)`;
* **Theorem 2.7** (`thm:normal-kazhdan`): the hypothesis is stated per
  representation — "every operator norm asymptotic representation satisfies
  `‖V_n(k) − 1‖₂ → 0` for all `k ∈ K`" — and the conclusion is that every
  corona homomorphism is trivial on `K`.

The development proves each of them in radical form (`K ≤ Rad_MF(G)`,
`𝔇_G(L) ≤ R_{∞→2}(G)`, `K ≤ R_{∞→2}(G) → K ≤ Rad_MF(G)`).  This module
restates the four exactly as printed and derives each from its radical form:
the passage between "trivial on `K` for every homomorphism to an MF group" and
"`K ≤ Rad_MF(G)`" is `literalMFClosure_bot`, and the passage between
"`‖V_n(g) − 1‖₂ → 0` for every `(V_n)`" and "`g ∈ R_{∞→2}(G)`" is
`mem_opToHSShadowResidual_iff_forall_hsKernel`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-! ## "Trivial on `K` for every homomorphism to an MF group" -/

/-- **"Every homomorphism from `G` to an MF group is trivial on `K`."** -/
def KillsMFTargetsOn (G : Type) [Group G] (K : Subgroup G) : Prop :=
  ∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
    ∀ (f : G →* M), ∀ k ∈ K, f k = 1

/-- A subgroup of the MF radical is killed by every homomorphism to an MF
group: the radical is functorial and the radical of an MF group is trivial. -/
theorem killsMFTargetsOn_of_le_residual {G : Type} [Group G] {K : Subgroup G}
    (hK : K ≤ manuscriptCoronaMFResidual G) : KillsMFTargetsOn G K := by
  intro M _ _ hM f k hk
  have hMbot : manuscriptCoronaMFResidual M = ⊥ :=
    (isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot).mp hM
  have hmem : f k ∈ (manuscriptCoronaMFResidual G).map f :=
    Subgroup.mem_map_of_mem _ (hK hk)
  have := map_manuscriptCoronaMFResidual_le f hmem
  rw [hMbot] at this
  simpa using this

/-! ## Lemma 2.1 (`prop:mf-residual-calculus`), as printed -/

/-- **`prop:mf-residual-calculus`, exactly as printed.**  "Let `G` be countable
and `K ≤ G`.  Every homomorphism from `G` to an MF group is trivial on `K` if
and only if every corona homomorphism from `G` is trivial on `K`." -/
def PrintedMFResidualCalculus : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (K : Subgroup G),
    KillsMFTargetsOn G K ↔ ∀ k ∈ K, ManuscriptCoronaMFInvisible k

theorem manuscriptPrintedMFResidualCalculus : PrintedMFResidualCalculus := by
  intro G _ _ K
  constructor
  · intro h k hk
    rw [← mem_manuscriptCoronaMFResidual_iff, ← literalMFClosure_bot,
      mem_literalMFClosure_iff]
    intro M instM instC f hMF _
    exact @h M instM instC hMF f k hk
  · intro h
    exact killsMFTargetsOn_of_le_residual
      (fun k hk => (mem_manuscriptCoronaMFResidual_iff).2 (h k hk))

/-! ## Theorem A (`thm:compression-criterion`), as printed -/

/-- **Theorem A, exactly as printed.**  "Let `G` be countable and let `L ≤ G`
have property (T).  If `K ⊴ G` has property (T) and `K ≤ 𝔇_G(L)`, then every
homomorphism from `G` to an MF group is trivial on `K`.  In particular, a
nontrivial such `K` makes `G` non-MF, and if `G` has property (T) and
`𝔇_G(L) = G`, then every homomorphism from `G` to an MF group is trivial." -/
def PrintedCompressionCriterion : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      (∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
          K ≤ printedDefect L → KillsMFTargetsOn G K) ∧
        (∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
          K ≤ printedDefect L → K ≠ ⊥ → ¬ IsCDEOperatorMF G) ∧
        (HasKazhdanPropertyT.{0, 0} G → printedDefect L = ⊤ →
          KillsMFTargetsOn G ⊤)

theorem manuscriptPrintedCompressionCriterion : PrintedCompressionCriterion := by
  intro G _ _ L hL
  obtain ⟨h1, h2, h3⟩ := manuscriptOneSidedCompressionCriterion G L hL
  refine ⟨fun K _ hK hKD => killsMFTargetsOn_of_le_residual (h1 K hK hKD), h2,
    fun hG hD => killsMFTargetsOn_of_le_residual (le_of_eq (h3 hG hD).symm)⟩

/-! ## Corollary 2.5 (`cor:defect-hs`), per representation -/

/-- The printed `‖V_n(g) − 1‖₂ → 0` for one operator norm asymptotic
representation. -/
def HSVanishes {G : Type} [Group G] (B : OpAlmostRepresentation G) (g : G) : Prop :=
  Filter.Tendsto
    (fun n ↦ Real.sqrt (hsLengthSq (B.model n)
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ))))
    Filter.atTop (nhds 0)

/-- **`cor:defect-hs`, exactly as printed.**  "Let `L ≤ G` have property (T)
and let `(V_n)` be an operator norm asymptotic representation of `G`.  Then
`‖V_n(d) − 1‖₂ → 0` for `d ∈ 𝔇_G(L)`." -/
def PrintedDefectHS : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G), HasKazhdanPropertyT.{0, 0} ↥L →
    ∀ (B : OpAlmostRepresentation G), ∀ d ∈ printedDefect L, HSVanishes B d

theorem manuscriptPrintedDefectHS : PrintedDefectHS := by
  intro G _ L hL B d hd
  rw [HSVanishes, ← isHSNull_iff_tendsto, ← mem_hsKernel_iff]
  exact (mem_opToHSShadowResidual_iff_forall_hsKernel d).1
    (printedDefect_le_opToHSShadowResidual_direct L hL hd) B

/-! ## Theorem 2.7 (`thm:normal-kazhdan`), per representation -/

/-- **`thm:normal-kazhdan`, exactly as printed.**  "Let `G` be countable and
let `K ⊴ G` have property (T).  If every operator norm asymptotic
representation `(V_n)` of `G` satisfies `‖V_n(k) − 1‖₂ → 0` for all `k ∈ K`,
then every corona homomorphism from `G` is trivial on `K`." -/
def PrintedNormalKazhdan : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (K : Subgroup G) [K.Normal],
    HasKazhdanPropertyT.{0, 0} ↥K →
      (∀ (B : OpAlmostRepresentation G), ∀ k ∈ K, HSVanishes B k) →
        ∀ k ∈ K, ManuscriptCoronaMFInvisible k

theorem manuscriptPrintedNormalKazhdan : PrintedNormalKazhdan := by
  intro G _ _ K _ hT hV k hk
  have hK : K ≤ opToHSShadowResidual G := by
    intro x hx
    rw [mem_opToHSShadowResidual_iff_forall_hsKernel]
    intro B
    rw [mem_hsKernel_iff, isHSNull_iff_tendsto]
    exact hV B x hx
  exact mem_manuscriptCoronaMFResidual_iff.1
    (manuscriptNormalKazhdanPrintedRadical G K hT hK hk)

end OneSidedMFRadical
end Manuscript
end GroupApproximation
