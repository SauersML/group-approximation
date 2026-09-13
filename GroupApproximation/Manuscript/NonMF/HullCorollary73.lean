import GroupApproximation.GGT.HullSCTheorem71GeneralLeastArea
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridgeHolds
import GroupApproximation.GGT.HullSCLemma44BoundaryTransfer
import GroupApproximation.GGT.WPDAcylindricalHyperbolicity
import GroupApproximation.Manuscript.NonMF.HullTheorem312Lemma58
import GroupApproximation.Manuscript.NonMF.HullCitationSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull, Corollary 7.3

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, arXiv:1308.4345, §7.
`non_mf_groups_exist.tex` cites Hull's Corollary 7.4 (tex line 1682), and Hull's proof of 7.4
applies this corollary.

> **Corollary 7.3.** Suppose `G ∈ AH` is countable and `S` is suitable with respect to `A`.  Then
> for any `N ∈ ℕ`, there exists a non-virtually-cyclic group `Q` and a surjective homomorphism
> `η : G → Q` such that
> 1. `η|_S` is surjective.
> 2. `η|_{B_A(N)}` is injective.

Hull's alphabet `A : HullGeneratingSet G` carries the hypothesis `G ∈ AH`.

## The proof

This is Hull's proof.  Hull first enlarges `A` (his Lemma 6.1) until it contains two cyclic
subgroups with no common nonzero power.  Here the enlargement comes from results proved on main:

* Corollary 5.7 (`HullCitationSentences.printedHullCorollary57`) gives loxodromic
  `h₀, h₁, h₂ ∈ S`, pairwise non-commensurable, whose cyclic subgroups form a family
  hyperbolically embedded in `(G, A)`;
* merging `⟨h₀⟩` and `⟨h₁⟩` into the base leaves `⟨h₂⟩ ↪h (G, A ∪ ⟨h₀⟩ ∪ ⟨h₁⟩)`
  (`isHypEmbeddedOf_merged`);
* Lemma 5.8 (`HullTheorem312Lemma58.printedHullLemma58`) gives an alphabet `A'` for `G` with
  `A ∪ ⟨h₀⟩ ∪ ⟨h₁⟩ ⊆ A'` and `S` suitable with respect to `A'`.

Enumerate `G = {g₀, g₁, …}`.  Theorem 7.1, applied along the enumeration, gives quotients
`G → Q₀ → Q₁ → ⋯`, each injective on the `(N + 1)`-ball of `Γ(G, A')`, where the image of `gₙ`
lies in the image of `S` (`stage`).  Put `Q = G / ⋃ₙ ker(G → Qₙ)` (`limitKer`).  Then `S` maps onto
`Q`, and `G → Q` is injective on the `(N + 1)`-ball of `Γ(G, A')`.  That ball contains the `N`-ball
of `Γ(G, A)` and every power of `h₀` and of `h₁`.  So the images of `h₀` and `h₁` in `Q` have no
common nonzero power, and `Q` is not virtually cyclic.

Theorem 7.1 enters as `HullSC.HullTowerStatementGeneral`.  On main it is proved from the two
least-area wall statements (`HullSC.hullTowerStatementGeneral_of_leastAreaLeaves`), so
`printedHullCorollary73_of_leastAreaLeaves` takes exactly those two statements.  The embedded
bridge is proved (`HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`), so
`printedHullCorollary73_of_greendlinger` takes the Greendlinger wall alone.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace HullCorollary73

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Merge

variable {G : Type u} [Group G]

/-- An alphabet is determined by its carrier. -/
theorem alphabet_eq_of_carrier_eq {B C : Alphabet G} (hBC : B.carrier = C.carrier) : B = C := by
  obtain ⟨b, hb⟩ := B
  obtain ⟨c, hc⟩ := C
  change b = c at hBC
  subst hBC
  rfl

/-- The merged alphabet `A ∪ ⟨h₀⟩ ∪ ⟨h₁⟩ ∪ ⟨h₂⟩` is the cone-off alphabet of the family. -/
theorem merged_carrier (A : Alphabet G) (h : Fin 3 → G) :
    A.carrier ∪ (Subgroup.zpowers (h 0) : Set G) ∪ (Subgroup.zpowers (h 1) : Set G) ∪
        ⋃ _ : Unit, (Subgroup.zpowers (h 2) : Set G) =
      A.carrier ∪ ⋃ i : Fin 3, (Subgroup.zpowers (h i) : Set G) := by
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, SetLike.mem_coe, exists_const]
  constructor
  · rintro (((hx | hx) | hx) | hx)
    · exact Or.inl hx
    · exact Or.inr ⟨0, hx⟩
    · exact Or.inr ⟨1, hx⟩
    · exact Or.inr ⟨2, hx⟩
  · rintro (hx | ⟨i, hx⟩)
    · exact Or.inl (Or.inl (Or.inl hx))
    · fin_cases i
      · exact Or.inl (Or.inl (Or.inr hx))
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx

/-- `⟨h₂⟩` relative to the base `A ∪ ⟨h₀⟩ ∪ ⟨h₁⟩`. -/
def mergedRelGenSet (A : Alphabet G) (h : Fin 3 → G) : GGT.RelGenSet G Unit where
  base := A.carrier ∪ (Subgroup.zpowers (h 0) : Set G) ∪ (Subgroup.zpowers (h 1) : Set G)
  fam := fun _ => Subgroup.zpowers (h 2)
  symmetricGenerating := by
    show IsSymmetricGeneratingSet (A.carrier ∪ (Subgroup.zpowers (h 0) : Set G) ∪
      (Subgroup.zpowers (h 1) : Set G) ∪ ⋃ _ : Unit, (Subgroup.zpowers (h 2) : Set G))
    rw [merged_carrier A h]
    exact (HullSC.coneOffFamily A (fun i : Fin 3 => Subgroup.zpowers (h i))).symmetricGenerating

theorem merged_alphabet (A : Alphabet G) (h : Fin 3 → G) :
    (mergedRelGenSet A h).alphabet =
      (HullSC.coneOffFamily A (fun i : Fin 3 => Subgroup.zpowers (h i))).alphabet :=
  alphabet_eq_of_carrier_eq (merged_carrier A h)

open scoped Classical in
/-- A letter over `(A ∪ ⟨h₀⟩ ∪ ⟨h₁⟩; ⟨h₂⟩)` read as a letter over `(A; ⟨h₀⟩, ⟨h₁⟩, ⟨h₂⟩)`. -/
noncomputable def mergeLetter (A : Alphabet G) (h : Fin 3 → G) :
    GGT.RelLetter G Unit → GGT.RelLetter G (Fin 3)
  | .base x =>
    if x ∈ A.carrier then .base x else if x ∈ Subgroup.zpowers (h 0) then .comp 0 x else .comp 1 x
  | .comp _ y => .comp 2 y

theorem mergeLetter_val (A : Alphabet G) (h : Fin 3 → G) (a : GGT.RelLetter G Unit) :
    (mergeLetter A h a).val = a.val := by
  cases a with
  | base x =>
    simp only [mergeLetter]
    split_ifs <;> rfl
  | comp _ y => rfl

theorem listVal_mergeLetter (A : Alphabet G) (h : Fin 3 → G) (w : List (GGT.RelLetter G Unit)) :
    GGT.RelLetter.listVal (w.map (mergeLetter A h)) = GGT.RelLetter.listVal w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [GGT.RelLetter.listVal, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, mergeLetter_val]

theorem isLetter_mergeLetter (A : Alphabet G) (h : Fin 3 → G) (a : GGT.RelLetter G Unit)
    (ha : (mergedRelGenSet A h).IsLetter a) :
    (HullSC.coneOffFamily A (fun i : Fin 3 => Subgroup.zpowers (h i))).IsLetter
      (mergeLetter A h a) := by
  cases a with
  | base x =>
    change x ∈ A.carrier ∪ (Subgroup.zpowers (h 0) : Set G) ∪ (Subgroup.zpowers (h 1) : Set G)
      at ha
    simp only [mergeLetter]
    split_ifs with h1 h2
    · exact h1
    · exact h2
    · rcases ha with (ha | ha) | ha
      · exact absurd ha h1
      · exact absurd ha h2
      · exact ha
  | comp _ y => exact ha

theorem avoidsFrom_mergeLetter (A : Alphabet G) (h : Fin 3 → G)
    (w : List (GGT.RelLetter G Unit)) :
    ∀ v : G, GGT.AvoidsFrom (fun _ : Unit => Subgroup.zpowers (h 2)) () w v →
      GGT.AvoidsFrom (fun i : Fin 3 => Subgroup.zpowers (h i)) 2 (w.map (mergeLetter A h)) v := by
  induction w with
  | nil => intro _ _; exact trivial
  | cons a w ih =>
    intro v hav
    change ¬ (GGT.RelLetter.IsCompOf () a ∧ v ∈ Subgroup.zpowers (h 2)) ∧
      GGT.AvoidsFrom (fun _ : Unit => Subgroup.zpowers (h 2)) () w (v * a.val) at hav
    change ¬ (GGT.RelLetter.IsCompOf 2 (mergeLetter A h a) ∧ v ∈ Subgroup.zpowers (h 2)) ∧
      GGT.AvoidsFrom (fun i : Fin 3 => Subgroup.zpowers (h i)) 2 (w.map (mergeLetter A h))
        (v * (mergeLetter A h a).val)
    obtain ⟨ha, hw⟩ := hav
    refine ⟨fun hc => ha ⟨?_, hc.2⟩, ?_⟩
    · obtain ⟨hc, -⟩ := hc
      cases a with
      | base x =>
        simp only [mergeLetter] at hc
        split_ifs at hc
        · exact False.elim hc
        · exact absurd (show (0 : Fin 3) = 2 from hc) (by decide)
        · exact absurd (show (1 : Fin 3) = 2 from hc) (by decide)
      | comp lam y => exact Subsingleton.elim lam ()
    · rw [mergeLetter_val]
      exact ih (v * a.val) hw

theorem relBall_merged_subset (A : Alphabet G) (h : Fin 3 → G) (n : ℕ) :
    (mergedRelGenSet A h).relBall () n ⊆
      (HullSC.coneOffFamily A (fun i : Fin 3 => Subgroup.zpowers (h i))).relBall 2 n := by
  rintro g ⟨hg, w, hw, hval, hav, hlen⟩
  refine ⟨hg, w.map (mergeLetter A h), ?_, ?_, avoidsFrom_mergeLetter A h w 1 hav, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact isLetter_mergeLetter A h a (hw a ha)
  · rw [listVal_mergeLetter]
    exact hval
  · rw [List.length_map]
    exact hlen

/-- If the family `⟨h₀⟩, ⟨h₁⟩, ⟨h₂⟩` is hyperbolically embedded in `(G, A)`, then
`⟨h₂⟩ ↪h (G, A ∪ ⟨h₀⟩ ∪ ⟨h₁⟩)`: the Cayley graphs are the same, and the relative balls of
`⟨h₂⟩` only shrink. -/
theorem isHypEmbeddedOf_merged (A : Alphabet G) (h : Fin 3 → G)
    (hemb : (HullSC.coneOffFamily A
      (fun i : Fin 3 => Subgroup.zpowers (h i))).IsHyperbolicallyEmbedded) :
    GGT.IsHypEmbeddedOf G
      (A.carrier ∪ (Subgroup.zpowers (h 0) : Set G) ∪ (Subgroup.zpowers (h 1) : Set G))
      (Subgroup.zpowers (h 2)) := by
  refine ⟨mergedRelGenSet A h, rfl, rfl, ⟨?_, ?_⟩⟩
  · obtain ⟨δ, hδ⟩ := hemb.hyperbolic
    refine ⟨δ, ?_⟩
    rw [merged_alphabet A h]
    exact hδ
  · intro lam n
    cases lam
    exact (hemb.locallyFinite 2 n).subset (relBall_merged_subset A h n)

#audit_axioms isHypEmbeddedOf_merged

end Merge

section Powers

variable {G : Type u} [Group G]

theorem isOfFinOrder_of_zpow_eq_one {x : G} {n : ℤ} (hn : n ≠ 0) (hx : x ^ n = 1) :
    IsOfFinOrder x :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨n.natAbs, Int.natAbs_pos.mpr hn, pow_natAbs_eq_one.mpr hx⟩

/-- `⟨h₂⟩` is a proper subgroup of `S`: it does not contain `h₀`. -/
theorem zpowers_lt_of_pnc {S : Subgroup G} {h : Fin 3 → G} (hhS : ∀ i, h i ∈ S)
    (hinf : ∀ i, ¬ IsOfFinOrder (h i)) (hpnc : HullSC.PairwiseNonCommensurable h) :
    Subgroup.zpowers (h 2) < S := by
  refine SetLike.lt_iff_le_and_exists.mpr ⟨Subgroup.zpowers_le.mpr (hhS 2), h 0, hhS 0, ?_⟩
  intro hmem
  obtain ⟨q, hq⟩ := Subgroup.mem_zpowers_iff.mp hmem
  by_cases hq0 : q = 0
  · subst hq0
    rw [zpow_zero] at hq
    exact hinf 0 (isOfFinOrder_of_zpow_eq_one (n := 1) one_ne_zero (by rw [zpow_one, ← hq]))
  · exact hpnc 0 2 (by decide) 1 q one_ne_zero hq0 1
      (by rw [one_mul, inv_one, mul_one, zpow_one, hq])

/-- `h₀` and `h₁` have no common nonzero power. -/
theorem eq_zero_of_zpow_eq_zpow {h : Fin 3 → G} (hinf : ∀ i, ¬ IsOfFinOrder (h i))
    (hpnc : HullSC.PairwiseNonCommensurable h) {m k : ℤ} (hmk : h 0 ^ m = h 1 ^ k) :
    m = 0 ∧ k = 0 := by
  by_cases hm : m = 0
  · subst hm
    refine ⟨rfl, ?_⟩
    by_contra hk
    rw [zpow_zero] at hmk
    exact hinf 1 (isOfFinOrder_of_zpow_eq_one hk hmk.symm)
  · by_cases hk : k = 0
    · subst hk
      rw [zpow_zero] at hmk
      exact absurd (isOfFinOrder_of_zpow_eq_one hm hmk) (hinf 0)
    · have hne := hpnc 0 1 (by decide) m k hm hk 1
      rw [one_mul, inv_one, mul_one] at hne
      exact absurd hmk hne

/-- A letter of the alphabet lies in every ball of radius at least one. -/
theorem mem_cayleyBall_of_mem_carrier (A : Alphabet G) {x : G} (hx : x ∈ A.carrier) {R : ℕ}
    (hR : 1 ≤ R) : x ∈ cayleyBall A R := by
  refine HullSC.cayleyBall_subset_of_le_radius A hR ?_
  rw [HullSC.mem_cayleyBall_iff, wordDist_one_left]
  exact_mod_cast wordNorm_le_one_of_mem hx

end Powers

section Stages

variable {G : Type} [Group G]

/-- Theorem 7.1 with no prescribed family, pulling `g` into the image of `S`. -/
noncomputable def firstStage (htower : HullSC.HullTowerStatementGeneral.{0})
    (A : HullGeneratingSet G) {S : Subgroup G} (hS : Suitable A.alphabet S) (R : ℕ) (g : G) :
    HullSC.HullStep A S (fun j : Fin 0 => Fin.elim0 j) R :=
  (htower (S := fun j : Fin 0 => Fin.elim0 j) A hS (fun j : Fin 0 => Fin.elim0 j)
    (fun _ : Fin 1 => g) R).some.step

theorem firstStage_mem_map (htower : HullSC.HullTowerStatementGeneral.{0})
    (A : HullGeneratingSet G) {S : Subgroup G} (hS : Suitable A.alphabet S) (R : ℕ) (g : G) :
    (firstStage htower A hS R g).q g ∈ S.map (firstStage htower A hS R g).q :=
  (htower (S := fun j : Fin 0 => Fin.elim0 j) A hS (fun j : Fin 0 => Fin.elim0 j)
    (fun _ : Fin 1 => g) R).some.mem_map 0

/-- Theorem 7.1 applied to the quotient of a step, pulling the image of `g` into the image
of `S`. -/
noncomputable def towerStep (htower : HullSC.HullTowerStatementGeneral.{0})
    {A : HullGeneratingSet G} {S : Subgroup G} {R : ℕ}
    (s : HullSC.HullStep A S (fun j : Fin 0 => Fin.elim0 j) R) (g : G) :
    HullSC.HullTower s.hullSet (S.map s.q) (fun j : Fin 0 => (Fin.elim0 j : Subgroup G).map s.q)
      (fun _ : Fin 1 => s.q g) R :=
  (htower s.hullSet s.suitable_map s.suitable_map_family (fun _ : Fin 1 => s.q g) R).some

/-- The step followed by `towerStep`. -/
noncomputable def nextStage (htower : HullSC.HullTowerStatementGeneral.{0})
    {A : HullGeneratingSet G} {S : Subgroup G} {R : ℕ}
    (s : HullSC.HullStep A S (fun j : Fin 0 => Fin.elim0 j) R) (g : G) :
    HullSC.HullStep A S (fun j : Fin 0 => Fin.elim0 j) R :=
  s.comp (towerStep htower s g).step

theorem nextStage_q_apply (htower : HullSC.HullTowerStatementGeneral.{0})
    {A : HullGeneratingSet G} {S : Subgroup G} {R : ℕ}
    (s : HullSC.HullStep A S (fun j : Fin 0 => Fin.elim0 j) R) (g x : G) :
    (nextStage htower s g).q x = (towerStep htower s g).step.q (s.q x) :=
  rfl

theorem nextStage_q_eq_one (htower : HullSC.HullTowerStatementGeneral.{0})
    {A : HullGeneratingSet G} {S : Subgroup G} {R : ℕ}
    (s : HullSC.HullStep A S (fun j : Fin 0 => Fin.elim0 j) R) (g x : G) (hx : s.q x = 1) :
    (nextStage htower s g).q x = 1 := by
  rw [nextStage_q_apply, hx]
  exact map_one _

theorem nextStage_mem_map (htower : HullSC.HullTowerStatementGeneral.{0})
    {A : HullGeneratingSet G} {S : Subgroup G} {R : ℕ}
    (s : HullSC.HullStep A S (fun j : Fin 0 => Fin.elim0 j) R) (g : G) :
    (nextStage htower s g).q g ∈ S.map (nextStage htower s g).q := by
  have hmem := (towerStep htower s g).mem_map 0
  rw [Subgroup.map_map] at hmem
  exact hmem

/-- The `n`-th quotient: the images of `e 0, …, e n` lie in the image of `S`. -/
noncomputable def stage (htower : HullSC.HullTowerStatementGeneral.{0})
    (A : HullGeneratingSet G) {S : Subgroup G} (hS : Suitable A.alphabet S) (R : ℕ) (e : ℕ → G) :
    ℕ → HullSC.HullStep A S (fun j : Fin 0 => Fin.elim0 j) R
  | 0 => firstStage htower A hS R (e 0)
  | n + 1 => nextStage htower (stage htower A hS R e n) (e (n + 1))

theorem stage_mem_map (htower : HullSC.HullTowerStatementGeneral.{0})
    (A : HullGeneratingSet G) {S : Subgroup G} (hS : Suitable A.alphabet S) (R : ℕ) (e : ℕ → G)
    (n : ℕ) : (stage htower A hS R e n).q (e n) ∈ S.map (stage htower A hS R e n).q := by
  cases n with
  | zero => exact firstStage_mem_map htower A hS R (e 0)
  | succ n => exact nextStage_mem_map htower (stage htower A hS R e n) (e (n + 1))

theorem stage_q_eq_one_of_le (htower : HullSC.HullTowerStatementGeneral.{0})
    (A : HullGeneratingSet G) {S : Subgroup G} (hS : Suitable A.alphabet S) (R : ℕ) (e : ℕ → G)
    (x : G) {m n : ℕ} (hx : (stage htower A hS R e m).q x = 1) (hmn : m ≤ n) :
    (stage htower A hS R e n).q x = 1 := by
  induction hmn with
  | refl => exact hx
  | step _ ih => exact nextStage_q_eq_one htower _ _ x ih

/-- The union of the kernels of the stages. -/
noncomputable def limitKer (htower : HullSC.HullTowerStatementGeneral.{0})
    (A : HullGeneratingSet G) {S : Subgroup G} (hS : Suitable A.alphabet S) (R : ℕ) (e : ℕ → G) :
    Subgroup G where
  carrier := {x | ∃ n, (stage htower A hS R e n).q x = 1}
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    rw [map_mul, stage_q_eq_one_of_le htower A hS R e x hm (le_max_left m n),
      stage_q_eq_one_of_le htower A hS R e y hn (le_max_right m n), one_mul]
  one_mem' := ⟨0, map_one _⟩
  inv_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, by rw [map_inv, hn, inv_one]⟩

theorem mem_limitKer (htower : HullSC.HullTowerStatementGeneral.{0})
    (A : HullGeneratingSet G) {S : Subgroup G} (hS : Suitable A.alphabet S) (R : ℕ) (e : ℕ → G)
    (x : G) : x ∈ limitKer htower A hS R e ↔ ∃ n, (stage htower A hS R e n).q x = 1 :=
  Iff.rfl

theorem limitKer_normal (htower : HullSC.HullTowerStatementGeneral.{0})
    (A : HullGeneratingSet G) {S : Subgroup G} (hS : Suitable A.alphabet S) (R : ℕ) (e : ℕ → G) :
    (limitKer htower A hS R e).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨n, hn⟩ := (mem_limitKer htower A hS R e x).mp hx
  exact (mem_limitKer htower A hS R e _).mpr
    ⟨n, by rw [map_mul, map_mul, hn, mul_one, map_inv, mul_inv_cancel]⟩

end Stages

/-- **Hull, Corollary 7.3**, verbatim.  `G ∈ AH` with its alphabet `A`; `S` is suitable with
respect to `A`; `B_A(N)` is the ball `cayleyBall A.alphabet N` of `Γ(G, A)`. -/
def PrintedHullCorollary73 : Prop :=
  ∀ {G : Type} [Group G] [Countable G] (A : HullGeneratingSet G) {S : Subgroup G},
    Suitable A.alphabet S → ∀ N : ℕ,
      ∃ (Q : Type) (_ : Group Q) (η : G →* Q), ¬ GGT.IsVirtuallyCyclic Q ∧
        Function.Surjective η ∧ (∀ y : Q, ∃ s ∈ S, η s = y) ∧
          Set.InjOn η (cayleyBall A.alphabet N)

/-- Hull's Corollary 7.3 from Theorem 7.1, along Hull's proof; see the module docstring. -/
theorem printedHullCorollary73_of_tower (htower : HullSC.HullTowerStatementGeneral.{0}) :
    PrintedHullCorollary73 := by
  intro G _ _ A S hS N
  obtain ⟨h, hhS, hlox, hpnc, -, hemb⟩ := HullCitationSentences.printedHullCorollary57 A hS 3
  have hinf : ∀ i, ¬ IsOfFinOrder (h i) := fun i => not_isOfFinOrder_of_isLoxodromic (hlox i)
  obtain ⟨A', hXA', hS'⟩ := HullTheorem312Lemma58.printedHullLemma58
    (A.alphabet.carrier ∪ (Subgroup.zpowers (h 0) : Set G) ∪ (Subgroup.zpowers (h 1) : Set G))
    S (h 2) (hhS 2) (hinf 2) (zpowers_lt_of_pnc hhS hinf hpnc)
    (isHypEmbeddedOf_merged A.alphabet h (hemb (by norm_num)))
  obtain ⟨e, he⟩ := exists_surjective_nat G
  haveI hK : (limitKer htower A' hS' (N + 1) e).Normal := limitKer_normal htower A' hS' (N + 1) e
  have hinj' : Set.InjOn (QuotientGroup.mk' (limitKer htower A' hS' (N + 1) e))
      (cayleyBall A'.alphabet (N + 1)) := by
    intro x hx y hy hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_limitKer] at hxy
    obtain ⟨n, hn⟩ := hxy
    rw [map_mul, map_inv, inv_mul_eq_one] at hn
    exact (stage htower A' hS' (N + 1) e n).injOn hx hy hn
  refine ⟨G ⧸ limitKer htower A' hS' (N + 1) e, inferInstance,
    QuotientGroup.mk' (limitKer htower A' hS' (N + 1) e), ?_,
    QuotientGroup.mk'_surjective (N := limitKer htower A' hS' (N + 1) e), ?_, ?_⟩
  · refine GGT.not_isVirtuallyCyclic_of_no_common_power
      (a := QuotientGroup.mk' (limitKer htower A' hS' (N + 1) e) (h 0))
      (b := QuotientGroup.mk' (limitKer htower A' hS' (N + 1) e) (h 1)) ?_
    intro m k hmk
    rw [← map_zpow, ← map_zpow] at hmk
    have hm0 : h 0 ^ m ∈
        A.alphabet.carrier ∪ (Subgroup.zpowers (h 0) : Set G) ∪ (Subgroup.zpowers (h 1) : Set G) :=
      Or.inl (Or.inr (Subgroup.zpow_mem_zpowers (h 0) m))
    have hk1 : h 1 ^ k ∈
        A.alphabet.carrier ∪ (Subgroup.zpowers (h 0) : Set G) ∪ (Subgroup.zpowers (h 1) : Set G) :=
      Or.inr (Subgroup.zpow_mem_zpowers (h 1) k)
    exact eq_zero_of_zpow_eq_zpow hinf hpnc
      (hinj' (mem_cayleyBall_of_mem_carrier A'.alphabet (hXA' hm0) (Nat.le_add_left 1 N))
        (mem_cayleyBall_of_mem_carrier A'.alphabet (hXA' hk1) (Nat.le_add_left 1 N)) hmk)
  · intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N := limitKer htower A' hS' (N + 1) e) y
    obtain ⟨n, rfl⟩ := he x
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp (stage_mem_map htower A' hS' (N + 1) e n)
    refine ⟨s, hs, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_limitKer]
    exact ⟨n, by rw [map_mul, map_inv, hsx, inv_mul_cancel]⟩
  · refine hinj'.mono ?_
    exact (HullSC.cayleyBall_subset_of_alphabet_subset A.alphabet A'.alphabet
      (fun x hx => hXA' (Set.mem_union_left _ (Set.mem_union_left _ hx))) N).trans
        (HullSC.cayleyBall_subset_of_le_radius A'.alphabet (Nat.le_succ N))

#audit_axioms printedHullCorollary73_of_tower

/-- Hull's Corollary 7.3 from the two least-area wall statements behind Theorem 7.1. -/
theorem printedHullCorollary73_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    PrintedHullCorollary73 :=
  printedHullCorollary73_of_tower
    (HullSC.hullTowerStatementGeneral_of_leastAreaLeaves hgreendlinger hbridge)

#audit_axioms printedHullCorollary73_of_leastAreaLeaves

/-- Hull's Corollary 7.3 from the least-area Greendlinger wall alone: the embedded bridge is
`HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed`. -/
theorem printedHullCorollary73_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    PrintedHullCorollary73 :=
  printedHullCorollary73_of_leastAreaLeaves hgreendlinger
    HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed

#audit_axioms printedHullCorollary73_of_greendlinger

end HullCorollary73
end NonMF
end Manuscript
end GroupApproximation
