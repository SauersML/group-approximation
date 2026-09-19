import GroupApproximation.GGT.WPDDGOReduction

/-!
# Dahmani--Guirardel--Osin's Theorem 6.11 is false as printed

> **Theorem 6.11.**  Suppose that a group `G` is weakly hyperbolic relative to
> `X` and `{H_λ}`.  Assume that for some `λ` the following hold. (a) `H_λ` is
> unbounded with respect to `d̂_λ`.  (b) There exists `a ∈ X` such that
> `|H_λ^a ∩ H_λ| < ∞`.  Then there exists `h ∈ H_λ` such that `ah` is a
> loxodromic element satisfying the WPD condition with respect to the action of
> `G` on `Γ(G, X ⊔ H)`.

Neither hypothesis says `a ∉ H_λ`, and without it the conclusion fails.  Their
proof needs it: it applies their Lemma 4.21 to the word `(ah)^N`, whose
condition `(W3)` --- *if `h₁ x h₂` is a subword with `x ∈ X`, `h₁ ∈ H_λ`,
`h₂ ∈ H_μ`, then either `λ ≠ μ` or the element represented by `x` does not
belong to `H_λ`* --- reads, for that word, exactly `a ∉ H_λ`.  The gap is in the
statement only; the theorem is used just once, through Corollary 6.12, where `a`
is taken in `G \ H`.

`GGT.DGOTheorem611` transcribed the printed hypotheses faithfully, so it is
false, and `not_dgoTheorem611` below proves that.
`GGT.dgoTheorem611'` is the repaired statement, and it is a theorem.

## The model

`G` any nontrivial finite group, `X = {1}`, `H = G`.

Every hypothesis holds.  `X ∪ H = G` is symmetric and generates, so this is a
relative generating set.  `Γ(G, X ⊔ H)` has diameter one, hence is hyperbolic
--- Gromov products are bounded by one, so the four-point condition holds at
`δ = 1`.  Every relative ball is a subset of a finite group, so `d̂` is locally
finite: the family is hyperbolically embedded.  Clause (b) holds because
`{h ∈ H | a⁻¹ h a ∈ H} = G` is finite.

Clause (a) holds for the reason that makes the model work at all.  Every vertex
of `Γ(G, X ⊔ H)` lies in `H`, since `H = G`, so `AvoidsFrom` forbids *every*
`H`-letter: an admissible path is spelled by letters of `X = {1}` and therefore
stays at `1`.  Every relative ball is `{1}`, so no ball contains `H` --- `d̂`
takes the value `∞` on `H \ {1}`, which is exactly the phenomenon
Dahmani--Guirardel--Osin's Remark 6.10 records and the reason `DGOTheorem611`
states unboundedness as `∀ n, ¬ (H ⊆ relBall n)` rather than metrically.

The conclusion fails for the reason it must: `a ∈ H`, so `a h ∈ H` for every
`h ∈ H`, and `RelGenSet.not_isLoxodromic_of_mem_fam` --- coning off `H` makes
every element of `H` elliptic --- forbids `a h` from being loxodromic.

The model is as degenerate as it can be, and that is the point: the missing
hypothesis is the only thing standing between the printed statement and it.  It
cannot be made less degenerate.  A finite `H` unbounded in `d̂` forces
`⟨X⟩ ⊆ H`: an admissible path leaving `H` may read `H`-letters, and conjugating
back reaches the rest of `H`.  So `H = ⟨X ∪ H⟩ = G` and `G` is finite, and then
`a ∈ X ⊆ G = H` whatever `X` is.
-/

namespace GroupApproximation
namespace GGT
namespace DGOTheorem611Refutation

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- The two-element group, written multiplicatively. -/
abbrev Two : Type := Multiplicative (ZMod 2)

/-- Its nontrivial element. -/
abbrev tau : Two := Multiplicative.ofAdd (1 : ZMod 2)

theorem tau_ne_one : tau ≠ 1 := by
  intro hcon
  simp only [ofAdd_eq_one] at hcon
  exact absurd hcon (by decide)

/-- **The model**: `X = {1}` and `H = G`, over the two-element group. -/
def modelD : RelGenSet Two Unit where
  base := {1}
  fam := fun _ => ⊤
  symmetricGenerating := by
    have hall : ∀ y : Two,
        y ∈ ({1} : Set Two) ∪ ⋃ _ : Unit, ((⊤ : Subgroup Two) : Set Two) :=
      fun y => Or.inr (Set.mem_iUnion.mpr ⟨(), Subgroup.mem_top _⟩)
    refine ⟨fun y _ => hall _, ?_⟩
    rw [eq_top_iff]
    intro y _
    exact Subgroup.subset_closure (hall y)

/-- Every element is a letter: the family is everything. -/
theorem mem_alphabet (y : Two) : y ∈ modelD.alphabet.carrier := by
  show y ∈ modelD.base ∪ ⋃ lam : Unit, ((modelD.fam lam : Subgroup Two) : Set Two)
  exact Or.inr (Set.mem_iUnion.mpr ⟨(), Subgroup.mem_top _⟩)

/-- `Γ(G, X ⊔ H)` has diameter at most one. -/
theorem dist_le_one (y z : Cayley modelD.alphabet) : dist y z ≤ 1 := by
  have hnorm : wordNorm modelD.alphabet.carrier
      ((Cayley.val y)⁻¹ * Cayley.val z) ≤ 1 :=
    wordNorm_le_one_of_mem (mem_alphabet _)
  have hd : wordDist modelD.alphabet.carrier (Cayley.val y) (Cayley.val z) ≤ 1 :=
    hnorm
  rw [Cayley.dist_eq]
  exact_mod_cast hd

/-- A space of diameter one is hyperbolic: Gromov products lie in `[0,1]`. -/
theorem isHyperbolicSpace_model : IsHyperbolicSpace 1 (Cayley modelD.alphabet) := by
  intro w y z t
  have hle : gromovProduct y z w ≤ 1 := by
    unfold gromovProduct
    have h1 := dist_le_one y w
    have h2 := dist_le_one z w
    have h3 : (0 : ℝ) ≤ dist y z := dist_nonneg
    linarith
  have hmin : min (gromovProduct y z w) (gromovProduct z t w) ≤ 1 :=
    le_trans (min_le_left _ _) hle
  have hnn : 0 ≤ gromovProduct y t w := gromovProduct_nonneg _ _ _
  linarith

/-- **Every admissible path stays at `1`.**  Every vertex lies in `H`, so
`AvoidsFrom` forbids every `H`-letter, and the only `X`-letter is `1`. -/
theorem listVal_eq_one_of_avoidsFrom :
    ∀ (w : List (RelLetter Two Unit)) (v : Two),
      (∀ y ∈ w, modelD.IsLetter y) → AvoidsFrom modelD.fam () w v →
        RelLetter.listVal w = 1 := by
  intro w
  induction w with
  | nil =>
      intro _ _ _
      exact RelLetter.listVal_nil
  | cons b t ih =>
      rintro v hlet ⟨h0, htail⟩
      have hval : b.val = 1 := by
        cases b with
        | base y =>
            have hy : modelD.IsLetter (RelLetter.base y) :=
              hlet (RelLetter.base y) (by simp)
            exact hy
        | comp mu y =>
            cases mu
            exact absurd ⟨rfl, Subgroup.mem_top v⟩ h0
      have htv : RelLetter.listVal t = 1 :=
        ih (v * b.val) (fun y hy => hlet y (List.mem_cons_of_mem b hy)) htail
      simp only [RelLetter.listVal, List.map_cons, List.prod_cons] at htv ⊢
      rw [hval, htv, one_mul]

/-- Every relative ball is `{1}`. -/
theorem relBall_subset_one (n : ℕ) : modelD.relBall () n ⊆ ({1} : Set Two) := by
  rintro y ⟨-, w, hlet, hval, havoid, -⟩
  rw [Set.mem_singleton_iff, ← hval]
  exact listVal_eq_one_of_avoidsFrom w 1 hlet havoid

/-- Clause (a): `H` is unbounded, no relative ball containing it. -/
theorem not_subset_relBall (n : ℕ) :
    ¬ ((modelD.fam () : Subgroup Two) : Set Two) ⊆ modelD.relBall () n := by
  intro hsub
  have hmem : tau ∈ ((modelD.fam () : Subgroup Two) : Set Two) :=
    Subgroup.mem_top _
  have h1 : tau ∈ ({1} : Set Two) := relBall_subset_one n (hsub hmem)
  exact tau_ne_one (Set.mem_singleton_iff.mp h1)

/-- The family is hyperbolically embedded. -/
theorem isHyperbolicallyEmbedded_model : modelD.IsHyperbolicallyEmbedded where
  hyperbolic := ⟨1, isHyperbolicSpace_model⟩
  locallyFinite := fun _ _ => Set.toFinite _

/-- **Dahmani--Guirardel--Osin's Theorem 6.11 as printed is false.**  Its `a` is
asked for in `X` and nowhere required to lie outside `H_λ`; over the model above
the letter `1` satisfies every hypothesis and no `a h` is loxodromic, `a h`
lying in `H` and `H` being elliptic on its own cone-off. -/
theorem not_dgoTheorem611 : ¬ DGOTheorem611.{0} := by
  intro hthm
  obtain ⟨y, -, hlox⟩ := hthm Two modelD isHyperbolicallyEmbedded_model
    not_subset_relBall 1 rfl (Set.toFinite _)
  exact modelD.not_isLoxodromic_of_mem_fam () (Subgroup.mem_top (1 * y)) hlox

end DGOTheorem611Refutation
end GGT
end GroupApproximation
