import GroupApproximation.GGT.DGOWindmillPath
import GroupApproximation.GGT.DGOWindmillStage
import GroupApproximation.GGT.DGOWindmillCyclic

/-!
# A cyclically reduced element is loxodromic

Eleventh module of the campaign aimed at
`Manuscript.NonMF.TheoremCAssembly.dgoTheorem53` (DGO's Theorem 5.3(b)).

This is the payoff of the whole construction, and the point at which the three
strands of the campaign meet: the geometry of `GGT/DGOWindmillPath.lean`, the
concrete reference sets of `GGT/DGOWindmillStage.lean`, and the word algebra of
`GGT/DGOWindmillCyclic.lean`.

## The argument

Let `g` be the value of a cyclically reduced spelling `t` with at least one
syllable and trailing letter `1`.  Then the syllable list of `gⁿ` is the `n`-fold
concatenation of `t`'s, and it is still reduced --- reducedness of the
concatenation is exactly the wrap-around seam, which is what "cyclically
reduced" means.  So the broken path of `gⁿ` has `n · k` corners, and the length
bound of `between_and_dist_of_reducedList` reads

    ρ · (n·k − 1) ≤ d(P₁, gⁿ · y)

where `P₁` is the first developed apex --- the *same* apex for every `n`, because
the concatenation begins with `t`'s own first syllable.  Moving the basepoint
from `y` to `P₁` costs `d(y, P₁)`, and what is left is

    (ρk)·n − (ρ + d(y, P₁)) ≤ d(P₁, gⁿ · P₁),

which is `HullGeometry.IsLoxodromic` with translation constant `ρk ≥ ρ > 0`.

## Why the additive constant is unavoidable

The length bound is measured from the first apex of the word, and the first apex
moves with the word.  Any statement of the form `ρ n ≤ d(x, gⁿ · x)` at a fixed
`x` would have to absorb `d(x, P₁)`, which no hypothesis bounds.  That is the
structural reason the windmill's fifth axiom carries `IsLoxodromic` rather than a
bare translation bound, and this module is where the need becomes concrete.

## The basepoint of the induction is `y`, not the apex

`between_and_dist_of_reducedList` needs its starting point to be reached from
the first apex *through the reference set*, and the first apex is `55δ` from that
set --- so the apex cannot be its own starting point.  A point of the windmill
can: `w.pre⁻¹ • y` lies in `W` because the windmill group preserves `W`, and `W`
is inside every reference set.  Hence `y`, an apex of `W`, is the basepoint of
every application, and the translation bound is transported to `P₁` afterwards.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- **A cyclically reduced element of the stage group is loxodromic.**

The hypotheses are the campaign's standing ones plus a windmill `W`; the new
apices, the reference sets and the stage group are the concrete choices of
`GGT/DGOWindmillStage.lean`, so nothing here has to be supplied by the caller
beyond the spelling itself. -/
theorem isLoxodromic_of_cyclicallyReduced {δ ρ : ℝ} (hδ : 0 < δ)
    (hρ : 200 * δ ≤ ρ) (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X)
    {C : Set X} {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) (hsep : IsSeparated C ρ) {W : Set X}
    (hW : IsWindmill G X δ C Rot W) {t : Spelling G X}
    (ht : t.IsValid Rot (newApices δ C W) (windmillGroup C Rot W))
    (htcr : t.CyclicallyReduced) (httail : t.tail = 1) (htne : t.sylls ≠ []) :
    ∃ x : X, IsLoxodromic t.eval x := by
  have hδ0 : (0 : ℝ) ≤ δ := le_of_lt hδ
  have hρ0 : (0 : ℝ) < ρ := by linarith
  obtain ⟨y, -, hyW⟩ := hW.apex_mem
  -- the first syllable, and the apex it develops to
  obtain ⟨w, l', hsylls⟩ : ∃ w l', t.sylls = w :: l' := by
    -- `cases hl : e` REWRITES the goal, which here mentions the scrutinee, so
    -- the cons branch's goal is already `∃ w l', a :: b = w :: l'` and `rfl`
    -- is what it wants -- `hl` would be the equation at the un-rewritten goal.
    cases hl : t.sylls with
    | nil => exact absurd hl htne
    | cons a b => exact ⟨a, b, rfl⟩
  have hwmem : w ∈ t.sylls := by
    rw [hsylls]
    exact List.mem_cons_self
  have hw : Syll.IsValid Rot (newApices δ C W) (windmillGroup C Rot W) w :=
    ht.sylls_valid w hwmem
  -- the hypotheses of the broken-path induction, all discharged by the stage
  have hC₁C : newApices δ C W ⊆ C := newApices_subset
  have hSqc : ∀ d ∈ newApices δ C W,
      IsQuasiconvexSet (stageRef δ C W d) (12 * δ) :=
    fun d _ => isQuasiconvexSet_stageRef hδ0 hhyp hgeo hW d
  have hSfar : ∀ d ∈ newApices δ C W, ∀ z ∈ stageRef δ C W d,
      55 * δ ≤ dist d z :=
    fun d hd => le_dist_of_mem_stageRef hδ0 hρ hW hsep hd
  have hC₁S : ∀ d ∈ newApices δ C W, ∀ e ∈ newApices δ C W, e ≠ d →
      e ∈ stageRef δ C W d :=
    fun _ _ e he hne => mem_stageRef_of_mem_newApices he hne
  have hGWC₁ : ∀ a ∈ windmillGroup C Rot W, ∀ d ∈ newApices δ C W,
      a • d ∈ newApices δ C W :=
    fun _ ha _ hd => smul_mem_newApices hfam hW ha hd
  have hy : ∀ d ∈ newApices δ C W, ∃ z ∈ stageRef δ C W d, Between d z y :=
    fun d _ => ⟨y, subset_spokeSet hyW, between_self_right d y⟩
  -- the starting point of every application
  have hyinv : w.pre⁻¹ • y ∈ W :=
    hW.invariant w.pre⁻¹ (inv_mem hw.pre_mem) y hyW
  have hstart : ∃ z ∈ stageRef δ C W w.dir, Between w.dir z (w.pre⁻¹ • y) :=
    ⟨w.pre⁻¹ • y, subset_spokeSet hyinv, between_self_right _ _⟩
  -- the syllable count
  have hd0 : (0 : ℝ) ≤ dist y (w.pre • w.dir) := dist_nonneg
  have hkpos : (1 : ℕ) ≤ t.sylls.length := by
    rw [hsylls]
    simp
  have hk1 : (1 : ℝ) ≤ (t.sylls.length : ℝ) := by exact_mod_cast hkpos
  refine ⟨w.pre • w.dir, ρ * (t.sylls.length : ℝ),
    mul_pos hρ0 (by linarith), ρ + dist y (w.pre • w.dir), by linarith, ?_⟩
  intro n
  cases n with
  | zero =>
      have h1 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
      have h2 : (t.eval ^ (0 : ℕ)) • (w.pre • w.dir) = w.pre • w.dir := by
        rw [pow_zero, one_smul]
      rw [h1, h2, dist_self, mul_zero]
      linarith
  | succ m =>
      -- the syllable list of the `(m+1)`-st power begins with the same syllable
      have hflat : (List.replicate (m + 1) t.sylls).flatten
          = w :: (l' ++ (List.replicate m t.sylls).flatten) := by
        rw [List.replicate_succ, List.flatten_cons, hsylls, List.cons_append]
      have hvalidL : ∀ v ∈ w :: (l' ++ (List.replicate m t.sylls).flatten),
          Syll.IsValid Rot (newApices δ C W) (windmillGroup C Rot W) v := by
        intro v hv
        rw [← hflat, List.mem_flatten] at hv
        obtain ⟨u, hu, hvu⟩ := hv
        rw [List.eq_of_mem_replicate hu] at hvu
        exact ht.sylls_valid v hvu
      have hredL : ReducedList (w :: (l' ++ (List.replicate m t.sylls).flatten)) := by
        rw [← hflat]
        exact reducedList_flatten_replicate htne htcr.1 htcr.2 (m + 1)
      obtain ⟨-, hbound⟩ :=
        between_and_dist_of_reducedList hδ hhyp hgeo hfam hvr hsep hC₁C hSqc
          hSfar hC₁S hGWC₁ hy (l' ++ (List.replicate m t.sylls).flatten) w
          hvalidL hredL y hstart
      -- the endpoint is `g ^ (m+1)` applied to the basepoint
      have hev : listEval (w :: (l' ++ (List.replicate m t.sylls).flatten))
          = t.eval ^ (m + 1) := by
        rw [← hflat, listEval_flatten_replicate, Spelling.eval_def, httail,
          mul_one]
      rw [hev] at hbound
      -- the corner count
      have hLlen : (((l' ++ (List.replicate m t.sylls).flatten).length : ℕ) : ℝ)
          = (t.sylls.length : ℝ) * ((m : ℝ) + 1) - 1 := by
        have h1 : (l' ++ (List.replicate m t.sylls).flatten).length
            = l'.length + m * t.sylls.length := by
          rw [List.length_append, length_flatten_replicate]
        have h2 : t.sylls.length = l'.length + 1 := by
          rw [hsylls, List.length_cons]
        rw [h1, h2]
        push_cast
        ring
      rw [hLlen] at hbound
      -- transport the bound from `y` to the apex
      have htri := dist_triangle (w.pre • w.dir)
        ((t.eval ^ (m + 1)) • (w.pre • w.dir)) ((t.eval ^ (m + 1)) • y)
      have hiso : dist ((t.eval ^ (m + 1)) • (w.pre • w.dir))
          ((t.eval ^ (m + 1)) • y) = dist (w.pre • w.dir) y :=
        hfam.isometric (t.eval ^ (m + 1)) (w.pre • w.dir) y
      have hcomm : dist (w.pre • w.dir) y = dist y (w.pre • w.dir) :=
        dist_comm _ _
      have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by simp
      rw [hcast]
      linarith

/-- **The next-stage group already has the rotation-or-loxodromic
dichotomy.**

Cyclic reduction gives three outcomes.  An element conjugate into the old
windmill group is handled by the old windmill's dichotomy, an element
conjugate into a rotation at a new apex is already in the rotation branch,
and a nonempty cyclically reduced spelling is loxodromic by
`isLoxodromic_of_cyclicallyReduced`.  In either loxodromic case, conjugacy
invariance transports the conclusion back to the original element.

This is the algebraic/axis half of DGO's Proposition 5.12.  Constructing the
enlarged windmill remains a separate geometric step: it must identify its
windmill group with this `stepGroup` (or at least bound it by this group) and
prove quasiconvexity, invariance, and the far-apex clause. -/
theorem rotation_or_loxodromic_of_mem_stepGroup {δ ρ : ℝ} (hδ : 0 < δ)
    (hρ : 200 * δ ≤ ρ) (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X)
    {C : Set X} {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) (hsep : IsSeparated C ρ) {W : Set X}
    (hW : IsWindmill G X δ C Rot W) {g : G}
    (hg : g ∈ stepGroup Rot (newApices δ C W) (windmillGroup C Rot W)) :
    (∃ (a : G) (d : X),
      a ∈ stepGroup Rot (newApices δ C W) (windmillGroup C Rot W) ∧
        d ∈ C ∧ (d ∈ W ∨ d ∈ newApices δ C W) ∧
          a * g * a⁻¹ ∈ Rot d) ∨
      ∃ x : X, IsLoxodromic g x := by
  have hconj : ∀ (a : G) (d : X), d ∈ newApices δ C W →
      ∀ b ∈ Rot d, a * b * a⁻¹ ∈ Rot (a • d) := by
    intro a d hd b hb
    apply (hfam.rot_equivariant a (newApices_subset hd) (a * b * a⁻¹)).2
    have heq : a⁻¹ * (a * b * a⁻¹) * a = b := by group
    rwa [heq]
  have hfree : ∀ a ∈ windmillGroup C Rot W, ∀ d ∈ newApices δ C W,
      a • d = d → a = 1 :=
    eq_one_of_smul_eq_apex hδ hhyp hgeo hfam hvr hW
      (fun d hd => ⟨newApices_subset hd, not_mem_of_mem_newApices hd⟩)
  have hlox_of_conj : ∀ (a h : G) (x : X), IsLoxodromic (a * h * a⁻¹) x →
      ∃ y : X, IsLoxodromic h y := by
    intro a h x hlox
    have hback := isLoxodromic_conj hfam.isometric (a := a⁻¹) hlox
    have heq : a⁻¹ * (a * h * a⁻¹) * (a⁻¹)⁻¹ = h := by group
    rw [heq] at hback
    exact ⟨x, hback⟩
  rcases isCyclicOutcome_of_mem_stepGroup hconj hfree hg with
      ⟨a, haStep, ha⟩ | ⟨a, d, haStep, hd, ha⟩ |
        ⟨a, t, haStep, ht, htcr, httail, htne, hte⟩
  · rcases hW.dichotomy (a * g * a⁻¹) ha with
      ⟨d, hdC, hdW, hrot⟩ | ⟨x, hlox⟩
    · exact Or.inl ⟨a, d, haStep, hdC, Or.inl hdW, hrot⟩
    · exact Or.inr (hlox_of_conj a g x hlox)
  · exact Or.inl ⟨a, d, haStep, newApices_subset hd, Or.inr hd, ha⟩
  · obtain ⟨x, hlox⟩ :=
      isLoxodromic_of_cyclicallyReduced hδ hρ hhyp hgeo hfam hvr hsep hW
        ht htcr httail htne
    rw [hte] at hlox
    exact Or.inr (hlox_of_conj a g x hlox)

end DGOWindmill
end GroupApproximation
