import GroupApproximation.GGT.DGOWindmillSpelling
import GroupApproximation.GGT.DGOWindmillCorner

/-!
# The broken path of a reduced word is geodesic

Ninth module of the campaign aimed at
`Manuscript.NonMF.TheoremCDebts.dgoTheorem53` (DGO's Theorem 5.3(b)).

This is where the word algebra of `GGT/DGOWindmillSpelling.lean` and the
geometry of `GGT/DGOWindmillCorner.lean` meet, and it is the content of DGO's
Lemma 5.16: the broken path through the developed apices of a reduced word is a
geodesic.

## What replaces the Bass-Serre tree

DGO prove this by building the Bass-Serre tree of a graph of groups, an
isomorphism `f : T_Λ → Γ` onto a graph of translates, and reading the path off a
segment of the tree.  Mathlib has no Bass-Serre theory at the pin, and none is
needed: the tree is bookkeeping for "reduced word", and the induction below does
the same bookkeeping on the word itself.

The induction is on the syllable list, and the invariant is the one thing that
makes it close: **the corner lemma is applied with the far endpoint of the
already-built path, not merely with the previous apex.**  Translating the `j`-th
corner into standard position at its own apex `d_j`, the incoming direction is
the previous developed apex and the outgoing is `b_j · (p_{j+1} • d_{j+1})`, and
*both* are apices of `C₁` distinct from `d_j` --- the first by the induction
hypothesis read at `x := d_j`, the second by reducedness.  That is exactly the
shape `DGOWindmill.between_of_corner` consumes, with the reference set `S d_j`
containing every apex of `C₁` other than `d_j`.

Reducedness is used exactly once per corner, and only through
`Spelling.Seam`: `t.pre • t.dir ≠ w.dir`.  Nothing else about the word matters.

## Two conclusions, one induction

`Between x P₁ E` is what the next corner consumes, and
`ρ · (length) ≤ d(P₁, E)` is what the axis needs.  They are proved together
because the second's inductive step needs the first at the translated basepoint:
the chain `P₁, P₂, E` is the induction hypothesis moved by `p₁ b₁`, and
consecutive developed apices are distinct apices of `C`, hence `ρ` apart by the
separation of the family.

The length bound is measured **from the first apex**, not from `x`.  That is
deliberate and it is why the windmill's fifth axiom has to carry
`IsLoxodromic`'s additive constant: moving the bound to a fixed basepoint costs
`2 d(x, P₁)`, and no bound of the form `ρ n ≤ d(x, gⁿ · x)` survives that move.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- **DGO's Lemma 5.16, with the length bound the axis needs.**

For a valid reduced syllable list `w :: l`, a point `x` reached from the first
apex through the reference set, and an endpoint `y` reachable from every apex:
the first developed apex lies between `x` and the endpoint of the word, and the
endpoint is at least `ρ · l.length` from that apex.

The hypotheses on `S` are exactly what `between_of_corner` spends: each `S d` is
`12δ`-quasiconvex, sits `55δ` from `d`, and contains every apex of `C₁` other
than `d`.  The growth step supplies them with `S d` a spoke set. -/
theorem between_and_dist_of_reducedList {δ ρ : ℝ} (hδ : 0 < δ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X) {C : Set X}
    {Rot : X → Subgroup G} (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X δ C Rot) (hsep : IsSeparated C ρ)
    {C₁ : Set X} (hC₁C : C₁ ⊆ C) {S : X → Set X}
    (hSqc : ∀ d ∈ C₁, IsQuasiconvexSet (S d) (12 * δ))
    (hSfar : ∀ d ∈ C₁, ∀ z ∈ S d, 55 * δ ≤ dist d z)
    (hC₁S : ∀ d ∈ C₁, ∀ e ∈ C₁, e ≠ d → e ∈ S d)
    {GW : Subgroup G} (hGWC₁ : ∀ a ∈ GW, ∀ d ∈ C₁, a • d ∈ C₁)
    {y : X} (hy : ∀ d ∈ C₁, ∃ z ∈ S d, Between d z y) :
    ∀ (l : List (Syll G X)) (w : Syll G X),
      (∀ v ∈ w :: l, Syll.IsValid Rot C₁ GW v) → ReducedList (w :: l) →
        ∀ x : X, (∃ z ∈ S w.dir, Between w.dir z (w.pre⁻¹ • x)) →
          Between x (w.pre • w.dir) (listEval (w :: l) • y) ∧
            ρ * (l.length : ℝ)
              ≤ dist (w.pre • w.dir) (listEval (w :: l) • y) := by
  intro l
  induction l with
  | nil =>
      intro w hvalid _ x hx
      have hw : Syll.IsValid Rot C₁ GW w := hvalid w (by simp)
      have hdirC : w.dir ∈ C := hC₁C hw.dir_mem
      obtain ⟨z, hzS, hzb⟩ := hx
      obtain ⟨z', hz'S, hz'b⟩ := hy w.dir hw.dir_mem
      have hcorner := between_of_corner hδ hhyp hgeo hfam hvr hdirC hw.rot_mem
        hw.rot_ne_one (hSqc w.dir hw.dir_mem) (hSfar w.dir hw.dir_mem) hzS hzb
        hz'S hz'b
      have htr := smul_between hfam.isometric w.pre hcorner
      rw [smul_inv_smul, ← mul_smul] at htr
      have hEeq : listEval (w :: ([] : List (Syll G X))) • y
          = (w.pre * w.rot) • y := by
        rw [listEval_cons, listEval_nil, mul_one]
      rw [hEeq]
      refine ⟨htr, ?_⟩
      have hlen : ((([] : List (Syll G X)).length : ℕ) : ℝ) = 0 := by simp
      rw [hlen, mul_zero]
      exact dist_nonneg
  | cons t l' ih =>
      intro w hvalid hred x hx
      have hw : Syll.IsValid Rot C₁ GW w := hvalid w (by simp)
      have ht : Syll.IsValid Rot C₁ GW t := hvalid t (by simp)
      have hdirC : w.dir ∈ C := hC₁C hw.dir_mem
      -- `ReducedList` and `Seam` are `def`s; ascribe before destructuring so
      -- that no tactic has to unfold them at reducible transparency.
      have hredC : List.IsChain Seam (w :: t :: l') := hred
      obtain ⟨hseam, hredtail⟩ := List.isChain_cons_cons.mp hredC
      have hredtail' : ReducedList (t :: l') := hredtail
      have hseam' : t.pre • t.dir ≠ w.dir := hseam
      have htdirC₁ : t.pre • t.dir ∈ C₁ :=
        hGWC₁ t.pre ht.pre_mem t.dir ht.dir_mem
      -- the induction hypothesis, read from the current apex
      have hxtail : ∃ z ∈ S t.dir, Between t.dir z (t.pre⁻¹ • w.dir) := by
        refine ⟨t.pre⁻¹ • w.dir, ?_, between_self_right _ _⟩
        refine hC₁S t.dir ht.dir_mem (t.pre⁻¹ • w.dir)
          (hGWC₁ t.pre⁻¹ (inv_mem ht.pre_mem) w.dir hw.dir_mem) ?_
        intro heq
        apply hseam'
        rw [← heq, smul_inv_smul]
      obtain ⟨ihb, ihlen⟩ :=
        ih t (fun v hv => hvalid v (List.mem_cons_of_mem w hv)) hredtail' w.dir
          hxtail
      -- the corner at the current apex
      obtain ⟨z, hzS, hzb⟩ := hx
      have hz' : t.pre • t.dir ∈ S w.dir :=
        hC₁S w.dir hw.dir_mem (t.pre • t.dir) htdirC₁ hseam'
      have hcorner := between_of_corner hδ hhyp hgeo hfam hvr hdirC hw.rot_mem
        hw.rot_ne_one (hSqc w.dir hw.dir_mem) (hSfar w.dir hw.dir_mem) hzS hzb
        hz' ihb
      have htr := smul_between hfam.isometric w.pre hcorner
      rw [smul_inv_smul] at htr
      have hEeq : listEval (w :: t :: l') • y
          = w.pre • w.rot • (listEval (t :: l') • y) := by
        rw [listEval_cons, mul_smul, mul_smul]
      rw [hEeq]
      refine ⟨htr, ?_⟩
      -- the chain from the first apex to the second, and the gap between them
      have hrotfix : w.rot • w.dir = w.dir := hfam.rot_fix hdirC w.rot hw.rot_mem
      have hchain0 := smul_between hfam.isometric w.rot ihb
      rw [hrotfix] at hchain0
      have hchain := smul_between hfam.isometric w.pre hchain0
      unfold Between at hchain
      have hd2 : dist (w.pre • w.rot • (t.pre • t.dir))
            (w.pre • w.rot • (listEval (t :: l') • y))
          = dist (t.pre • t.dir) (listEval (t :: l') • y) := by
        rw [hfam.isometric w.pre (w.rot • (t.pre • t.dir))
            (w.rot • (listEval (t :: l') • y)),
          hfam.isometric w.rot (t.pre • t.dir) (listEval (t :: l') • y)]
      have hP₁C : w.pre • w.dir ∈ C := hfam.apex_smul w.pre hdirC
      have hP₂C : w.pre • w.rot • (t.pre • t.dir) ∈ C :=
        hfam.apex_smul w.pre (hfam.apex_smul w.rot (hC₁C htdirC₁))
      have hne : w.pre • w.dir ≠ w.pre • w.rot • (t.pre • t.dir) := by
        intro heq
        have h1 : w.dir = w.rot • (t.pre • t.dir) := smul_left_cancel w.pre heq
        apply hseam'
        have h2 : w.rot • w.dir = w.rot • (t.pre • t.dir) := by
          rw [hrotfix]; exact h1
        exact (smul_left_cancel w.rot h2).symm
      have hgap : ρ ≤ dist (w.pre • w.dir) (w.pre • w.rot • (t.pre • t.dir)) :=
        hsep _ hP₁C _ hP₂C hne
      have hlen : (((t :: l').length : ℕ) : ℝ) = (l'.length : ℝ) + 1 := by simp
      rw [hlen]
      linarith

end DGOWindmill
end GroupApproximation
