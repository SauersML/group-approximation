import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindSixIter
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: sign-keeping excision steps that are always available

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-64.

Route.  `gfaceWindSix_PosStep` asks, at a reached pinched state `(c, g)` with `g ≥ 0`, for an
excision step keeping `g ≥ 0`.  Two kinds of step do so for sign reasons alone.

* A **negative lobe**: a simple lobe `W` (inner stretch `A`, or wrapping stretch `q ++ p`)
  whose side contains the base face `o`.  Then `wind_W = ind_W - 1 ≤ 0`, so `g - wind_W ≥ g`
  (`gfaceWindSeven_neg_nonneg`, `gfaceWindSeven_inner_neg`, `gfaceWindSeven_wrap_neg`).
* A **two-lobe split** `c = p ++ A ++ q` with both `A` and `q ++ p` simple.  If `o` lies on the
  side of `A`, excise `A` (negative lobe).  Otherwise excise `q ++ p`: the new state has the
  simple walk `A`, so by `gfaceWindSix_eq_wind` its `g` is `wind_A = ind_A ≥ 0`
  (`gfaceWindSeven_two`).

## Truth check

Scratchpad `gl-p10-64/seven.py` classifies every reached pinched state with `g ≥ 0` (models
of `gl-p10-49/gface.py`, integer reach of `gl-p10-55/wind.py`).  Of 1145707 states (random
seed 1), 824863 have a negative lobe and 183989 more a two-lobe split; the residual 136855 all
have a sign-keeping step (0 failures).  Seed 3: 1115420 / 818420 / 182319 / 114681, 0
failures.  Witness seed 2: 1109170 / 809673 / 144008 / 155489, 0 failures.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **Subtracting a negative winding function keeps `g ≥ 0`**: when the base face lies on the
side of `W`, the normalised winding function of `W` is `≤ 0`. -/
theorem gfaceWindSeven_neg_nonneg {M : CombMap.{v}} {o : M.Face} {W : List M.Dart}
    {g : M.Face → ℤ} (hpos : ∀ f, 0 ≤ g f)
    (ho : o ∈ SimpleClosedWalkSides.sideFaces M W) :
    ∀ f, 0 ≤ g f - gfaceWind_wind M o W f := by
  intro f
  have h1 : gfaceWind_ind (SimpleClosedWalkSides.sideFaces M W) o = 1 := gfaceWind_ind_pos ho
  have h2 := hpos f
  have h3 : gfaceWind_wind M o W f = gfaceWind_ind (SimpleClosedWalkSides.sideFaces M W) f -
      gfaceWind_ind (SimpleClosedWalkSides.sideFaces M W) o := rfl
  rcases gfaceWindSix_ind01 (SimpleClosedWalkSides.sideFaces M W) f with h | h <;> linarith

/-- **Excising an inner negative lobe** keeps `g ≥ 0`. -/
theorem gfaceWindSeven_inner_neg {M : CombMap.{v}} {o : M.Face} {c p A q : List M.Dart}
    {g : M.Face → ℤ} (hpos : ∀ f, 0 ≤ g f) (hseg : c = p ++ A ++ q)
    (hA : IsSimpleClosedWalk M A) (hoA : o ∈ SimpleClosedWalkSides.sideFaces M A) :
    ∃ t : List M.Dart × (M.Face → ℤ), gfaceWind_Step M o (c, g) t ∧ ∀ f, 0 ≤ t.2 f :=
  ⟨(p ++ q, fun f => g f - gfaceWind_wind M o A f), ⟨p, A, q, hseg, Or.inl ⟨hA, rfl, rfl⟩⟩,
    gfaceWindSeven_neg_nonneg hpos hoA⟩

/-- **Excising a wrapping negative lobe** keeps `g ≥ 0`. -/
theorem gfaceWindSeven_wrap_neg {M : CombMap.{v}} {o : M.Face} {c p A q : List M.Dart}
    {g : M.Face → ℤ} (hpos : ∀ f, 0 ≤ g f) (hseg : c = p ++ A ++ q)
    (hB : IsSimpleClosedWalk M (q ++ p))
    (hoB : o ∈ SimpleClosedWalkSides.sideFaces M (q ++ p)) :
    ∃ t : List M.Dart × (M.Face → ℤ), gfaceWind_Step M o (c, g) t ∧ ∀ f, 0 ≤ t.2 f :=
  ⟨(A, fun f => g f - gfaceWind_wind M o (q ++ p) f), ⟨p, A, q, hseg, Or.inr ⟨hB, rfl, rfl⟩⟩,
    gfaceWindSeven_neg_nonneg hpos hoB⟩

/-- **A two-lobe split** `c = p ++ A ++ q` with `A` and `q ++ p` both simple has a
sign-keeping excision step: excise `A` if the base face lies on its side, else excise
`q ++ p`, leaving `g = wind_A = ind_A ≥ 0`. -/
theorem gfaceWindSeven_two {M : CombMap.{v}} (hM : M.IsPlanar) {C : List M.Dart}
    (hC : C.Nodup) {o : M.Face} {c p A q : List M.Dart} {g : M.Face → ℤ}
    (hinv : gfaceWind_Inv M C o c g) (hpos : ∀ f, 0 ≤ g f) (hseg : c = p ++ A ++ q)
    (hA : IsSimpleClosedWalk M A) (hB : IsSimpleClosedWalk M (q ++ p)) :
    ∃ t : List M.Dart × (M.Face → ℤ), gfaceWind_Step M o (c, g) t ∧ ∀ f, 0 ≤ t.2 f := by
  by_cases hoA : o ∈ SimpleClosedWalkSides.sideFaces M A
  · exact gfaceWindSeven_inner_neg hpos hseg hA hoA
  · have hst : gfaceWind_Step M o (c, g)
        (A, fun f => g f - gfaceWind_wind M o (q ++ p) f) :=
      ⟨p, A, q, hseg, Or.inr ⟨hB, rfl, rfl⟩⟩
    obtain ⟨⟨-, -, hcob, ho⟩, -⟩ := gfaceWind_step_inv (s := (c, g)) hM hC hinv hst
    refine ⟨_, hst, fun f => ?_⟩
    have key : g f - gfaceWind_wind M o (q ++ p) f = gfaceWind_wind M o A f :=
      gfaceWindSix_eq_wind (g := fun f => g f - gfaceWind_wind M o (q ++ p) f) hM hA hcob ho f
    show 0 ≤ g f - gfaceWind_wind M o (q ++ p) f
    rw [key]
    have h1 : gfaceWind_ind (SimpleClosedWalkSides.sideFaces M A) o = 0 := gfaceWind_ind_neg hoA
    have h3 : gfaceWind_wind M o A f = gfaceWind_ind (SimpleClosedWalkSides.sideFaces M A) f -
        gfaceWind_ind (SimpleClosedWalkSides.sideFaces M A) o := rfl
    rcases gfaceWindSix_ind01 (SimpleClosedWalkSides.sideFaces M A) f with h | h <;> linarith

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSeven_neg_nonneg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSeven_inner_neg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSeven_wrap_neg
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSeven_two
