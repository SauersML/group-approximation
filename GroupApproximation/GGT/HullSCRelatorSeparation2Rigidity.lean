import GroupApproximation.GGT.HullSCRelatorSeparation2Rigid
import GroupApproximation.GGT.OsinTheorem54SepRigidityReduction

/-!
# The rigidity input, over the bound

`GGT/HullSCRelatorSeparation2Rigid.lean` takes `hgeo` -- that a short
conjugation carrying one deep power onto another leaves both conjugators in the
subgroup -- as a named hypothesis.  `GGT/OsinTheorem54SepRigidityReduction.lean`
proves it from fp-geometry's bound, and this module is the bridge: it produces
`hgeo` in exactly the shape the rigidity consumes.

Three things the bridge has to do, and one of them is not bookkeeping.

* **Words, not elements.**  The reduction speaks of base-spelled words `px`,
  `rx`; the rigidity speaks of group elements with a norm bound.  A shortest
  spelling converts one to the other (`exists_isWord_length_eq` and
  `listVal_map_base`).
* **The degenerate case is not the reduction's.**  The reduction requires
  `0 < rx.length`, so it says nothing when the second conjugator is trivial --
  and that case needs no geometry at all: `x · a^i · 1 = a^j` gives
  `x = a^j (a^i)⁻¹`, a product of peripheral elements.  So no separate lemma is
  needed for it; the bridge splits on `x' = 1` and closes that branch by hand.
* **The polygon is the price.**  What replaces `hgeo` is not nothing: the
  reduction wants the quadrilateral
  `px ++ [a_s^i] ++ rx ++ revWord [a_s^j]` to be quasi-geodesic, and that is
  carried here as a hypothesis.  The trade is worth making -- a quasi-geodesicity
  side condition on a four-sided polygon is the same species as `hcount` and is
  what the polygon theory is built to consume, whereas `hgeo` was an
  isolated-component claim with nothing behind it.

Worth recording: the norm bounds on the conjugators are NOT used.  The reduction
needs them base-spelled and the quadrilateral quasi-geodesic; shortness enters
only through the latter.  They are kept in the conclusion so that it matches the
rigidity's binder verbatim.

The depth radius is the reduction's, not the caller's: it yields a constant `C`
and asks for `C · 4 ≤ rho`.  A caller whose `rho` is given designs its exponents
at `max rho (C * 4)` and weakens with `HullSC.notMem_relBall_of_le`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Rigidity

variable {G : Type u} [Group G]

/-- **The rigidity input, from the bound.**

`hgeo` in the shape `HullSC.exponent_eq_of_blockMatch₂` takes it, at any depth
radius past `4C`, with the quadrilateral's quasi-geodesicity as the hypothesis
that replaces it. -/
theorem exists_hgeo_of_bound {D : GGT.RelGenSet G Bool}
    (hbase : IsSymmetricGeneratingSet D.base)
    (hbound : GGT.OsinComponents.IsolatedComponentBound
      (GGT.OsinComponents.IsQuasiGeodesicPolygon D) D)
    {a : Bool → G} (hmem : ∀ t : Bool, a t ∈ D.fam t) (s : Bool)
    {mu b : ℝ} (hmu : 1 ≤ mu) (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧ ∀ rho eps : ℕ, C * 4 ≤ rho →
      (∀ (i j : ℕ) (px rx : List (GGT.RelLetter G Bool)),
          (∀ c ∈ px, ∃ y : G, c = GGT.RelLetter.base y) →
          (∀ c ∈ rx, ∃ y : G, c = GGT.RelLetter.base y) →
          GGT.RelLetter.listVal px * a s ^ i * GGT.RelLetter.listVal rx
              = a s ^ j →
            GGT.OsinComponents.IsQuasiGeodesicPolygon D mu b 4 1
              (px ++ [GGT.RelLetter.comp s (a s ^ i)] ++ rx ++
                GGT.OsinComponents.revWord
                  [GGT.RelLetter.comp s (a s ^ j)])) →
        ∀ (i j : ℕ) (x x' : G), wordNorm D.base x ≤ eps →
          wordNorm D.base x' ≤ eps → a s ^ i ∉ D.relBall s rho →
            a s ^ j ∉ D.relBall s rho → x * a s ^ i * x' = a s ^ j →
              x ∈ D.fam s ∧ x' ∈ D.fam s := by
  obtain ⟨C, hCpos, hred⟩ :=
    GGT.OsinComponents.mem_fam_of_conj_of_deep D hbound hmem s hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro rho eps hrho hpoly i j x x' _hx _hx' hdi _hdj heq
  by_cases hx'1 : x' = 1
  · subst hx'1
    refine ⟨?_, one_mem _⟩
    have hxe : x = a s ^ j * (a s ^ i)⁻¹ := by
      rw [mul_one] at heq
      rw [← heq, mul_inv_cancel_right]
    rw [hxe]
    exact mul_mem (pow_mem (hmem s) j) (inv_mem (pow_mem (hmem s) i))
  · obtain ⟨l, hl, -⟩ := exists_isWord_length_eq hbase x
    obtain ⟨l', hl', -⟩ := exists_isWord_length_eq hbase x'
    have hpx : GGT.RelLetter.listVal
        (l.map (GGT.RelLetter.base : G → GGT.RelLetter G Bool)) = x := by
      rw [listVal_map_base]
      exact hl.prod_eq
    have hrx : GGT.RelLetter.listVal
        (l'.map (GGT.RelLetter.base : G → GGT.RelLetter G Bool)) = x' := by
      rw [listVal_map_base]
      exact hl'.prod_eq
    have hbasepx : ∀ c ∈ l.map (GGT.RelLetter.base : G → GGT.RelLetter G Bool),
        ∃ y : G, c = GGT.RelLetter.base y := by
      intro c hc
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc
      exact ⟨y, rfl⟩
    have hbaserx : ∀ c ∈ l'.map (GGT.RelLetter.base : G → GGT.RelLetter G Bool),
        ∃ y : G, c = GGT.RelLetter.base y := by
      intro c hc
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hc
      exact ⟨y, rfl⟩
    have hne : 0 < (l'.map (GGT.RelLetter.base : G → GGT.RelLetter G Bool)).length := by
      rw [List.length_map]
      rcases Nat.eq_zero_or_pos l'.length with h0 | hpos
      · exact absurd (by rw [← hl'.prod_eq, List.length_eq_zero_iff.mp h0,
          List.prod_nil]) hx'1
      · exact hpos
    have heq' : GGT.RelLetter.listVal
          (l.map (GGT.RelLetter.base : G → GGT.RelLetter G Bool)) * a s ^ i *
        GGT.RelLetter.listVal
          (l'.map (GGT.RelLetter.base : G → GGT.RelLetter G Bool)) = a s ^ j := by
      rw [hpx, hrx]
      exact heq
    obtain ⟨h1, h2⟩ := hred 4 rho i j _ _ hbasepx hbaserx hne heq'
      (hpoly i j _ _ hbasepx hbaserx heq') hrho hdi
    rw [hpx] at h1
    rw [hrx] at h2
    exact ⟨h1, h2⟩

end Rigidity

end HullSC
end GroupApproximation
