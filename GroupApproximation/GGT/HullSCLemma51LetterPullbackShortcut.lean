import GroupApproximation.GGT.HullSCLemma51LetterPullbackShortcutArcs

/-!
# The shortcut move of the letter pullback

A lifted quotient-null word `p ++ [comp λ h⁻¹]` with a rotation that is not geodesic has an
outcome at radius `2 n + 2` and count `2 n + 3`.  The rotation `x ++ comp λ h⁻¹ :: y` has a
geodesic shortcut `g` with the same value.  If no peripheral letter of index `λ` of `g` is read at
the coset of `listVal x`, then `h` is a bounded product of the atoms.  Otherwise exactly one is,
and `g` is the new quotient-null word, with that letter designated.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- **The move bound for words with a non-geodesic rotation.** -/
theorem letterStepBound_of_not_isRelGeodesic (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (q : G →* Q) (hq : Function.Surjective q) :
    LetterStepBound D W q hq (fun w => ¬ ∀ r : ℕ, IsRelGeodesic D (w.rotate r)) := by
  refine ⟨fun n => 2 * n + 2, fun n => 2 * n + 3, ?_⟩
  intro lam n h p hh hp hlen havoid hqp _ hP
  show PullbackOutcome D q hq lam (pullbackAtoms W D lam (2 * n + 2)) (2 * n + 3) h n
  have hng : ¬ ∀ r : ℕ, IsRelGeodesic D ((p ++ [GGT.RelLetter.comp lam h⁻¹]).rotate r) := hP
  obtain ⟨r, hr⟩ := not_forall.mp hng
  obtain ⟨x, y, c, hrot, hlift⟩ := exists_rotatedLift D q hq hh hp havoid hqp r
  have hsgeo : ¬ IsRelGeodesic D (x ++ GGT.RelLetter.comp lam h⁻¹ :: y) := by
    rw [← hrot]
    exact hr
  obtain ⟨g, hgadm, hggeo, hgval, hglen⟩ :=
    exists_shortcut_of_not_isRelGeodesic D hlift.letters hsgeo
  have hg : ∀ a ∈ g, D.IsLetter a := hgadm
  have hslen : x.length + y.length = p.length := by
    have e := congrArg List.length hrot
    simp only [List.length_rotate, List.length_append, List.length_cons, List.length_singleton,
      List.length_nil] at e
    omega
  have hglen' : g.length ≤ x.length + y.length := by
    simp only [List.length_append, List.length_cons] at hglen
    omega
  have hr1 : 1 ≤ 2 * n + 2 := by omega
  have hrlen : g.length + x.length + y.length ≤ 2 * n + 2 := by omega
  have hN : 2 * n + 2 + 1 ≤ 2 * n + 3 := by omega
  have hgn : g.length ≤ n + 1 := by omega
  by_cases hdes : ∃ (k : ℕ) (hk : k < g.length), GGT.RelLetter.IsCompOf lam g[k] ∧
      (GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal x ∈ D.fam lam
  · obtain ⟨k, hk, hkcomp, hkcos⟩ := hdes
    exact pullbackOutcome_of_rotatedLift_of_designated W D q hq hlift hh hg hggeo hgval hr1 hrlen
      hN hgn hk hkcomp hkcos
  · exact Or.inl ⟨h, mem_boundedProducts_of_rotatedLift_of_forall W D q hq hlift hh hg hgval hr1
      hrlen hN (fun k hk hkcomp hkcos => hdes ⟨k, hk, hkcomp, hkcos⟩), rfl⟩

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.letterStepBound_of_not_isRelGeodesic
