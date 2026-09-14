import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellCycle
import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.Meta.AxiomGuard

/-!
# Faces of a simple bipartite map have degree at least four

Colour the darts of a map by a Boolean `c` that edge reversal flips and vertex rotation keeps: the
two ends of every edge have different colours.  The face permutation `φ = σ ∘ α` flips the colour,
so a face orbit has even length.  A face of degree two reads `x, φ x`; its two edges join the same
two vertices, so when no two darts join one ordered pair of vertices, `φ x = α x`.  Then both ends
of the edge of `x` have degree one.  So if the vertices of colour `true` have degree at least two,
every face has degree at least four.

This is the face half of the contact count of Osin's Lemma 9.4, on the bipartite map of polygons
(colour `true`, degree `d_f ≥ 2`) and objects.

* `CombMap.colour_facePerm_pow`: `φ^{2t}` keeps the colour and `φ^{2t+1}` flips it.
* `CombMap.four_le_faceDegree_of_bipartite`: the degree bound.

Model tests (hand).
* A square with both faces of degree four meets the bound.
* Two vertices joined by two edges form a digon face: simplicity fails.
* A single edge has one face of degree two: its vertices have degree one, which the degree
  hypothesis rules out on the `true` side.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe v

/-- **The colour along a face**: an even number of face steps keeps it, an odd number flips it. -/
theorem colour_facePerm_pow {M : CombMap.{v}} (c : M.Dart → Bool)
    (hflip : ∀ x, c (M.alpha x) = !c x) (hsig : ∀ x, c (M.sigma x) = c x) (x : M.Dart) :
    ∀ t : ℕ, c ((M.facePerm ^ (2 * t)) x) = c x ∧ c ((M.facePerm ^ (2 * t + 1)) x) = !c x := by
  have hstep : ∀ d, c (M.facePerm d) = !c d := fun d => by
    show c (M.sigma (M.alpha d)) = !c d
    rw [hsig, hflip]
  intro t
  induction t with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [show 2 * 0 + 1 = 1 from rfl, pow_one, hstep]
  | succ t ih =>
    have e1 : (M.facePerm ^ (2 * (t + 1))) x = M.facePerm ((M.facePerm ^ (2 * t + 1)) x) := by
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring, pow_succ', Equiv.Perm.mul_apply]
    have e2 : (M.facePerm ^ (2 * (t + 1) + 1)) x =
        M.facePerm ((M.facePerm ^ (2 * (t + 1))) x) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have h1 : c ((M.facePerm ^ (2 * (t + 1))) x) = c x := by
      rw [e1, hstep, ih.2, Bool.not_not]
    exact ⟨h1, by rw [e2, hstep, h1]⟩

/-- **Faces of a simple bipartite map have degree at least four**, when the vertices of colour
`true` have degree at least two. -/
theorem four_le_faceDegree_of_bipartite (M : CombMap.{v}) (c : M.Dart → Bool)
    (hflip : ∀ x, c (M.alpha x) = !c x) (hsig : ∀ x, c (M.sigma x) = c x)
    (hsimple : ∀ x y, M.vertexOf x = M.vertexOf y →
      M.vertexOf (M.alpha x) = M.vertexOf (M.alpha y) → x = y)
    (hdeg : ∀ x, c x = true → M.sigma x ≠ x) (f : M.Face) : 4 ≤ M.faceDegree f := by
  classical
  induction f using Quotient.inductionOn' with
  | h x =>
  show 4 ≤ M.faceDegree (M.faceOf x)
  obtain ⟨l, hl, hhead⟩ := M.exists_isFaceCycle_head x
  have hlen : l.length = M.faceDegree (M.faceOf x) := by
    rw [hl.length_eq, hhead]
  have hpos : 0 < l.length := List.length_pos_of_ne_nil hl.ne_nil
  have hper : (M.facePerm ^ l.length) x = x := by
    have h := OsinUnboundSameCellCycle.pow_length hl.toFaceBoundary (k := 0) hpos
    have h0 : hl.toFaceBoundary.darts[0]'hpos = x := by
      show l[0]'hpos = x
      rw [List.getElem_zero]
      exact hhead
    rw [h0] at h
    exact h
  have hodd : ¬ l.length % 2 = 1 := by
    intro hodd
    obtain ⟨t, ht⟩ : ∃ t, l.length = 2 * t + 1 := ⟨l.length / 2, by omega⟩
    have h := (colour_facePerm_pow c hflip hsig x t).2
    rw [← ht, hper] at h
    cases hcx : c x <;> simp [hcx] at h
  by_contra hlt
  have h2 : l.length = 2 := by omega
  have hper2 : M.facePerm (M.facePerm x) = x := by
    have h := hper
    rw [h2, pow_succ', pow_one, Equiv.Perm.mul_apply] at h
    exact h
  have hvy : M.vertexOf (M.facePerm x) = M.vertexOf (M.alpha x) := by
    show M.vertexOf (M.sigma (M.alpha x)) = M.vertexOf (M.alpha x)
    exact M.vertexOf_sigma _
  have hvay : M.vertexOf (M.alpha (M.facePerm x)) = M.vertexOf x := by
    have e : M.sigma (M.alpha (M.facePerm x)) = x := hper2
    conv_rhs => rw [← e]
    exact (M.vertexOf_sigma _).symm
  have hxy : x = M.alpha (M.facePerm x) :=
    hsimple x (M.alpha (M.facePerm x)) hvay.symm (by rw [M.alpha_involutive]; exact hvy.symm)
  have hya : M.facePerm x = M.alpha x := by
    conv_rhs => rw [hxy]
    rw [M.alpha_involutive]
  have hsa : M.sigma (M.alpha x) = M.alpha x := hya
  have hsx : M.sigma x = x := by
    have e : M.sigma (M.alpha (M.facePerm x)) = x := hper2
    rwa [hya, M.alpha_involutive] at e
  cases hcx : c x
  · exact hdeg (M.alpha x) (by rw [hflip, hcx]; rfl) hsa
  · exact hdeg x hcx hsx

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.colour_facePerm_pow
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.four_le_faceDegree_of_bipartite
