import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.OuterWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Section corners: the lobe separates nested corners

The lobe of a corner `(p, q)` of the outer face (`OuterWalk.lean`) satisfies the chain and turning
hypotheses of `FirstTurnEnclosure`, so on a planar map it has enclosed faces.

* `lobe_turnMem`: rotating from the reversal of a lobe dart, the first kept dart is a lobe dart.
  For a middle dart the first rotation is the next lobe dart.  For the last dart `ℓ (p + 1)` the
  rotations are `ℓ p` (not kept), `α (ℓ q)` (not kept), and `ℓ (q - 1)`, the first lobe dart.
* `lobe_separation`: for `p' ∈ (p, q)`, no face beyond the edges of two darts on the faces of
  `α (ℓ p)` and `α (ℓ p')` coincides, when all these reversals are off the outer face.  The face of
  `α (ℓ p')` is enclosed; crossing the non-walk edges carries enclosure to the face of `α (ℓ p)` and
  then to `F`, which holds walk darts.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners

open Equiv

universe v

variable {M : CombMap.{v}} {F : M.Face} (B : FaceBoundary M F)

/-- The turning condition at a middle lobe dart. -/
theorem turn_middle_mem {p q j m : ℕ} (hj1 : j + 1 < (lobe B p q).length) (hm : 0 < m)
    (havoid : ∀ k, 0 < k → k < m → ¬ SimpleClosedWalkSides.walkKeep M (lobe B p q)
      ((M.sigma ^ k) (M.alpha (ell B (q + B.darts.length - 1 - j))))) :
    (M.sigma ^ m) (M.alpha (ell B (q + B.darts.length - 1 - j))) ∈ lobe B p q := by
  have hs := lobe_turn_middle B hj1
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · refine (havoid 1 Nat.one_pos h1 ?_).elim
    rw [sigma_pow_one, hs]
    exact Or.inl (List.getElem_mem _)
  · obtain rfl : m = 1 := by omega
    rw [sigma_pow_one, hs]
    exact List.getElem_mem _

/-- The turning condition at the last lobe dart. -/
theorem turn_last_mem {p q m : ℕ} (hp : p < B.darts.length) (hq : q < B.darts.length)
    (hpq : p ≠ q) (hface : M.facePerm (M.alpha (ell B p)) = M.alpha (ell B q))
    (hpF : M.faceOf (M.alpha (ell B p)) ≠ F) (hqF : M.faceOf (M.alpha (ell B q)) ≠ F)
    (hlen1 : 0 < lobeLen B.darts.length p q) (hm : 0 < m)
    (hkeep : SimpleClosedWalkSides.walkKeep M (lobe B p q)
      ((M.sigma ^ m) (M.alpha (ell B (p + 1)))))
    (havoid : ∀ k, 0 < k → k < m → ¬ SimpleClosedWalkSides.walkKeep M (lobe B p q)
      ((M.sigma ^ k) (M.alpha (ell B (p + 1))))) :
    (M.sigma ^ m) (M.alpha (ell B (p + 1))) ∈ lobe B p q := by
  obtain ⟨s1, s2, s3⟩ := lobe_last_rotations B hq hface
  have c0 : ell B (q + B.darts.length - 1) ∈ lobe B p q :=
    (mem_lobe B).mpr ⟨0, hlen1, congrArg (ell B) (Nat.sub_zero _)⟩
  have nkp : ¬ SimpleClosedWalkSides.walkKeep M (lobe B p q) (ell B p) := by
    rintro (h | h)
    · have h' := inOpen_of_ell_mem B hq hp hpq h
      unfold InOpen at h'
      omega
    · exact hpF (faceOf_of_mem_lobe B h)
  have nkq : ¬ SimpleClosedWalkSides.walkKeep M (lobe B p q) (M.alpha (ell B q)) := by
    rintro (h | h)
    · exact hqF (faceOf_of_mem_lobe B h)
    · rw [M.alpha_involutive (ell B q)] at h
      have h' := inOpen_of_ell_mem B hq hq hpq h
      unfold InOpen at h'
      omega
  rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ 3 < m) with rfl | rfl | rfl | h3
  · rw [sigma_pow_one, s1] at hkeep
    exact absurd hkeep nkp
  · rw [sigma_pow_two, s1, s2] at hkeep
    exact absurd hkeep nkq
  · rw [sigma_pow_three, s1, s2, s3]
    exact c0
  · refine (havoid 3 (by omega) h3 ?_).elim
    rw [sigma_pow_three, s1, s2, s3]
    exact Or.inl c0

/-- **The lobe turns like a noncrossing walk.** -/
theorem lobe_turnMem {p q : ℕ} (hp : p < B.darts.length) (hq : q < B.darts.length)
    (hpq : p ≠ q) (hface : M.facePerm (M.alpha (ell B p)) = M.alpha (ell B q))
    (hpF : M.faceOf (M.alpha (ell B p)) ≠ F) (hqF : M.faceOf (M.alpha (ell B q)) ≠ F) :
    FirstTurnEnclosure.TurnMem M (lobe B p q) := by
  intro d hd m hm hkeep havoid
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hd
  rw [lobe_getElem B p q j hj] at hkeep havoid ⊢
  rcases Nat.lt_or_ge (j + 1) (lobe B p q).length with hj1 | hj1
  · exact turn_middle_mem B hj1 hm havoid
  · have hlen := lobe_length B p q
    have hj' : j + 1 = lobeLen B.darts.length p q := by omega
    have hlast : ell B (q + B.darts.length - 1 - j) = ell B (p + 1) := by
      unfold lobeLen at hj'
      split_ifs at hj'
      · rw [show q + B.darts.length - 1 - j = (p + 1) + B.darts.length by omega, ell_add_length]
      · exact congrArg (ell B) (by omega)
    rw [hlast] at hkeep havoid ⊢
    exact turn_last_mem B hp hq hpq hface hpF hqF (by omega) hm hkeep havoid

/-- Darts based off `F` with reversals based off `F` are not kept by a lobe. -/
theorem not_walkKeep_lobe {p q : ℕ} {y : M.Dart} (hy : M.faceOf y ≠ F)
    (hay : M.faceOf (M.alpha y) ≠ F) : ¬ SimpleClosedWalkSides.walkKeep M (lobe B p q) y := by
  rintro (h | h)
  · exact hy (faceOf_of_mem_lobe B h)
  · exact hay (faceOf_of_mem_lobe B h)

/-- **Separation of nested corners.** -/
theorem lobe_separation (hM : M.IsPlanar) {p q p' : ℕ} (hp : p < B.darts.length)
    (hq : q < B.darts.length) (hp' : p' < B.darts.length)
    (hface : M.facePerm (M.alpha (ell B p)) = M.alpha (ell B q))
    (hpF : M.faceOf (M.alpha (ell B p)) ≠ F) (hqF : M.faceOf (M.alpha (ell B q)) ≠ F)
    (hp'F : M.faceOf (M.alpha (ell B p')) ≠ F) (hopen : InOpen p q p')
    {x x' : M.Dart} (hx : M.faceOf x = M.faceOf (M.alpha (ell B p)))
    (hx' : M.faceOf x' = M.faceOf (M.alpha (ell B p')))
    (hax : M.faceOf (M.alpha x) ≠ F) (hax' : M.faceOf (M.alpha x') ≠ F)
    (hxx' : M.faceOf (M.alpha x) = M.faceOf (M.alpha x')) : False := by
  have hpq : p ≠ q := by
    unfold InOpen at hopen
    omega
  have hmem : ell B p' ∈ lobe B p q := ell_mem_lobe B hp hp' hopen
  have hne : lobe B p q ≠ [] := List.ne_nil_of_mem hmem
  have hchain := lobe_isChain B p q
  have hturn := lobe_turnMem B hp hq hpq hface hpF hqF
  have hFout : F ∉ enclosedFaces M (lobe B p q) := by
    have h := FirstTurnEnclosure.faceOf_not_mem_enclosedFaces hM hne hchain hturn hmem
    rwa [faceOf_ell] at h
  have h1 : M.faceOf x' ∈ enclosedFaces M (lobe B p q) := by
    rw [hx']
    rcases ((FirstTurnEnclosure.mem_iff_enclosedFaces hM hne hchain hturn _).mp hmem).2 with h | h
    · exact h
    · exact absurd (faceOf_of_mem_lobe B h) hp'F
  have h2 := FirstTurnEnclosure.faceOf_alpha_mem_enclosedFaces
    (not_walkKeep_lobe B (by rw [hx']; exact hp'F) hax') h1
  rw [← hxx'] at h2
  have h3 := FirstTurnEnclosure.faceOf_alpha_mem_enclosedFaces
    (not_walkKeep_lobe B (p := p) (q := q) hax (by rw [M.alpha_involutive x, hx]; exact hpF)) h2
  rw [M.alpha_involutive x, hx] at h3
  have hnk : ¬ SimpleClosedWalkSides.walkKeep M (lobe B p q) (M.alpha (ell B p)) := by
    rintro (h | h)
    · exact hpF (faceOf_of_mem_lobe B h)
    · rw [M.alpha_involutive (ell B p)] at h
      have h' := inOpen_of_ell_mem B hq hp hpq h
      unfold InOpen at h'
      omega
  have h4 := FirstTurnEnclosure.faceOf_alpha_mem_enclosedFaces hnk h3
  rw [M.alpha_involutive (ell B p), faceOf_ell] at h4
  exact hFout h4

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners
