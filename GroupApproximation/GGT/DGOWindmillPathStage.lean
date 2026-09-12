import GroupApproximation.GGT.DGOWindmillPath
import GroupApproximation.GGT.DGOWindmillStage

/-!
# The reduced-path induction with endpoints on the stage spoke set

`DGOWindmillPath.between_and_dist_of_reducedList` deliberately takes abstract
reference sets and therefore requires both boundary directions to reach those
sets.  At the concrete growth stage an endpoint belongs only to `stageOne`; it
may lie on the first or last syllable apex's own spoke, which is the one spoke
excluded from `stageRef`.

This module performs the boundary reduction which DGO leave implicit.  Extend
such an endpoint outwards along its spoke to the foot in the old windmill,
apply the sharp corner there, then move the endpoint back in using the two
metric trimming lemmas in `DGOWindmillCorner`.  No broken path is parametrised
and no extra hyperbolicity constant is spent.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- **Every stage-one point extends along its spoke to the reference set of a
fixed new apex.**

If the point is on the excluded spoke itself, its old-windmill foot is the
extension.  Otherwise the point already belongs to the reference set and is
its own extension. -/
theorem exists_stageRef_extension {delta : Real} {C W : Set X} {d p : X}
    (hp : p ∈ stageOne delta C W) :
    ∃ z ∈ stageRef delta C W d, Between d p z := by
  rcases mem_spokeSet_iff.mp hp with hpW | ⟨e, he, w, hw, hew, hep⟩
  · exact ⟨p, subset_spokeSet hpW, between_self_right d p⟩
  · by_cases hed : e = d
    · subst e
      exact ⟨w, subset_spokeSet hw, hep⟩
    · refine ⟨p, ?_, between_self_right d p⟩
      exact Or.inr ⟨e, ⟨he, hed⟩, w, hw, hew, hep⟩

/-! ## Covering a caller-owned geodesic by the ordered local ranges -/

/-- **An ordered between-chain with `12δ`-quasiconvex consecutive ranges is
`18δ`-close to the caller's geodesic.**

For a parameter `t`, take the least chain vertex whose distance from the first
endpoint is at least `t`.  The preceding and current vertices are each `2δ`
from the caller's geodesic at their exact distance parameters.  The
quadrilateral between those two points and the corresponding local side costs
`6δ`; its middle side costs another `12δ`, while either short outer side
costs only `2δ`. -/
theorem exists_close_of_ordered_between_chain {delta : Real}
    (hdelta : 0 < delta) (hhyp : IsHyperbolicSpace delta X)
    (hgeo : IsGeodesicSpace X) {Q : Set X} {x y : X}
    (chain : Nat → X) (N : Nat) (hzero : chain 0 = x) (hlast : chain N = y)
    (hbetween : ∀ i, i ≤ N → Between x (chain i) y)
    (hstep : ∀ i, i < N → Between x (chain i) (chain (i + 1)))
    (hmem : ∀ i, i ≤ N → chain i ∈ Q)
    (hlocal : ∀ i, i < N → ∀ g : Real → X,
      IsGeodesicSegment g 0 (dist (chain i) (chain (i + 1))) →
      g 0 = chain i → g (dist (chain i) (chain (i + 1))) = chain (i + 1) →
      ∀ s ∈ Set.Icc (0 : Real) (dist (chain i) (chain (i + 1))),
        ∃ q ∈ Q, dist (g s) q ≤ 12 * delta)
    {f : Real → X} (hf : IsGeodesicSegment f 0 (dist x y))
    (hf0 : f 0 = x) (hf1 : f (dist x y) = y)
    {t : Real} (ht : t ∈ Set.Icc (0 : Real) (dist x y)) :
    ∃ q ∈ Q, dist (f t) q ≤ 18 * delta := by
  have hex : ∃ j : Nat, j ≤ N ∧ t ≤ dist x (chain j) := by
    refine ⟨N, le_rfl, ?_⟩
    rw [hlast]
    exact ht.2
  let j : Nat := Nat.find hex
  have hj : j ≤ N ∧ t ≤ dist x (chain j) := Nat.find_spec hex
  by_cases hj0 : j = 0
  · have ht0 : t = 0 := by
      have : t ≤ 0 := by simpa [hj0, hzero] using hj.2
      linarith [ht.1]
    refine ⟨chain 0, hmem 0 (Nat.zero_le N), ?_⟩
    rw [ht0, hf0, hzero, dist_self]
    linarith
  · let i : Nat := j - 1
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hij : i + 1 = j := by
      dsimp [i]
      omega
    have hiN : i < N := by omega
    have hnotprev : ¬ (i ≤ N ∧ t ≤ dist x (chain i)) :=
      Nat.find_min hex (by dsimp [i]; omega)
    have hleft : dist x (chain i) < t := by
      have hi_le : i ≤ N := by omega
      exact lt_of_not_ge (fun h ↦ hnotprev ⟨hi_le, h⟩)
    have hright : t ≤ dist x (chain (i + 1)) := by
      rw [hij]
      exact hj.2
    have hbi := hbetween i (by omega)
    have hbj := hbetween (i + 1) (by omega)
    have hsi := hstep i hiN
    have hri : dist (chain i) (f (dist x (chain i))) ≤ 2 * delta :=
      dist_geodesic_at_between_parameter_le hhyp hbi hf hf0 hf1
    have hrj : dist (chain (i + 1)) (f (dist x (chain (i + 1)))) ≤ 2 * delta :=
      dist_geodesic_at_between_parameter_le hhyp hbj hf hf0 hf1
    let A : X := f (dist x (chain i))
    let B : X := chain i
    let C' : X := chain (i + 1)
    let D : X := f (dist x (chain (i + 1)))
    let F : Real → X := fun s => f (dist x (chain i) + s)
    have hlen : dist x (chain (i + 1))
        = dist x (chain i) + dist (chain i) (chain (i + 1)) := hsi
    have hAD : dist A D = dist (chain i) (chain (i + 1)) := by
      dsimp [A, D]
      have hiMem : dist x (chain i) ∈ Set.Icc (0 : Real) (dist x y) :=
        ⟨dist_nonneg, hbi.dist_le_left⟩
      have hjMem : dist x (chain (i + 1)) ∈ Set.Icc (0 : Real) (dist x y) :=
        ⟨dist_nonneg, hbj.dist_le_left⟩
      rw [hf _ hiMem _ hjMem, abs_of_nonpos (by linarith [hsi.dist_le_left]),
        hlen]
      ring
    have hF : IsGeodesicSegment F 0 (dist A D) := by
      rw [hAD]
      intro s hs u hu
      have hsMem : dist x (chain i) + s ∈ Set.Icc (0 : Real) (dist x y) := by
        constructor
        · linarith [dist_nonneg (x := x) (y := chain i), hs.1]
        · have := hbj.dist_le_left
          linarith [hs.2, hlen]
      have huMem : dist x (chain i) + u ∈ Set.Icc (0 : Real) (dist x y) := by
        constructor
        · linarith [dist_nonneg (x := x) (y := chain i), hu.1]
        · have := hbj.dist_le_left
          linarith [hu.2, hlen]
      dsimp [F]
      rw [hf _ hsMem _ huMem]
      congr 1
      ring
    have hF0 : F 0 = A := by simp [F, A]
    have hF1 : F (dist A D) = D := by
      dsimp [F, D]
      rw [hAD, ← hlen]
    have htF : t - dist x (chain i) ∈ Set.Icc (0 : Real) (dist A D) := by
      constructor
      · linarith
      · rw [hAD]
        linarith [hlen]
    obtain ⟨gAB, hAB, hAB0, hAB1⟩ := hgeo A B
    obtain ⟨gBC, hBC, hBC0, hBC1⟩ := hgeo B C'
    obtain ⟨gCD, hCD, hCD0, hCD1⟩ := hgeo C' D
    have hAt : F (t - dist x (chain i)) = f t := by
      dsimp [F]
      congr 1
      linarith
    rcases exists_close_on_other_sides_of_quadrilateral hhyp (le_of_lt hdelta)
        hgeo hF hF0 hF1 hAB hAB0 hAB1 hBC hBC0 hBC1 hCD hCD0 hCD1 htF with
      ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩
    · refine ⟨B, hmem i (by omega), ?_⟩
      rw [hAt] at hclose
      have hsB : dist (gAB s) B ≤ 2 * delta := by
        have hd := hAB s hs (dist A B) ⟨dist_nonneg, le_rfl⟩
        rw [hAB1, abs_of_nonpos (by linarith [hs.2])] at hd
        have hABle : dist A B ≤ 2 * delta := by
          dsimp [A, B]
          rwa [dist_comm]
        rw [hd]
        linarith [hs.1, hs.2, hABle]
      linarith [dist_triangle (f t) (gAB s) B]
    · obtain ⟨q, hq, hqd⟩ := hlocal i hiN gBC hBC hBC0 hBC1 s hs
      refine ⟨q, hq, ?_⟩
      rw [hAt] at hclose
      linarith [dist_triangle (f t) (gBC s) q]
    · refine ⟨C', hmem (i + 1) (by omega), ?_⟩
      rw [hAt] at hclose
      have hsC : dist (gCD s) C' ≤ 2 * delta := by
        have hd := hCD s hs 0 ⟨le_rfl, dist_nonneg⟩
        rw [hCD0, sub_zero, abs_of_nonneg hs.1] at hd
        have hCDle : dist C' D ≤ 2 * delta := by
          dsimp [C', D]
          exact hrj
        have hsle := hs.2
        linarith
      linarith [dist_triangle (f t) (gCD s) C']

/-- **DGO's reduced-path induction with both endpoints allowed in
`stageOne`.**

The central induction is the same as `between_and_dist_of_reducedList`.  The
only new work is at the two boundary syllables: `exists_stageRef_extension`
moves an endpoint to a valid far anchor, the corner lemma is applied there,
and the result is trimmed back to the original endpoint. -/
theorem between_and_dist_of_reducedList_stageOne {delta rho : Real}
    (hdelta : 0 < delta) (hrho : 200 * delta ≤ rho)
    (hhyp : IsHyperbolicSpace delta X) (hgeo : IsGeodesicSpace X)
    {C : Set X} {Rot : X → Subgroup G}
    (hfam : IsRotatingFamily G X C Rot)
    (hvr : IsVeryRotating G X delta C Rot) (hsep : IsSeparated C rho)
    {W : Set X} (hW : IsWindmill G X delta C Rot W)
    {y : X} (hy : y ∈ stageOne delta C W) :
    ∀ (l : List (Syll G X)) (w : Syll G X),
      (∀ u ∈ w :: l,
        Syll.IsValid Rot (newApices delta C W) (windmillGroup C Rot W) u) →
      ReducedList (w :: l) →
      ∀ x : X, w.pre⁻¹ • x ∈ stageOne delta C W →
        Between x (w.pre • w.dir) (listEval (w :: l) • y) ∧
          rho * (l.length : Real) ≤
            dist (w.pre • w.dir) (listEval (w :: l) • y) := by
  intro l
  induction l with
  | nil =>
      intro w hvalid _ x hx
      have hw := hvalid w (by simp)
      obtain ⟨zx, hzx, hxb⟩ := exists_stageRef_extension (d := w.dir) hx
      obtain ⟨zy, hzy, hyb⟩ := exists_stageRef_extension (d := w.dir) hy
      have hcorner := between_of_corner hdelta hhyp hgeo hfam hvr
        (newApices_subset hw.dir_mem) hw.rot_mem hw.rot_ne_one
        (isQuasiconvexSet_stageRef (le_of_lt hdelta) hhyp hgeo hW w.dir)
        (le_dist_of_mem_stageRef (le_of_lt hdelta) hrho hW hsep hw.dir_mem)
        hzx (between_self_right w.dir zx) hzy (between_self_right w.dir zy)
      have hleft := between_of_corner_of_between hcorner hxb
      have hyrot : Between w.dir (w.rot • y) (w.rot • zy) :=
        smul_between_of_mem_rot hfam (newApices_subset hw.dir_mem)
          hw.rot_mem hyb
      have htrim := between_of_corner_of_between_right hleft hyrot
      have htr := smul_between hfam.isometric w.pre htrim
      rw [smul_inv_smul, ← mul_smul] at htr
      have hEeq : listEval (w :: ([] : List (Syll G X))) • y
          = (w.pre * w.rot) • y := by
        rw [listEval_cons, listEval_nil, mul_one]
      rw [hEeq]
      refine ⟨htr, ?_⟩
      simp
  | cons t l' ih =>
      intro w hvalid hred x hx
      have hw := hvalid w (by simp)
      have ht := hvalid t (by simp)
      have hredC : List.IsChain Seam (w :: t :: l') := hred
      obtain ⟨hseam, hredtail⟩ := List.isChain_cons_cons.mp hredC
      have hseam' : t.pre • t.dir ≠ w.dir := hseam
      have htdirNew : t.pre • t.dir ∈ newApices delta C W :=
        smul_mem_newApices hfam hW ht.pre_mem ht.dir_mem
      have htailStart : t.pre⁻¹ • w.dir ∈ stageOne delta C W :=
        newApices_subset_stageOne
          (smul_mem_newApices hfam hW (inv_mem ht.pre_mem) hw.dir_mem)
      obtain ⟨ihb, ihlen⟩ :=
        ih t (fun u hu => hvalid u (List.mem_cons_of_mem w hu)) hredtail
          w.dir htailStart
      obtain ⟨zx, hzx, hxb⟩ := exists_stageRef_extension (d := w.dir) hx
      have hzout : t.pre • t.dir ∈ stageRef delta C W w.dir :=
        mem_stageRef_of_mem_newApices (d := w.dir) htdirNew hseam'
      have hcorner := between_of_corner hdelta hhyp hgeo hfam hvr
        (newApices_subset hw.dir_mem) hw.rot_mem hw.rot_ne_one
        (isQuasiconvexSet_stageRef (le_of_lt hdelta) hhyp hgeo hW w.dir)
        (le_dist_of_mem_stageRef (le_of_lt hdelta) hrho hW hsep hw.dir_mem)
        hzx (between_self_right w.dir zx) hzout ihb
      have htrim := between_of_corner_of_between hcorner hxb
      have htr := smul_between hfam.isometric w.pre htrim
      rw [smul_inv_smul] at htr
      have hEeq : listEval (w :: t :: l') • y
          = w.pre • w.rot • (listEval (t :: l') • y) := by
        rw [listEval_cons, mul_smul, mul_smul]
      rw [hEeq]
      refine ⟨htr, ?_⟩
      have hrotfix : w.rot • w.dir = w.dir :=
        hfam.rot_fix (newApices_subset hw.dir_mem) w.rot hw.rot_mem
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
      have hP1C : w.pre • w.dir ∈ C :=
        hfam.apex_smul w.pre (newApices_subset hw.dir_mem)
      have hP2C : w.pre • w.rot • (t.pre • t.dir) ∈ C :=
        hfam.apex_smul w.pre (hfam.apex_smul w.rot (newApices_subset htdirNew))
      have hne : w.pre • w.dir ≠ w.pre • w.rot • (t.pre • t.dir) := by
        intro heq
        have h1 : w.dir = w.rot • (t.pre • t.dir) :=
          smul_left_cancel w.pre heq
        apply hseam'
        have h2 : w.rot • w.dir = w.rot • (t.pre • t.dir) := by
          rw [hrotfix]
          exact h1
        exact (smul_left_cancel w.rot h2).symm
      have hgap : rho ≤
          dist (w.pre • w.dir) (w.pre • w.rot • (t.pre • t.dir)) :=
        hsep _ hP1C _ hP2C hne
      have hlen : (((t :: l').length : Nat) : Real)
          = (l'.length : Real) + 1 := by simp
      rw [hlen]
      linarith

end DGOWindmill
end GroupApproximation
