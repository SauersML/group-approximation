import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketEnclosedSides
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket of a same-face bridge as an enclosed face set

Osin (math/0411039v3, §9), proof of Lemma 9.4.  Let `d` be a dart of a relator cell `i` whose reverse
lies on cell `i`, oriented toward the exterior, with a relator cell other than `i` on the far side.
The far faces (`SameCellPocketEnclosed.farFaces`) are enclosed, in successor form, by the pocket walk
`f d, …, fᵐ d`, which is an arc of cell `i`.

* `enclosedFaceSetSucc_pocketWalk`: the enclosed face set, from the far side along the face
  (`OsinUnboundSameCellPocketEnclosedSides`).  Every turn of the walk is one face step, except the
  closing turn, which passes `α d` and meets `f d` at the second rotation.
* `pocketArc_darts`: the pocket walk is the arc of cell `i` starting right after `d`.
* `exists_enclosedPocket`: the statement used by the loop cut.  A far relator cell forces `m ≥ 1`,
  since a degree-one endpoint is alone on its side (`AvoidEdgeStep.eq_iff_of_sigma_fixed`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace SameCellPocketEnclosed

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

theorem faceOf_pow {M : CombMap.{v}} (x : M.Dart) (t : ℕ) :
    M.faceOf ((M.facePerm ^ t) x) = M.faceOf x :=
  ((M.faceOf_eq_iff _ _).mpr (⟨(t : ℤ), by rw [zpow_natCast]⟩ : M.facePerm.SameCycle x _)).symm

theorem vertexOf_alpha_eq_facePerm {M : CombMap.{v}} (x : M.Dart) :
    M.vertexOf (M.alpha x) = M.vertexOf (M.facePerm x) :=
  (M.vertexOf_eq_iff _ _).mpr ⟨1, by rw [zpow_one]; rfl⟩

section Walk

variable {M : CombMap.{v}} {d : M.Dart} {n m : ℕ}

/-- The first turn of the pocket walk after the reverse of its `k`-th dart. -/
theorem first_turn_pocket
    (hinj : ∀ a b, a < n → b < n → (M.facePerm ^ a) d = (M.facePerm ^ b) d → a = b)
    (hmn : m + 1 < n) (hm : (M.facePerm ^ (m + 1)) d = M.alpha d) (hpos : 0 < m) {k : ℕ}
    (hk : k < m) {m' : ℕ} (hm' : 0 < m')
    (hkeep : walkKeep M (pocketWalk M d m) ((M.sigma ^ m') (M.alpha ((M.facePerm ^ (k + 1)) d))))
    (hmin : ∀ j, 0 < j → j < m' →
      ¬ walkKeep M (pocketWalk M d m) ((M.sigma ^ j) (M.alpha ((M.facePerm ^ (k + 1)) d)))) :
    (M.sigma ^ m') (M.alpha ((M.facePerm ^ (k + 1)) d)) = (M.facePerm ^ ((k + 1) % m + 1)) d := by
  have hone : (M.sigma ^ 1) (M.alpha ((M.facePerm ^ (k + 1)) d)) = (M.facePerm ^ (k + 1 + 1)) d := by
    rw [pow_one, pow_succ' _ (k + 1), Equiv.Perm.mul_apply]
    rfl
  rcases Nat.lt_or_ge (k + 1) m with hlt | hge
  · have hkept : walkKeep M (pocketWalk M d m) ((M.sigma ^ 1) (M.alpha ((M.facePerm ^ (k + 1)) d))) := by
      rw [hone]
      exact Or.inl (mem_pocketWalk.mpr ⟨k + 1, hlt, rfl⟩)
    obtain rfl : m' = 1 := by
      by_contra hne
      exact hmin 1 Nat.one_pos (by omega) hkept
    rw [hone, Nat.mod_eq_of_lt hlt]
  · have hkm : k + 1 = m := by omega
    have htwo : (M.sigma ^ 2) (M.alpha ((M.facePerm ^ (k + 1)) d)) = (M.facePerm ^ (0 + 1)) d := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ', Equiv.Perm.mul_apply, hone, hkm, hm, zero_add,
        pow_one]
      rfl
    have hnot : ¬ walkKeep M (pocketWalk M d m) ((M.sigma ^ 1) (M.alpha ((M.facePerm ^ (k + 1)) d))) := by
      rw [hone, hkm, hm]
      rintro (h | h)
      · obtain ⟨t, ht, heq⟩ := mem_pocketWalk.mp h
        have := hinj (t + 1) (m + 1) (by omega) hmn (heq.trans hm.symm)
        omega
      · rw [M.alpha_involutive] at h
        obtain ⟨t, ht, heq⟩ := mem_pocketWalk.mp h
        have := hinj (t + 1) 0 (by omega) (by omega) (by rw [pow_zero, Equiv.Perm.one_apply]; exact heq)
        omega
    have hkept : walkKeep M (pocketWalk M d m) ((M.sigma ^ 2) (M.alpha ((M.facePerm ^ (k + 1)) d))) := by
      rw [htwo]
      exact Or.inl (mem_pocketWalk.mpr ⟨0, hpos, rfl⟩)
    have hm2 : m' = 2 := by
      rcases Nat.lt_or_ge m' 2 with h | h
      · obtain rfl : m' = 1 := by omega
        exact absurd hkeep hnot
      · by_contra hne
        exact hmin 2 (by omega) (by omega) hkept
    subst hm2
    rw [htwo, hkm, Nat.mod_self]

/-- **The pocket walk encloses the far faces, turning to its successor.** -/
theorem enclosedFaceSetSucc_pocketWalk (Delta : DiscDiagram.{u, w, v} W) {d : Delta.toCombMap.Dart}
    {n m : ℕ} (hface : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = Delta.toCombMap.faceOf d)
    (hout : Delta.toCombMap.faceOf d ≠ Delta.outerFace)
    (hor : AvoidEdgeStep.Oriented Delta.toCombMap Delta.outerFace d)
    (hinj : ∀ a b, a < n → b < n →
      (Delta.toCombMap.facePerm ^ a) d = (Delta.toCombMap.facePerm ^ b) d → a = b)
    (hall : ∀ x, Delta.toCombMap.faceOf x = Delta.toCombMap.faceOf d →
      ∃ t < n, (Delta.toCombMap.facePerm ^ t) d = x)
    (hmn : m + 1 < n) (hm : (Delta.toCombMap.facePerm ^ (m + 1)) d = Delta.toCombMap.alpha d)
    (hpos : 0 < m) :
    EnclosedFaceSetSucc Delta (farFaces Delta.toCombMap d) (pocketWalk Delta.toCombMap d m) where
  outerFace_not_mem := by
    intro hmem
    obtain ⟨-, y, hy, hfar⟩ := mem_farFaces.mp hmem
    obtain ⟨o, ho, hdo⟩ := hor
    have hoy := AvoidEdgeStep.eqvGen_of_faceOf_eq (d := d) (ho.trans hy.symm)
      (fun h => hout (h.trans ho)) (fun h => hout (hface.symm.trans (h.trans ho)))
    exact AvoidEdgeStep.not_eqvGen_alpha_of_sameFace Delta.toCombMap Delta.planar d hface.symm
      (.trans _ _ _ hdo (.trans _ _ _ hoy hfar))
  ne_nil := List.ne_nil_of_length_pos (by rw [pocketWalk_length]; exact hpos)
  nodup := by
    refine List.Nodup.map_on (fun a ha b hb h => ?_) List.nodup_range
    rw [List.mem_range] at ha hb
    have := hinj (a + 1) (b + 1) (by omega) (by omega) h
    omega
  chain := by
    refine List.isChain_iff_getElem.mpr fun k hk => ?_
    rw [pocketWalk_getElem, pocketWalk_getElem, vertexOf_alpha_eq_facePerm, pow_succ' _ (k + 1),
      Equiv.Perm.mul_apply]
  closes := by
    rw [List.getLast_eq_getElem, List.head_eq_getElem, pocketWalk_getElem, pocketWalk_getElem,
      pocketWalk_length, Nat.sub_add_cancel hpos, vertexOf_alpha_eq_facePerm, ← Equiv.Perm.mul_apply,
      ← pow_succ', hm, vertexOf_alpha_eq_facePerm, zero_add, pow_one]
  mem_iff := by
    intro x
    constructor
    · intro hx
      obtain ⟨t, ht, rfl⟩ := mem_pocketWalk.mp hx
      refine ⟨by rw [faceOf_pow]; exact faceOf_not_mem_farFaces d, ?_⟩
      have hfar := far_pow hinj hmn hm (t := t + 1) (by omega) (by omega)
      have hne_d : (Delta.toCombMap.facePerm ^ (t + 1)) d ≠ d := fun h => by
        have := hinj (t + 1) 0 (by omega) (by omega) (by rw [pow_zero, Equiv.Perm.one_apply]; exact h)
        omega
      have hne_a : (Delta.toCombMap.facePerm ^ (t + 1)) d ≠ Delta.toCombMap.alpha d := fun h => by
        have := hinj (t + 1) (m + 1) (by omega) hmn (h.trans hm.symm)
        omega
      have hfarα := (far_alpha_iff hne_d hne_a).mpr hfar
      by_cases hα : Delta.toCombMap.faceOf (Delta.toCombMap.alpha ((Delta.toCombMap.facePerm ^ (t + 1)) d)) =
          Delta.toCombMap.faceOf d
      · right
        obtain ⟨s, hs, hseq⟩ := hall _ hα
        have hs' := (far_pow_iff Delta.planar hface hinj hmn hm hs).mp (by rw [hseq]; exact hfarα)
        have hsm : s ≠ m + 1 := fun h => hne_d (Delta.toCombMap.alpha.injective (by rw [← hseq, h, hm]))
        exact mem_pocketWalk.mpr ⟨s - 1, by omega, by rw [Nat.sub_add_cancel (by omega)]; exact hseq⟩
      · left
        exact (far_iff_mem_farFaces hface hα).mp hfarα
    · rintro ⟨hnot, hα⟩
      have hfar : Far Delta.toCombMap d x ∧ x ≠ Delta.toCombMap.alpha d := by
        rcases hα with hmem | hmem
        · have hne := (mem_farFaces.mp hmem).1
          have hfarα := (far_iff_mem_farFaces hface hne).mpr hmem
          have hxd : x ≠ d := fun h => hne (by rw [h]; exact hface)
          have hxa : x ≠ Delta.toCombMap.alpha d := fun h => hne (by rw [h, Delta.toCombMap.alpha_involutive])
          exact ⟨(far_alpha_iff hxd hxa).mp hfarα, hxa⟩
        · obtain ⟨s, hs, hseq⟩ := mem_pocketWalk.mp hmem
          have hfarα : Far Delta.toCombMap d (Delta.toCombMap.alpha x) := by
            rw [← hseq]
            exact far_pow hinj hmn hm (by omega) (by omega)
          have hxd : x ≠ d := fun h => by
            have h2 : (Delta.toCombMap.facePerm ^ (s + 1)) d = (Delta.toCombMap.facePerm ^ (m + 1)) d := by
              rw [hseq, h, hm]
            have := hinj (s + 1) (m + 1) (by omega) hmn h2
            omega
          have hxa : x ≠ Delta.toCombMap.alpha d := fun h => by
            have h2 : (Delta.toCombMap.facePerm ^ (s + 1)) d = (Delta.toCombMap.facePerm ^ 0) d := by
              rw [hseq, h, Delta.toCombMap.alpha_involutive, pow_zero, Equiv.Perm.one_apply]
            have := hinj (s + 1) 0 (by omega) (by omega) h2
            omega
          exact ⟨(far_alpha_iff hxd hxa).mp hfarα, hxa⟩
      obtain ⟨hfarx, hxa⟩ := hfar
      have hfx : Delta.toCombMap.faceOf x = Delta.toCombMap.faceOf d := by
        by_contra hne
        exact hnot ((far_iff_mem_farFaces hface hne).mp hfarx)
      obtain ⟨t, ht, rfl⟩ := hall x hfx
      have hrange := (far_pow_iff Delta.planar hface hinj hmn hm ht).mp hfarx
      have htm : t ≠ m + 1 := fun h => hxa (by rw [h, hm])
      exact mem_pocketWalk.mpr ⟨t - 1, by omega, by rw [Nat.sub_add_cancel (by omega)]⟩
  turn_mem := by
    intro x hx m' hm' hkeep hmin
    obtain ⟨k, hk, rfl⟩ := mem_pocketWalk.mp hx
    rw [first_turn_pocket hinj hmn hm hpos hk hm' hkeep hmin]
    exact mem_pocketWalk.mpr ⟨(k + 1) % m, Nat.mod_lt _ hpos, rfl⟩
  turn_next := by
    intro k hk m' hm' hkeep hmin
    simp only [pocketWalk_getElem, pocketWalk_length] at hkeep hmin ⊢
    exact first_turn_pocket hinj hmn hm hpos (by rw [pocketWalk_length] at hk; exact hk) hm' hkeep hmin

end Walk

/-- The arc of cell `i` right after the position `k` of the dart `d`. -/
def pocketArc (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) (k m : ℕ)
    (hk : k < (cellDarts Delta i).length) (hm : m ≤ (cellDarts Delta i).length) :
    CyclicArc (cellDarts Delta i) where
  start := ⟨k + 1, by omega⟩
  length := m
  length_le := hm

/-- **The pocket walk is an arc of cell `i`.** -/
theorem pocketArc_darts (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) {k m : ℕ}
    (hk : k < (cellDarts Delta i).length) (hm : m ≤ (cellDarts Delta i).length) :
    (pocketArc Delta i k m hk hm).darts =
      pocketWalk Delta.toCombMap (cellDarts Delta i)[k] m := by
  refine List.ext_getElem (by rw [CyclicArc.darts_length, pocketWalk_length]; rfl) fun t h1 h2 => ?_
  have hk' : k < (Delta.faceBoundary (cell Delta i).face).darts.length := hk
  have hA := OsinUnboundSameCellCycle.getElem_darts (cycle := cellDarts Delta i)
    (Delta.faceBoundary (cell Delta i).face) rfl (pocketArc Delta i k m hk hm) h1
  have hstep := OsinUnboundSameCellCycle.getElem_mod_pow (Delta.faceBoundary (cell Delta i).face) hk' 1
  rw [hA, pocketWalk_getElem]
  change (Delta.toCombMap.facePerm ^ t)
      ((Delta.faceBoundary (cell Delta i).face).darts[(k + 1) %
        (Delta.faceBoundary (cell Delta i).face).darts.length]'(Nat.mod_lt _ (by omega))) =
    (Delta.toCombMap.facePerm ^ (t + 1)) ((Delta.faceBoundary (cell Delta i).face).darts[k]'hk')
  rw [hstep, ← Equiv.Perm.mul_apply, ← pow_add]

/-- **The pocket of a same-face bridge dart with a far relator cell is an enclosed face set.** -/
theorem exists_enclosedPocket (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount)
    {d : Delta.toCombMap.Dart} (hd : d ∈ cellDarts Delta i)
    (hface : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = (cell Delta i).face)
    (hor : AvoidEdgeStep.Oriented Delta.toCombMap Delta.outerFace d)
    {C : RelatorCell Delta.toCombMap Delta.outerFace W} (hCi : C.face ≠ (cell Delta i).face)
    {x : Delta.toCombMap.Dart} (hx : Delta.toCombMap.faceOf x = C.face)
    (hch : Relation.EqvGen (AvoidEdgeStep Delta.toCombMap d) x (Delta.toCombMap.alpha d)) :
    ∃ A : CyclicArc (cellDarts Delta i),
      EnclosedFaceSetSucc Delta (farFaces Delta.toCombMap d) A.darts ∧
        C.face ∈ farFaces Delta.toCombMap d ∧ (cell Delta i).face ∉ farFaces Delta.toCombMap d := by
  have hdface : Delta.toCombMap.faceOf d = (cell Delta i).face :=
    ((Delta.faceBoundary (cell Delta i).face).mem_iff d).mp hd
  have hface' : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = Delta.toCombMap.faceOf d :=
    hface.trans hdface.symm
  obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hd
  have hk' : k < (Delta.faceBoundary (cell Delta i).face).darts.length := hk
  have hinj : ∀ a b, a < (cellDarts Delta i).length → b < (cellDarts Delta i).length →
      (Delta.toCombMap.facePerm ^ a) d = (Delta.toCombMap.facePerm ^ b) d → a = b := by
    intro a b ha hb h
    exact OsinUnboundSameCellCycle.pow_inj (Delta.faceBoundary (cell Delta i).face) hk' ha hb
      (by rw [show (Delta.faceBoundary (cell Delta i).face).darts[k] = d from hkd]; exact h)
  have hall : ∀ y, Delta.toCombMap.faceOf y = Delta.toCombMap.faceOf d →
      ∃ t < (cellDarts Delta i).length, (Delta.toCombMap.facePerm ^ t) d = y := by
    intro y hy
    have hmem : y ∈ (Delta.faceBoundary (cell Delta i).face).darts :=
      ((Delta.faceBoundary (cell Delta i).face).mem_iff y).mpr (hy.trans hdface)
    obtain ⟨t, ht, heq⟩ := OsinUnboundSameCellCycle.exists_pow_eq (Delta.faceBoundary (cell Delta i).face) hk' hmem
    exact ⟨t, ht, by rwa [show (Delta.faceBoundary (cell Delta i).face).darts[k] = d from hkd] at heq⟩
  obtain ⟨j, hj, hjeq⟩ := hall (Delta.toCombMap.alpha d) hface'
  have hj0 : j ≠ 0 := fun h => Delta.toCombMap.alpha_fixedPointFree d
    (by rw [← hjeq, h, pow_zero, Equiv.Perm.one_apply])
  have hmn : j - 1 + 1 < (cellDarts Delta i).length := by omega
  have hm : (Delta.toCombMap.facePerm ^ (j - 1 + 1)) d = Delta.toCombMap.alpha d := by
    rw [Nat.sub_add_cancel (by omega)]
    exact hjeq
  have hpos : 0 < j - 1 := by
    by_contra hzero
    have hj1 : j = 1 := by omega
    have hfix : Delta.toCombMap.sigma (Delta.toCombMap.alpha d) = Delta.toCombMap.alpha d := by
      have h := hjeq
      rw [hj1, pow_one] at h
      exact h
    have hxa := (AvoidEdgeStep.eq_iff_of_sigma_fixed (Or.inr rfl) hfix hch).mpr rfl
    exact hCi (hx.symm.trans (by rw [hxa]; exact hface))
  have hout : Delta.toCombMap.faceOf d ≠ Delta.outerFace := hdface ▸ (cell Delta i).face_ne_outer
  have E := enclosedFaceSetSucc_pocketWalk Delta hface' hout hor hinj hall hmn hm hpos
  refine ⟨pocketArc Delta i k (j - 1) hk (by omega), ?_, ?_, ?_⟩
  · rw [pocketArc_darts, show (cellDarts Delta i)[k] = d from hkd]
    exact E
  · exact mem_farFaces.mpr ⟨hdface ▸ hCi, x, hx, hch⟩
  · rw [← hdface]
    exact faceOf_not_mem_farFaces d

end SameCellPocketEnclosed

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.SameCellPocketEnclosed

#audit_axioms first_turn_pocket
#audit_axioms enclosedFaceSetSucc_pocketWalk
#audit_axioms pocketArc_darts
#audit_axioms exists_enclosedPocket
