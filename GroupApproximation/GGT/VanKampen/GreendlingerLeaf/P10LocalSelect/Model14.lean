import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Model14Pocket
import GroupApproximation.Meta.AxiomGuard

/-!
# The 14-dart shared-rose model: a witness for the kept sub-walk core

On the pocket `m14_pK` (`Model14Pocket`), a three-passage rose vertex `w` is visited by both
stretches of the first-turn contact vertex `v`:

* the stretch `[0,8,2]` holding the kept cell `K` fails the turning condition at `w`;
* the stretch `[4,6]` has side `{P_B, lake}`, with no relator cell.

The walk `B = [0,2]` (the kept stretch with its excursion `[8]` cut out at `w`) satisfies every
conjunct of the conclusion of `Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement`:

* `m14_conclusion`: the conclusion on this model, with `q` true exactly on `0` and `2`.

`Model14Core.m14_core_instance` checks that `m14_Conclusion` is the core's conclusion and that
`m14_leastArea`, `m14_letters`, `m14_closedWalk`, `m14_notFirst`, `m14_srcLt`, `m14_tgtLt`,
`m14_notUnpinched` and `m14_allCrossed` are exactly its hypotheses.

The side conditions are met through their second disjuncts: `B` meets the target arc (`2`), the
reversed source arc (`0`), and has a dart on the relator cell `K` (`0`).

Proof route: `decide` on the listed darts.  Truth witness for the local selection lemma of
`P10LocalSelect`; it certifies no printed sentence on its own.

Manuscript status: infrastructure (a truth witness) for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open OsinPocketPinchedTwoGonModel (D)

/-- The kept walk: the darts `0 = a_S` and `2 = a_E`. -/
def m14_q (d : Fin 14) : Bool :=
  (![true, false, true, false, false, false, false, false, false, false, false, false, false,
    false] : Fin 14 → Bool) d

/-- **The conclusion of the kept sub-walk core on the 14-dart model.** -/
def m14_Conclusion : Prop :=
  ∃ q : m14_X.toCombMap.Dart → Bool,
    m14_pK.boundary.cycle.filter q ≠ [] ∧
    (m14_pK.boundary.cycle.filter q).IsChain (fun d e =>
      m14_X.toCombMap.vertexOf (m14_X.toCombMap.alpha d) = m14_X.toCombMap.vertexOf e) ∧
    (∀ hne : m14_pK.boundary.cycle.filter q ≠ [],
      m14_X.toCombMap.vertexOf
          (m14_X.toCombMap.alpha ((m14_pK.boundary.cycle.filter q).getLast hne)) =
        m14_X.toCombMap.vertexOf ((m14_pK.boundary.cycle.filter q).head hne)) ∧
    (∀ d ∈ m14_pK.boundary.cycle.filter q, ∀ m : ℕ, 0 < m →
      walkKeep m14_X.toCombMap (m14_pK.boundary.cycle.filter q)
        ((m14_X.toCombMap.sigma ^ m) (m14_X.toCombMap.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ walkKeep m14_X.toCombMap (m14_pK.boundary.cycle.filter q)
        ((m14_X.toCombMap.sigma ^ k) (m14_X.toCombMap.alpha d))) →
      (m14_X.toCombMap.sigma ^ m) (m14_X.toCombMap.alpha d) ∈
        m14_pK.boundary.cycle.filter q) ∧
    (∃ y ∈ m14_pK.boundary.cycle, q y = false) ∧
    (m14_X.outerFace ∉ sideFaces m14_X.toCombMap (m14_pK.boundary.cycle.filter q) ∨
      ∃ d ∈ m14_pK.targetArc.darts, q d = true) ∧
    ((cell m14_X m14_pK.source).face ∉
        sideFaces m14_X.toCombMap (m14_pK.boundary.cycle.filter q) ∨
      ∃ d ∈ invDarts m14_X m14_pK.sourceArc.darts, q d = true) ∧
    ((∃ kept : Fin m14_X.rCellCount,
      (cell m14_X kept).face ∈ sideFaces m14_X.toCombMap (m14_pK.boundary.cycle.filter q)) ∨
      ∃ d ∈ m14_pK.boundary.cycle, q d = true ∧
        ∃ kept : Fin m14_X.rCellCount, m14_X.toCombMap.faceOf d = (cell m14_X kept).face) ∧
    GroupApproximation.Full.GL05b.IsEndBlock q (invDarts m14_X m14_pK.sourceArc.darts) ∧
    ∃ i, m14_pK.targetArc.darts.filter q = m14_pK.targetArc.darts.take i ∨
      (m14_pK.targetArc.darts.filter q = m14_pK.targetArc.darts.drop i ∧
        m14_pK.targetArc.start.1 + i ≤ (outerDarts m14_X).length)

theorem m14_filter_mem : ∀ d, d ∈ m14_pK.boundary.cycle.filter m14_q → d = 0 ∨ d = 2 := by
  decide

/-- **`B = [0,2]` is a kept walk** on the 14-dart model. -/
theorem m14_conclusion : m14_Conclusion := by
  have hchain : List.IsChain (fun d e : Fin 14 => m14_vClass (m14_M.alpha d) = m14_vClass e)
      (m14_cyc.filter m14_q) := by
    decide
  have hclose : ∀ hne : m14_cyc.filter m14_q ≠ [],
      m14_vClass (m14_M.alpha ((m14_cyc.filter m14_q).getLast hne)) =
        m14_vClass ((m14_cyc.filter m14_q).head hne) := by
    decide
  refine ⟨m14_q, by decide, hchain.imp (by intro a b hab; exact (m14_vClass_iff _ _).mpr hab),
    fun hne => (m14_vClass_iff _ _).mpr (hclose hne), ?_, ⟨8, by decide, rfl⟩,
    Or.inr ⟨2, ?_, rfl⟩, Or.inr ⟨0, ?_, rfl⟩,
    Or.inr ⟨0, by decide, rfl, m14_iK, (m14_faceOf_eq_face 0 0).mpr rfl⟩,
    ⟨1, Or.inr ?_⟩, ⟨1, Or.inl ?_⟩⟩
  · intro d hd m hm hkeep hmin
    rcases m14_filter_mem d hd with rfl | rfl
    · rcases Nat.lt_or_ge m 2 with hlt | hge
      · interval_cases m
        decide
      · exact (hmin 1 (by omega) (by omega) (Or.inl (by decide))).elim
    · rcases Nat.lt_or_ge m 2 with hlt | hge
      · interval_cases m
        decide
      · exact (hmin 1 (by omega) (by omega) (Or.inl (by decide))).elim
  · show 2 ∈ m14_tArc.darts
    rw [m14_tArc_darts]
    decide
  · show 0 ∈ invDarts m14_X m14_sArc.darts
    rw [m14_sArc_darts]
    decide
  · show (invDarts m14_X m14_sArc.darts).filter m14_q = (invDarts m14_X m14_sArc.darts).drop 1
    rw [m14_sArc_darts]
    decide
  · show m14_tArc.darts.filter m14_q = m14_tArc.darts.take 1
    rw [m14_tArc_darts]
    decide

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.m14_conclusion
