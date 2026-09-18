import GroupApproximation.Manuscript.NonMF.Full.GL01.Switch
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellSides
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingChains
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PendantRemoval
import GroupApproximation.Meta.AxiomGuard

/-!
# GL01: a switch has no bridges

*GL01 copy.*  This re-proves the bridge exclusion of the foreign module
`GreendlingerLeaf.P01EmptyTwoGon.SwitchCornerBridge` (origin/main blob `0735c3baf`).  That module
imports `TouchCornerSwitch`, which is last changed by a commit marked WIP, so it is not imported.
Only the residual statement and its reductions are dropped.

Infrastructure for `thm:hull` in non_mf_groups_exist.tex, through Osin, arXiv:math/0411039v3,
§9, proof of Lemma 9.4.  It certifies no printed sentence on its own.

Notation: `M = S.diagram.toCombMap`, `φ = M.facePerm`, `α = M.alpha`, and `e t = φ^t d`.
`AvoidEdgeStep M b` is a vertex rotation, or a reversal at an edge other than the edge of `b`.

`SwitchCornerExcluded P` (module `GL01.Switch`) excludes a stretch `d, e 1, …, e m` of the polygon
face `F = P.face k` with these properties:
* `α d` lies on `A = objectFace o` and `α (e m)` on `B = objectFace o'`, where `o ≠ o'`;
* every interior dart has `F` on both sides;
* a polygon `k' ≠ k` has darts `x` across `A` and `y` across `B`.

`switchCornerExcluded_of_one` reduces this to `m = 1`, which is `OneCornerExcluded P`.  Suppose
`m ≥ 2`.
1. The darts `e 0, …, e m` are distinct (`stretch_pow_ne_pow`).
2. No `α (e p) = e q` for `0 < p < q < m` (`stretch_alpha_ne`).  The proof is by induction on
   `q - p`: adjacent darts would give a leaf `φ z = α z`, which `S.DartMinimal` excludes, and
   otherwise the edge of `e (p+1)` is a bridge that the walk avoids.
3. The bridge `b = e 1` is joined to `α b` by a walk avoiding its edge (`false_of_bridge_stretch`).
   The walk runs `α b ~ e 2 ~ … ~ e m ~ α (e m) ~ α y ~ y ~ x ~ α x ~ α d ~ b`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

section StretchCombinatorics

/-- One more face step. -/
theorem switchPow_succ_apply (M : CombMap) (x : M.Dart) (i : ℕ) :
    M.facePerm ((M.facePerm ^ i) x) = (M.facePerm ^ (i + 1)) x := by
  rw [pow_succ', Equiv.Perm.mul_apply]

/-- The first face step. -/
theorem switchPow_one_apply (M : CombMap) (x : M.Dart) :
    M.facePerm x = (M.facePerm ^ 1) x := by
  rw [pow_one]

/-- A vertex rotation from the reverse of `x` reaches `φ x`, avoiding any edge. -/
theorem avoid_sigma_step {M : CombMap} (b : M.Dart) {x y : M.Dart}
    (hxy : M.facePerm x = y) : Relation.EqvGen (AvoidEdgeStep M b) (M.alpha x) y := by
  subst hxy
  exact Relation.EqvGen.rel _ _ (Or.inl rfl)

/-- A reversal at an edge other than the edge of `b`. -/
theorem avoid_alpha_step {M : CombMap} {b x y : M.Dart} (hxb : x ≠ b) (hxa : x ≠ M.alpha b)
    (hxy : M.alpha x = y) : Relation.EqvGen (AvoidEdgeStep M b) x y :=
  Relation.EqvGen.rel _ _ (Or.inr ⟨hxb, hxa, hxy⟩)

/-- A face step from a dart off the edge of `b`. -/
theorem avoid_face_step {M : CombMap} {b x y : M.Dart} (hxb : x ≠ b) (hxa : x ≠ M.alpha b)
    (hxy : M.facePerm x = y) : Relation.EqvGen (AvoidEdgeStep M b) x y := by
  subst hxy
  exact AvoidEdgeStep.eqvGen_facePerm hxb hxa

/-- **Step 1: the darts of the stretch are distinct.** -/
theorem stretch_pow_ne_pow {M : CombMap} {F : M.Face} {d : M.Dart} {m : ℕ}
    (hint : ∀ i : ℕ, 0 < i → i < m → M.faceOf (M.alpha ((M.facePerm ^ i) d)) = F)
    (h0 : M.faceOf (M.alpha d) ≠ F)
    (hm : M.faceOf (M.alpha ((M.facePerm ^ m) d)) ≠ M.faceOf (M.alpha d))
    (s t : ℕ) (hst : s < t) (htm : t ≤ m) :
    (M.facePerm ^ s) d ≠ (M.facePerm ^ t) d := by
  intro h
  have hn : (M.facePerm ^ (t - s)) d = d := by
    apply (M.facePerm ^ s).injective
    rw [facePerm_pow_apply_pow, Nat.add_sub_of_le hst.le]
    exact h.symm
  rcases Nat.lt_or_ge (t - s) m with hlt | hge
  · exact h0 ((congrArg (fun x => M.faceOf (M.alpha x)) hn).symm.trans
      (hint (t - s) (Nat.sub_pos_of_lt hst) hlt))
  · have hms : m = t - s := by omega
    apply hm
    rw [hms, hn]

/-- **Step 2: no reverse pairs inside the stretch.** -/
theorem stretch_alpha_ne {M : CombMap} (hM : M.IsPlanar) {F : M.Face} {d : M.Dart} {m : ℕ}
    (hd : M.faceOf d = F)
    (hint : ∀ i : ℕ, 0 < i → i < m → M.faceOf (M.alpha ((M.facePerm ^ i) d)) = F)
    (hdist : ∀ s t : ℕ, s < t → t ≤ m → (M.facePerm ^ s) d ≠ (M.facePerm ^ t) d)
    (hleaf : ∀ z : M.Dart, M.faceOf z = F → M.facePerm z ≠ M.alpha z) :
    ∀ p q : ℕ, 0 < p → p < q → q < m →
      M.alpha ((M.facePerm ^ p) d) ≠ (M.facePerm ^ q) d := by
  suffices key : ∀ g p q : ℕ, q - p ≤ g → 0 < p → p < q → q < m →
      M.alpha ((M.facePerm ^ p) d) ≠ (M.facePerm ^ q) d from
    fun p q => key (q - p) p q le_rfl
  intro g
  induction g with
  | zero =>
    intro p q hg _ hpq _
    exact absurd hpq (by omega)
  | succ g ih =>
    intro p q hg hp hpq hqm heq
    rcases Nat.lt_or_ge (p + 1) q with hgap | hadj
    · have hb : M.faceOf ((M.facePerm ^ (p + 1)) d) = F :=
        (faceOf_facePerm_pow M d (p + 1)).trans hd
      have hab : M.faceOf (M.alpha ((M.facePerm ^ (p + 1)) d)) = F :=
        hint (p + 1) (Nat.succ_pos p) (by omega)
      have h1 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ (p + 1)) d))
          (M.alpha ((M.facePerm ^ (p + 1)) d)) ((M.facePerm ^ (p + 1 + 1)) d) :=
        avoid_sigma_step _ (switchPow_succ_apply M d (p + 1))
      have h2 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ (p + 1)) d))
          ((M.facePerm ^ (p + 1 + 1)) d) ((M.facePerm ^ q) d) :=
        AvoidEdgeStep.eqvGen_facePerm_pow_of_le d (by omega) fun t ht htq =>
          ⟨fun h => hdist (p + 1) t (by omega) (by omega) h.symm,
            fun h => ih (p + 1) t (by omega) (by omega) (by omega) (by omega) h.symm⟩
      have h3 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ (p + 1)) d))
          ((M.facePerm ^ q) d) ((M.facePerm ^ p) d) :=
        avoid_alpha_step (fun h => hdist (p + 1) q hgap hqm.le h.symm)
          (fun h => hdist p (p + 1) (Nat.lt_succ_self p) (by omega)
            (M.alpha_involutive.injective (heq.trans h)))
          (by rw [← heq]; exact M.alpha_involutive _)
      have h4 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ (p + 1)) d))
          ((M.facePerm ^ p) d) ((M.facePerm ^ (p + 1)) d) :=
        avoid_face_step (hdist p (p + 1) (Nat.lt_succ_self p) (by omega))
          (fun h => ih p (p + 1) (by omega) hp (Nat.lt_succ_self p) (by omega)
            (by rw [h]; exact M.alpha_involutive _))
          (switchPow_succ_apply M d p)
      exact AvoidEdgeStep.not_eqvGen_alpha_of_sameFace M hM ((M.facePerm ^ (p + 1)) d)
        (hb.trans hab.symm)
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _ h1
          (Relation.EqvGen.trans _ _ _ h2 (Relation.EqvGen.trans _ _ _ h3 h4))))
    · have hq : q = p + 1 := by omega
      subst hq
      exact hleaf ((M.facePerm ^ p) d) ((faceOf_facePerm_pow M d p).trans hd)
        ((switchPow_succ_apply M d p).trans heq.symm)

/-- **Step 3: a stretch of length at least two contradicts the bridge at `e 1`.** -/
theorem false_of_bridge_stretch {M : CombMap} (hM : M.IsPlanar) {F A B F' : M.Face}
    {d : M.Dart} {m : ℕ} (hm : 1 < m) (hd : M.faceOf d = F)
    (hint : ∀ i : ℕ, 0 < i → i < m → M.faceOf (M.alpha ((M.facePerm ^ i) d)) = F)
    (hA : M.faceOf (M.alpha d) = A) (hB : M.faceOf (M.alpha ((M.facePerm ^ m) d)) = B)
    (hAB : A ≠ B) (hAF : A ≠ F) (hBF : B ≠ F) {x y : M.Dart}
    (hx : M.faceOf x = F') (hxA : M.faceOf (M.alpha x) = A)
    (hy : M.faceOf y = F') (hyB : M.faceOf (M.alpha y) = B) (hF' : F' ≠ F)
    (hleaf : ∀ z : M.Dart, M.faceOf z = F → M.facePerm z ≠ M.alpha z) : False := by
  have hdist : ∀ s t : ℕ, s < t → t ≤ m → (M.facePerm ^ s) d ≠ (M.facePerm ^ t) d :=
    stretch_pow_ne_pow hint (fun h => hAF (hA.symm.trans h))
      (fun h => hAB (hA.symm.trans (h.symm.trans hB)))
  have hpair : ∀ p q : ℕ, 0 < p → p < q → q < m →
      M.alpha ((M.facePerm ^ p) d) ≠ (M.facePerm ^ q) d :=
    stretch_alpha_ne hM hd hint hdist hleaf
  have hb : M.faceOf ((M.facePerm ^ 1) d) = F := (faceOf_facePerm_pow M d 1).trans hd
  have hab : M.faceOf (M.alpha ((M.facePerm ^ 1) d)) = F := hint 1 Nat.one_pos hm
  have hmb : (M.facePerm ^ m) d ≠ M.alpha ((M.facePerm ^ 1) d) := by
    intro h
    apply hBF
    rw [← hB, h, M.alpha_involutive]
    exact hb
  have h1 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ 1) d))
      (M.alpha ((M.facePerm ^ 1) d)) ((M.facePerm ^ (1 + 1)) d) :=
    avoid_sigma_step _ (switchPow_succ_apply M d 1)
  have h2 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ 1) d))
      ((M.facePerm ^ (1 + 1)) d) ((M.facePerm ^ m) d) :=
    AvoidEdgeStep.eqvGen_facePerm_pow_of_le d (by omega) fun t ht htm =>
      ⟨fun h => hdist 1 t (by omega) htm.le h.symm,
        fun h => hpair 1 t Nat.one_pos (by omega) htm h.symm⟩
  have h3 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ 1) d))
      ((M.facePerm ^ m) d) (M.alpha ((M.facePerm ^ m) d)) :=
    avoid_alpha_step (fun h => hdist 1 m hm le_rfl h.symm) hmb rfl
  have h4 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ 1) d))
      (M.alpha ((M.facePerm ^ m) d)) (M.alpha y) :=
    AvoidEdgeStep.eqvGen_of_faceOf_eq (hB.trans hyB.symm)
      (fun h => hBF (hB.symm.trans (h.symm.trans hb)))
      (fun h => hBF (hB.symm.trans (h.symm.trans hab)))
  have h5 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ 1) d)) (M.alpha y) y :=
    Relation.EqvGen.symm _ _ (avoid_alpha_step
      (fun h => hF' (hy.symm.trans ((congrArg M.faceOf h).trans hb)))
      (fun h => hF' (hy.symm.trans ((congrArg M.faceOf h).trans hab))) rfl)
  have h6 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ 1) d)) y x :=
    AvoidEdgeStep.eqvGen_of_faceOf_eq (hy.trans hx.symm)
      (fun h => hF' (hy.symm.trans (h.symm.trans hb)))
      (fun h => hF' (hy.symm.trans (h.symm.trans hab)))
  have h7 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ 1) d)) x (M.alpha x) :=
    avoid_alpha_step (fun h => hF' (hx.symm.trans ((congrArg M.faceOf h).trans hb)))
      (fun h => hF' (hx.symm.trans ((congrArg M.faceOf h).trans hab))) rfl
  have h8 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ 1) d)) (M.alpha x) (M.alpha d) :=
    AvoidEdgeStep.eqvGen_of_faceOf_eq (hxA.trans hA.symm)
      (fun h => hAF (hxA.symm.trans (h.symm.trans hb)))
      (fun h => hAF (hxA.symm.trans (h.symm.trans hab)))
  have h9 : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ 1) d))
      (M.alpha d) ((M.facePerm ^ 1) d) :=
    avoid_sigma_step _ (switchPow_one_apply M d)
  exact AvoidEdgeStep.not_eqvGen_alpha_of_sameFace M hM ((M.facePerm ^ 1) d) (hb.trans hab.symm)
    (Relation.EqvGen.symm _ _
      (Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.trans _ _ _ h2
        (Relation.EqvGen.trans _ _ _ h3 (Relation.EqvGen.trans _ _ _ h4
          (Relation.EqvGen.trans _ _ _ h5 (Relation.EqvGen.trans _ _ _ h6
            (Relation.EqvGen.trans _ _ _ h7 (Relation.EqvGen.trans _ _ _ h8 h9)))))))))

end StretchCombinatorics

section SwitchCornerBridge

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **The triangle corner**: a dart `d` of polygon `k` with `o` across `d` and `o′ ≠ o` across
`φ d`, while a second polygon `k′` touches both `o` and `o′`. -/
def OneCornerExcluded (P : OsinLemma94RealizedPolygons S) : Prop :=
  ∀ k k' : Fin P.count, k ≠ k' →
    ∀ o o' : Option (Fin S.diagram.rCellCount), o ≠ o' →
      ∀ d : S.diagram.toCombMap.Dart,
        S.diagram.toCombMap.faceOf d = P.face k →
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) =
          OsinLemma94RealizedPolygons.objectFace S o →
        S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha (S.diagram.toCombMap.facePerm d)) =
          OsinLemma94RealizedPolygons.objectFace S o' →
        (∃ e, S.diagram.toCombMap.faceOf e = P.face k' ∧ S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha e) = OsinLemma94RealizedPolygons.objectFace S o) →
        (∃ e, S.diagram.toCombMap.faceOf e = P.face k' ∧ S.diagram.toCombMap.faceOf
          (S.diagram.toCombMap.alpha e) = OsinLemma94RealizedPolygons.objectFace S o') →
        False

/-- **The switch configuration from the triangle corner**: the bridges of a switch are absent,
so the switch is a triangle corner. -/
theorem switchCornerExcluded_of_one (P : OsinLemma94RealizedPolygons S) (hS : S.DartMinimal)
    (hone : OneCornerExcluded P) : SwitchCornerExcluded P := by
  intro k k' hkk o o' hoo d m hm hd h0 hmo hint hw hw'
  obtain ⟨x, hx, hxo⟩ := hw
  obtain ⟨y, hy, hyo'⟩ := hw'
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  · have hunsel : S.UnselectedGFace (P.face k) :=
      ⟨P.face_ne_outer k, relatorCell_face_ne P k, P.face_unselected k⟩
    exact false_of_bridge_stretch S.diagram.planar hm1 hd hint h0 hmo
      (fun h => hoo (OsinLemma94RealizedPolygons.objectFace_injective S h))
      (OsinLemma94RealizedPolygons.objectFace_ne_face P k o)
      (OsinLemma94RealizedPolygons.objectFace_ne_face P k o') hx hxo hy hyo'
      (fun h => hkk (P.face_injective h).symm)
      (fun z hz hleaf => GloballyDistinguishedSectionFamily.not_leaf_of_dartMinimal
        GloballyDistinguishedSectionFamily.pendantPathRemovalInput hS hunsel hz hleaf)
  · obtain rfl : m = 1 := Nat.le_antisymm hm1 hm
    rw [pow_one] at hmo
    exact hone k k' hkk o o' hoo d hd h0 hmo ⟨x, hx, hxo⟩ ⟨y, hy, hyo'⟩

end SwitchCornerBridge

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.stretch_pow_ne_pow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.stretch_alpha_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.false_of_bridge_stretch
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.switchCornerExcluded_of_one
