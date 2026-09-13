import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerRegionFaces
import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.GGT.VanKampen.CombMapDual
import GroupApproximation.GGT.VanKampen.CombMapEdgeInsertion
import GroupApproximation.Meta.AxiomGuard

/-!
# Restricting a map after inserting an edge at a face corner

Let `a` be a dart of `M` and `b = facePerm a` its successor on its face, and insert an edge
between the corners before `a` and before `b` (`EdgeInsertion.toCombMap M a b`).  The face cycle
of `a` becomes the digon `none, a`, and the old face of `a` reads `some none` in the place of `a`.

Retain an edge-invariant dart set `K` of `M` that contains `a` and `b`, and a dart set `K'` of the
new map that contains the new darts and agrees with `K` on the old darts.  The first-return
rotation of the new restriction is the old one, with the new darts inserted before `a` and `b`
(`restrict_sigma_embed`).  So `toNew`, which renames `a` to `some none`, commutes with face
rotation (`facePerm_toNew`).  A second restriction, of the duals, to dart sets that avoid the
digon is isomorphic to the old one (`toPhi`), and every face-class step of the new dual retracts
to a face-class chain of the old dual (`eqvGen_retract`).
-/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion.InsertionRestriction

open Equiv PermOrbitInsert CombMap
open scoped Classical

universe u

variable (M : CombMap.{u}) (a b : M.Dart)

/-- Where the rotation of an old dart lands after insertion, read off its old successor. -/
noncomputable def rotationImage (y : M.Dart) : (toCombMap M a b).Dart :=
  if y = a then some none else if y = b then none else embed M y

theorem rotationImage_of_ne {y : M.Dart} (ha : y ≠ a) (hb : y ≠ b) :
    rotationImage M a b y = embed M y := by
  rw [rotationImage, if_neg ha, if_neg hb]

theorem sigma_embed (z : M.Dart) :
    (toCombMap M a b).sigma (embed M z) = rotationImage M a b (M.sigma z) := by
  change insertBefore (insertBefore M.sigma a) (some b) (some (some z)) = _
  by_cases ha : M.sigma z = a
  · simp only [insertBefore_some, if_pos ha, reduceCtorEq, if_false, rotationImage]
  · by_cases hb : M.sigma z = b
    · simp only [insertBefore_some, if_neg ha, Option.some.injEq, if_pos hb, rotationImage]
    · simp only [insertBefore_some, if_neg ha, Option.some.injEq, if_neg hb, rotationImage,
        embed]

theorem sigma_positive (hab : a ≠ b) : (toCombMap M a b).sigma (some none) = embed M a := by
  change insertBefore (insertBefore M.sigma a) (some b) (some none) = some (some a)
  simp only [insertBefore_some, insertBefore_none, Option.some.injEq, if_neg hab]

theorem sigma_negative : (toCombMap M a b).sigma none = embed M b := by
  change insertBefore (insertBefore M.sigma a) (some b) none = some (some b)
  exact insertBefore_none _ _

variable (K : M.Dart → Prop) (K' : (toCombMap M a b).Dart → Prop)

theorem keep_rotationImage (hι : ∀ x, K' (embed M x) ↔ K x) (Kn : K' none)
    (Kp : K' (some none)) {y : M.Dart} (hy : K y) : K' (rotationImage M a b y) := by
  rw [rotationImage]
  split_ifs
  · exact Kp
  · exact Kn
  · exact (hι y).mpr hy

/-- **The rotation of the new restriction at an old dart.**  The skipped darts are not retained,
so they differ from `a` and `b`, and the new walk is the old one until its last step. -/
theorem restrict_sigma_embed (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b)
    (x : {d : M.Dart // K d}) (hx : K' (embed M x.1))
    (hy : K' (rotationImage M a b (PredicateRestriction.sigma M K x).1)) :
    PredicateRestriction.sigma (toCombMap M a b) K' ⟨embed M x.1, hx⟩ =
      ⟨rotationImage M a b (PredicateRestriction.sigma M K x).1, hy⟩ := by
  obtain ⟨m, hm, hreach, hskip⟩ := PredicateRestriction.sigma_firstReturn M K x
  have hreach' : (M.sigma ^ m) x.1 = (PredicateRestriction.sigma M K x).1 := hreach
  have hne : ∀ k, 0 < k → k < m → (M.sigma ^ k) x.1 ≠ a ∧ (M.sigma ^ k) x.1 ≠ b :=
    fun k hk hkm => ⟨fun h => hskip k hk hkm ⟨⟨a, Ka⟩, h.symm⟩,
      fun h => hskip k hk hkm ⟨⟨b, Kb⟩, h.symm⟩⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hwalk : ∀ k, k ≤ n →
      ((toCombMap M a b).sigma ^ k) (embed M x.1) = embed M ((M.sigma ^ k) x.1) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        obtain ⟨hka, hkb⟩ := hne (k + 1) (by omega) (by omega)
        rw [pow_succ' (toCombMap M a b).sigma, Perm.mul_apply, ih (by omega), sigma_embed,
          ← Perm.mul_apply, ← pow_succ', rotationImage_of_ne M a b hka hkb]
  refine PermFirstReturn.apply_eq_of_isFirstReturn
    (PredicateRestriction.sigma_firstReturn (toCombMap M a b) K') (m := n + 1) (by omega) ?_ ?_
  · change ((toCombMap M a b).sigma ^ (n + 1)) (embed M x.1) =
      rotationImage M a b (PredicateRestriction.sigma M K x).1
    rw [pow_succ' (toCombMap M a b).sigma, Perm.mul_apply, hwalk n le_rfl, sigma_embed,
      ← Perm.mul_apply, ← pow_succ', hreach']
  · rintro k hk hkn ⟨z, hz⟩
    have hz' : z.1 = ((toCombMap M a b).sigma ^ k) (embed M x.1) := hz
    rw [hwalk k (by omega)] at hz'
    exact hskip k hk hkn
      ⟨⟨(M.sigma ^ k) x.1, (hι ((M.sigma ^ k) x.1)).mp (by rw [← hz']; exact z.2)⟩, rfl⟩

theorem restrict_sigma_positive (hab : a ≠ b) (Kp : K' (some none)) (Ka' : K' (embed M a)) :
    PredicateRestriction.sigma (toCombMap M a b) K' ⟨some none, Kp⟩ = ⟨embed M a, Ka'⟩ :=
  PermFirstReturn.apply_eq_of_isFirstReturn
    (PredicateRestriction.sigma_firstReturn (toCombMap M a b) K') (m := 1) (by omega)
    (by rw [pow_one]; exact sigma_positive M a b hab) (by intro k hk hk1; omega)

theorem restrict_sigma_negative (Kn : K' none) (Kb' : K' (embed M b)) :
    PredicateRestriction.sigma (toCombMap M a b) K' ⟨none, Kn⟩ = ⟨embed M b, Kb'⟩ :=
  PermFirstReturn.apply_eq_of_isFirstReturn
    (PredicateRestriction.sigma_firstReturn (toCombMap M a b) K') (m := 1) (by omega)
    (by rw [pow_one]; exact sigma_negative M a b) (by intro k hk hk1; omega)

theorem restrict_sigma_alpha (hb : M.facePerm a = b) (Ka' : K (M.alpha a)) (Kb : K b) :
    PredicateRestriction.sigma M K ⟨M.alpha a, Ka'⟩ = ⟨b, Kb⟩ :=
  PermFirstReturn.apply_eq_of_isFirstReturn (PredicateRestriction.sigma_firstReturn M K)
    (m := 1) (by omega) (by rw [pow_one]; exact hb) (by intro k hk hk1; omega)

/-- The face rotation of a restriction, read at a value of the reversed dart. -/
theorem restrict_facePerm_val (N : CombMap.{u}) (keep : N.Dart → Prop)
    (hkeep : ∀ d, keep (N.alpha d) ↔ keep d) (y : (PredicateRestriction.toCombMap N keep hkeep).Dart)
    {z : N.Dart} (hz : N.alpha y.1 = z) (hkz : keep z) :
    ((PredicateRestriction.toCombMap N keep hkeep).facePerm y).1 =
      (PredicateRestriction.sigma N keep ⟨z, hkz⟩).1 := by
  subst hz
  rfl

/-- Old darts in the new map, with `a` renamed to the new dart `some none`. -/
noncomputable def renameDart (z : M.Dart) : (toCombMap M a b).Dart :=
  if z = a then some none else embed M z

theorem renameDart_injective : Function.Injective (renameDart M a b) := by
  intro y z h
  by_cases hy : y = a
  · by_cases hz : z = a
    · exact hy.trans hz.symm
    · rw [renameDart, if_pos hy, renameDart, if_neg hz] at h
      have h' : (some none : Option (Option M.Dart)) = some (some z) := h
      simp at h'
  · by_cases hz : z = a
    · rw [renameDart, if_neg hy, renameDart, if_pos hz] at h
      have h' : (some (some y) : Option (Option M.Dart)) = some none := h
      simp at h'
    · rw [renameDart, if_neg hy, renameDart, if_neg hz] at h
      exact Option.some.inj (Option.some.inj h)

variable (hK : ∀ d, K (M.alpha d) ↔ K d) (hK' : ∀ d, K' ((toCombMap M a b).alpha d) ↔ K' d)

/-- The retained old darts, renamed into the new restriction. -/
noncomputable def toNew (hι : ∀ x, K' (embed M x) ↔ K x) (Kp : K' (some none))
    (x : (PredicateRestriction.toCombMap M K hK).Dart) :
    (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').Dart :=
  ⟨renameDart M a b x.1, by
    rw [renameDart]
    split_ifs
    · exact Kp
    · exact (hι x.1).mpr x.2⟩

theorem toNew_injective (hι : ∀ x, K' (embed M x) ↔ K x) (Kp : K' (some none)) :
    Function.Injective (toNew M a b K K' hK hK' hι Kp) :=
  fun _ _ h => Subtype.ext (renameDart_injective M a b (congrArg Subtype.val h))

/-- **Renaming commutes with face rotation.**  At `a` the new rotation passes through the digon
dart `none` to `b`; elsewhere a return to `b` would force the dart to be `a`. -/
theorem facePerm_toNew (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b) (Kn : K' none)
    (Kp : K' (some none)) (hab : a ≠ b) (hb : M.facePerm a = b)
    (x : (PredicateRestriction.toCombMap M K hK).Dart) :
    (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').facePerm
        (toNew M a b K K' hK hK' hι Kp x) =
      toNew M a b K K' hK hK' hι Kp ((PredicateRestriction.toCombMap M K hK).facePerm x) := by
  obtain ⟨x, hx⟩ := x
  have hKa : K (M.alpha a) := (hK a).mpr Ka
  have hold := restrict_sigma_alpha M a b K hb hKa Kb
  apply Subtype.ext
  by_cases hxa : x = a
  · have hxs : renameDart M a b x = some none := by rw [renameDart, if_pos hxa]
    refine (restrict_facePerm_val (toCombMap M a b) K' hK' (toNew M a b K K' hK hK' hι Kp ⟨x, hx⟩)
      (z := none) ((congrArg (toCombMap M a b).alpha hxs).trans rfl) Kn).trans ?_
    refine (congrArg Subtype.val (restrict_sigma_negative M a b K' Kn ((hι b).mpr Kb))).trans ?_
    change embed M b = renameDart M a b ((PredicateRestriction.toCombMap M K hK).facePerm ⟨x, hx⟩).1
    rw [restrict_facePerm_val M K hK ⟨x, hx⟩ (z := M.alpha a) (congrArg M.alpha hxa) hKa, hold]
    show embed M b = renameDart M a b b
    rw [renameDart, if_neg (Ne.symm hab)]
  · have hxe : renameDart M a b x = embed M x := by rw [renameDart, if_neg hxa]
    have hKx : K' (embed M (M.alpha x)) := (hι _).mpr ((hK x).mpr hx)
    refine (restrict_facePerm_val (toCombMap M a b) K' hK' (toNew M a b K K' hK hK' hι Kp ⟨x, hx⟩)
      (z := embed M (M.alpha x)) ((congrArg (toCombMap M a b).alpha hxe).trans rfl) hKx).trans ?_
    refine (congrArg Subtype.val (restrict_sigma_embed M a b K K' hι Ka Kb
      ⟨M.alpha x, (hK x).mpr hx⟩ hKx
      (keep_rotationImage M a b K K' hι Kn Kp
        (PredicateRestriction.sigma M K ⟨M.alpha x, (hK x).mpr hx⟩).2))).trans ?_
    change rotationImage M a b (PredicateRestriction.sigma M K ⟨M.alpha x, (hK x).mpr hx⟩).1 =
      renameDart M a b (PredicateRestriction.sigma M K ⟨M.alpha x, (hK x).mpr hx⟩).1
    generalize hw : PredicateRestriction.sigma M K ⟨M.alpha x, (hK x).mpr hx⟩ = w
    have hwb : w.1 ≠ b := by
      intro h
      apply hxa
      have h2 := hw.trans ((Subtype.ext h : w = ⟨b, Kb⟩).trans hold.symm)
      exact M.alpha.injective (congrArg Subtype.val ((PredicateRestriction.sigma M K).injective h2))
    rw [rotationImage, renameDart]
    by_cases hwa : w.1 = a
    · simp only [if_pos hwa]
    · simp only [if_neg hwa, if_neg hwb]

theorem facePerm_pow_toNew (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b)
    (Kn : K' none) (Kp : K' (some none)) (hab : a ≠ b) (hb : M.facePerm a = b) (n : ℕ)
    (x : (PredicateRestriction.toCombMap M K hK).Dart) :
    ((PredicateRestriction.toCombMap (toCombMap M a b) K' hK').facePerm ^ n)
        (toNew M a b K K' hK hK' hι Kp x) =
      toNew M a b K K' hK hK' hι Kp (((PredicateRestriction.toCombMap M K hK).facePerm ^ n) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih,
        facePerm_toNew M a b K K' hK hK' hι Ka Kb Kn Kp hab hb]

/-- Away from `a` and its reverse, renaming commutes with edge reversal. -/
theorem alpha_toNew (hι : ∀ x, K' (embed M x) ↔ K x) (Kp : K' (some none))
    (x : (PredicateRestriction.toCombMap M K hK).Dart) (hx : x.1 ≠ a) (hax : x.1 ≠ M.alpha a) :
    (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').alpha
        (toNew M a b K K' hK hK' hι Kp x) =
      toNew M a b K K' hK hK' hι Kp ((PredicateRestriction.toCombMap M K hK).alpha x) := by
  apply Subtype.ext
  have h1 : renameDart M a b x.1 = embed M x.1 := by rw [renameDart, if_neg hx]
  have h2 : M.alpha x.1 ≠ a := fun h => hax (by rw [← h, M.alpha_involutive])
  change (toCombMap M a b).alpha (renameDart M a b x.1) = renameDart M a b (M.alpha x.1)
  rw [h1, renameDart, if_neg h2]
  rfl

variable (Q : (PredicateRestriction.toCombMap M K hK).Dart → Prop)
  (Q' : (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').Dart → Prop)
  (hQ : ∀ d, Q ((PredicateRestriction.toCombMap M K hK).dual.alpha d) ↔ Q d)
  (hQ' : ∀ d, Q' ((PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual.alpha d) ↔ Q' d)

/-- The renaming, on the second restriction of the duals. -/
noncomputable def toPhi (hι : ∀ x, K' (embed M x) ↔ K x) (Kp : K' (some none))
    (hτQ : ∀ x, Q' (toNew M a b K K' hK hK' hι Kp x) ↔ Q x)
    (y : (PredicateRestriction.toCombMap (PredicateRestriction.toCombMap M K hK).dual Q hQ).Dart) :
    (PredicateRestriction.toCombMap
      (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q' hQ').Dart :=
  ⟨toNew M a b K K' hK hK' hι Kp y.1, (hτQ y.1).mpr y.2⟩

theorem toPhi_injective (hι : ∀ x, K' (embed M x) ↔ K x) (Kp : K' (some none))
    (hτQ : ∀ x, Q' (toNew M a b K K' hK hK' hι Kp x) ↔ Q x) :
    Function.Injective (toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ) :=
  fun _ _ h => Subtype.ext (toNew_injective M a b K K' hK hK' hι Kp (congrArg Subtype.val h))

theorem toPhi_surjective (hι : ∀ x, K' (embed M x) ↔ K x) (Kp : K' (some none))
    (hτQ : ∀ x, Q' (toNew M a b K K' hK hK' hι Kp x) ↔ Q x)
    (hQrange : ∀ y, Q' y → ∃ x, toNew M a b K K' hK hK' hι Kp x = y) :
    Function.Surjective (toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ) := by
  intro z
  obtain ⟨x, hx⟩ := hQrange z.1 z.2
  exact ⟨⟨x, (hτQ x).mp (by rw [hx]; exact z.2)⟩, Subtype.ext hx⟩

/-- **The second rotation is transported.**  Retained darts of the new dual are renamed old
ones, so the new first return is the renamed old first return. -/
theorem sigma_toPhi (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b) (Kn : K' none)
    (Kp : K' (some none)) (hab : a ≠ b) (hb : M.facePerm a = b)
    (hτQ : ∀ x, Q' (toNew M a b K K' hK hK' hι Kp x) ↔ Q x)
    (hQrange : ∀ y, Q' y → ∃ x, toNew M a b K K' hK hK' hι Kp x = y)
    (y : (PredicateRestriction.toCombMap (PredicateRestriction.toCombMap M K hK).dual Q hQ).Dart) :
    PredicateRestriction.sigma (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q'
        (toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ y) =
      toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ
        (PredicateRestriction.sigma (PredicateRestriction.toCombMap M K hK).dual Q y) := by
  obtain ⟨m, hm, hreach, hskip⟩ :=
    PredicateRestriction.sigma_firstReturn (PredicateRestriction.toCombMap M K hK).dual Q y
  refine PermFirstReturn.apply_eq_of_isFirstReturn (PredicateRestriction.sigma_firstReturn
    (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q') hm ?_ ?_
  · change ((PredicateRestriction.toCombMap (toCombMap M a b) K' hK').facePerm ^ m)
        (toNew M a b K K' hK hK' hι Kp y.1) =
      toNew M a b K K' hK hK' hι Kp
        (PredicateRestriction.sigma (PredicateRestriction.toCombMap M K hK).dual Q y).1
    rw [facePerm_pow_toNew M a b K K' hK hK' hι Ka Kb Kn Kp hab hb]
    exact congrArg (toNew M a b K K' hK hK' hι Kp) hreach
  · rintro k hk hkm ⟨z, hz⟩
    obtain ⟨x, hx⟩ := hQrange z.1 z.2
    have hz' : z.1 = ((PredicateRestriction.toCombMap (toCombMap M a b) K' hK').facePerm ^ k)
        (toNew M a b K K' hK hK' hι Kp y.1) := hz
    rw [facePerm_pow_toNew M a b K K' hK hK' hι Ka Kb Kn Kp hab hb, ← hx] at hz'
    exact hskip k hk hkm ⟨⟨x, (hτQ x).mp (by rw [hx]; exact z.2)⟩,
      toNew_injective M a b K K' hK hK' hι Kp hz'⟩

theorem facePerm_toPhi (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b) (Kn : K' none)
    (Kp : K' (some none)) (hab : a ≠ b) (hb : M.facePerm a = b)
    (hτQ : ∀ x, Q' (toNew M a b K K' hK hK' hι Kp x) ↔ Q x)
    (hQrange : ∀ y, Q' y → ∃ x, toNew M a b K K' hK hK' hι Kp x = y)
    (hQa : ∀ x, Q x → x.1 ≠ a)
    (y : (PredicateRestriction.toCombMap (PredicateRestriction.toCombMap M K hK).dual Q hQ).Dart) :
    (PredicateRestriction.toCombMap
        (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q' hQ').facePerm
        (toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ y) =
      toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ
        ((PredicateRestriction.toCombMap
          (PredicateRestriction.toCombMap M K hK).dual Q hQ).facePerm y) := by
  have hy : y.1.1 ≠ a := hQa y.1 y.2
  have hQy : Q ((PredicateRestriction.toCombMap M K hK).alpha y.1) := (hQ y.1).mpr y.2
  have hy' : y.1.1 ≠ M.alpha a := fun h =>
    hQa _ hQy (show M.alpha y.1.1 = a by rw [h, M.alpha_involutive])
  apply Subtype.ext
  refine (restrict_facePerm_val (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q'
    hQ' (toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ y)
    (z := toNew M a b K K' hK hK' hι Kp ((PredicateRestriction.toCombMap M K hK).alpha y.1))
    (alpha_toNew M a b K K' hK hK' hι Kp y.1 hy hy') ((hτQ _).mpr hQy)).trans ?_
  exact congrArg Subtype.val (sigma_toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Ka Kb Kn Kp hab hb hτQ
    hQrange ⟨(PredicateRestriction.toCombMap M K hK).alpha y.1, hQy⟩)

theorem facePerm_pow_toPhi (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b)
    (Kn : K' none) (Kp : K' (some none)) (hab : a ≠ b) (hb : M.facePerm a = b)
    (hτQ : ∀ x, Q' (toNew M a b K K' hK hK' hι Kp x) ↔ Q x)
    (hQrange : ∀ y, Q' y → ∃ x, toNew M a b K K' hK hK' hι Kp x = y)
    (hQa : ∀ x, Q x → x.1 ≠ a) (n : ℕ)
    (y : (PredicateRestriction.toCombMap (PredicateRestriction.toCombMap M K hK).dual Q hQ).Dart) :
    ((PredicateRestriction.toCombMap
        (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q' hQ').facePerm ^ n)
        (toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ y) =
      toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ
        (((PredicateRestriction.toCombMap
          (PredicateRestriction.toCombMap M K hK).dual Q hQ).facePerm ^ n) y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih,
        facePerm_toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Ka Kb Kn Kp hab hb hτQ hQrange hQa]

/-- **Faces of the second restriction are transported.** -/
theorem faceOf_toPhi_eq_iff (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b)
    (Kn : K' none) (Kp : K' (some none)) (hab : a ≠ b) (hb : M.facePerm a = b)
    (hτQ : ∀ x, Q' (toNew M a b K K' hK hK' hι Kp x) ↔ Q x)
    (hQrange : ∀ y, Q' y → ∃ x, toNew M a b K K' hK hK' hι Kp x = y)
    (hQa : ∀ x, Q x → x.1 ≠ a)
    (y y' : (PredicateRestriction.toCombMap (PredicateRestriction.toCombMap M K hK).dual Q hQ).Dart) :
    (PredicateRestriction.toCombMap
        (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q' hQ').faceOf
        (toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ y) =
      (PredicateRestriction.toCombMap
        (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q' hQ').faceOf
        (toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ y') ↔
      (PredicateRestriction.toCombMap (PredicateRestriction.toCombMap M K hK).dual Q hQ).faceOf y =
        (PredicateRestriction.toCombMap
          (PredicateRestriction.toCombMap M K hK).dual Q hQ).faceOf y' := by
  rw [faceOf_eq_iff, faceOf_eq_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [facePerm_pow_toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Ka Kb Kn Kp hab hb hτQ hQrange hQa]
      at hn
    exact ⟨(n : ℤ), by
      simpa only [zpow_natCast] using toPhi_injective M a b K K' hK hK' Q Q' hQ hQ' hι Kp hτQ hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by
      rw [zpow_natCast, facePerm_pow_toPhi M a b K K' hK hK' Q Q' hQ hQ' hι Ka Kb Kn Kp hab hb hτQ
        hQrange hQa, hn]⟩

/-- New darts as old ones: the new edge collapses onto `b` and `a`. -/
def retractDart : Option (Option M.Dart) → M.Dart
  | none => b
  | some none => a
  | some (some d) => d

theorem retractDart_rotationImage (z : M.Dart) :
    retractDart M a b (rotationImage M a b z) = z := by
  rw [rotationImage]
  split_ifs with ha hb
  · exact ha.symm
  · exact hb.symm
  · rfl

theorem keep_retractDart (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b)
    (x : (toCombMap M a b).Dart) (hx : K' x) : K (retractDart M a b x) := by
  rcases x with _ | _ | d
  · exact Kb
  · exact Ka
  · exact (hι d).mp hx

/-- The retraction of the new restriction onto the old one. -/
def retract (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b)
    (x : (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').Dart) :
    (PredicateRestriction.toCombMap M K hK).Dart :=
  ⟨retractDart M a b x.1, keep_retractDart M a b K K' hι Ka Kb x.1 x.2⟩

/-- **A face-class step of the new dual retracts to a face-class chain of the old dual.** -/
theorem faceClassStep_retract (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b)
    (Kn : K' none) (Kp : K' (some none)) (hab : a ≠ b) (hb : M.facePerm a = b)
    (hQa : ∀ x, Q x → x.1 ≠ a) (hτQ : ∀ x, Q' (toNew M a b K K' hK hK' hι Kp x) ↔ Q x)
    {x y : (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').Dart}
    (h : FaceClassStep (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q' x y) :
    Relation.EqvGen (FaceClassStep (PredicateRestriction.toCombMap M K hK).dual Q)
      (retract M a b K K' hK hK' hι Ka Kb x) (retract M a b K K' hK hK' hι Ka Kb y) := by
  have Ka' : K (M.alpha a) := (hK a).mpr Ka
  have hstep : Relation.EqvGen (FaceClassStep (PredicateRestriction.toCombMap M K hK).dual Q)
      ⟨a, Ka⟩ ⟨b, Kb⟩ :=
    Relation.EqvGen.trans _ ⟨M.alpha a, Ka'⟩ _
      (Relation.EqvGen.rel _ _ (Or.inr ⟨fun hq => hQa _ hq rfl, rfl⟩))
      (Relation.EqvGen.rel _ _ (Or.inl (by
        rw [dual_facePerm]
        exact (restrict_sigma_alpha M a b K hb Ka' Kb).symm)))
  obtain ⟨x, hx⟩ := x
  rcases h with h | ⟨hq, h⟩
  · rw [dual_facePerm] at h
    rcases x with _ | _ | d
    · have h2 : y = ⟨embed M b, (hι b).mpr Kb⟩ :=
        h.trans (restrict_sigma_negative M a b K' hx ((hι b).mpr Kb))
      subst h2
      exact Relation.EqvGen.refl _
    · have h2 : y = ⟨embed M a, (hι a).mpr Ka⟩ :=
        h.trans (restrict_sigma_positive M a b K' hab hx ((hι a).mpr Ka))
      subst h2
      exact Relation.EqvGen.refl _
    · have hd : K d := (hι d).mp hx
      have h2 := h.trans (restrict_sigma_embed M a b K K' hι Ka Kb ⟨d, hd⟩ hx
        (keep_rotationImage M a b K K' hι Kn Kp (PredicateRestriction.sigma M K ⟨d, hd⟩).2))
      subst h2
      refine Relation.EqvGen.rel _ _ (Or.inl ?_)
      rw [dual_facePerm]
      apply Subtype.ext
      show retractDart M a b (rotationImage M a b (PredicateRestriction.sigma M K ⟨d, hd⟩).1) =
        (PredicateRestriction.sigma M K ⟨d, hd⟩).1
      exact retractDart_rotationImage M a b _
  · subst h
    rcases x with _ | _ | d
    · exact Relation.EqvGen.symm _ _ hstep
    · exact hstep
    · have hd : K d := (hι d).mp hx
      have hnq : ¬Q ⟨d, hd⟩ := by
        by_cases hda : d = a
        · exact fun hq' => hQa _ hq' hda
        · intro hq'
          apply hq
          have ht : toNew M a b K K' hK hK' hι Kp ⟨d, hd⟩ = ⟨some (some d), hx⟩ := by
            apply Subtype.ext
            show renameDart M a b d = embed M d
            rw [renameDart, if_neg hda]
          rw [← ht]
          exact (hτQ _).mpr hq'
      exact Relation.EqvGen.rel _ _ (Or.inr ⟨hnq, rfl⟩)

theorem eqvGen_retract (hι : ∀ x, K' (embed M x) ↔ K x) (Ka : K a) (Kb : K b)
    (Kn : K' none) (Kp : K' (some none)) (hab : a ≠ b) (hb : M.facePerm a = b)
    (hQa : ∀ x, Q x → x.1 ≠ a) (hτQ : ∀ x, Q' (toNew M a b K K' hK hK' hι Kp x) ↔ Q x)
    {x y : (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').Dart}
    (h : Relation.EqvGen
      (FaceClassStep (PredicateRestriction.toCombMap (toCombMap M a b) K' hK').dual Q') x y) :
    Relation.EqvGen (FaceClassStep (PredicateRestriction.toCombMap M K hK).dual Q)
      (retract M a b K K' hK hK' hι Ka Kb x) (retract M a b K K' hK hK' hι Ka Kb y) := by
  induction h with
  | rel _ _ h => exact faceClassStep_retract M a b K K' hK hK' Q Q' hι Ka Kb Kn Kp hab hb hQa hτQ h
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

end GroupApproximation.GGT.VanKampen.EdgeInsertion.InsertionRestriction

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.InsertionRestriction.restrict_sigma_embed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.InsertionRestriction.facePerm_toNew
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.InsertionRestriction.facePerm_pow_toNew
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.InsertionRestriction.sigma_toPhi
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.InsertionRestriction.facePerm_toPhi
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.InsertionRestriction.faceOf_toPhi_eq_iff
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.InsertionRestriction.eqvGen_retract
