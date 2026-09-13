import GroupApproximation.GGT.VanKampen.PinchLemma
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the gap at a same-cell junction

Two consecutive sides of a polygon face `f` can be arcs of one relator cell.  At the corner the
walk of `f` arrives along `α b` and leaves along `α a`, so `σ b = α a`.  Along the cell `b`
comes `m + 1` face steps after `a`, and the darts `facePerm^1 a, …, facePerm^m a` are the gap.
Reversed, the gap is a closed walk at the corner vertex.

Joining the vertex darts `α (facePerm^m a)` and `α a` cuts the cell face into the gap face and
the rest.  The corner is a pinch, so `PinchLemma.split_euler` gives Euler characteristic four,
and the darts of the joined map fall into two classes: the face side, reached from `b`, and the
gap side, reached from `facePerm a`.

* `JunctionPocket.reach_or_reach`: after any join, every dart is reached from one of the two
  new face successors.
* `JunctionPocket.junction_not_reach`: the two sides of a junction are apart.
* `JunctionPocket.gap_alpha_faceOf_ne`: the reversed gap avoids the walk of `f`.
* `JunctionPocket.reach_face_or_reach_face`: of two junctions of `f` with different `b`, every
  dart is on the face side of one.  So the exterior is on the gap side of at most one junction.
-/

namespace GroupApproximation.GGT.VanKampen

universe v

open Equiv

namespace JunctionPocket

section Map

variable {M : CombMap.{v}}

/-- Face rotation preserves the face of a dart. -/
theorem faceOf_pow_apply (x : M.Dart) (n : ℕ) : M.faceOf ((M.facePerm ^ n) x) = M.faceOf x := by
  induction n with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ n ih => rw [pow_succ', Perm.mul_apply, M.faceOf_facePerm, ih]

/-- An elementary move keeps the class of a dart. -/
theorem eqvGen_iff_of_adjacent {N : CombMap.{v}} {c u w : N.Dart} (h : N.Adjacent u w) :
    Relation.EqvGen N.Adjacent c u ↔ Relation.EqvGen N.Adjacent c w :=
  ⟨fun hc => Relation.EqvGen.trans _ _ _ hc (Relation.EqvGen.rel _ _ h),
    fun hc => Relation.EqvGen.trans _ _ _ hc (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h))⟩

variable {a b : M.Dart} {m : ℕ}

/-- The last gap dart turns into `b`. -/
theorem facePerm_last (hab : (M.facePerm ^ (m + 1)) a = b) :
    M.facePerm ((M.facePerm ^ m) a) = b := by
  rw [← hab, pow_succ', Perm.mul_apply]

/-- The walk of `f` turns from `α b` into `α a`. -/
theorem facePerm_alpha_b (hb : M.sigma b = M.alpha a) : M.facePerm (M.alpha b) = M.alpha a := by
  rw [← hb]
  show M.sigma (M.alpha (M.alpha b)) = M.sigma b
  rw [M.alpha_involutive b]

theorem faceOf_alpha_a (hb : M.sigma b = M.alpha a) :
    M.faceOf (M.alpha a) = M.faceOf (M.alpha b) := by
  rw [← facePerm_alpha_b hb, M.faceOf_facePerm]

/-- A gap dart is not `a`. -/
theorem gap_ne_start (hab : (M.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b) {t : ℕ} (ht : t < m) :
    (M.facePerm ^ (t + 1)) a ≠ a := by
  intro h
  apply hleast (m - t - 1) (by omega)
  have hsplit : m + 1 = (m - t - 1 + 1) + (t + 1) := by omega
  rw [← hab, hsplit, pow_add M.facePerm (m - t - 1 + 1) (t + 1), Perm.mul_apply, h]

/-- A gap dart before the last one is not the last one. -/
theorem gap_ne_last (hab : (M.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b) {t : ℕ} (ht : t + 1 < m) :
    (M.facePerm ^ (t + 1)) a ≠ (M.facePerm ^ m) a := by
  intro h
  apply hleast (t + 1) ht
  rw [pow_succ' M.facePerm (t + 1), Perm.mul_apply, h, facePerm_last hab]

theorem last_ne_start (hm : m ≠ 0) (hab : (M.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b) : (M.facePerm ^ m) a ≠ a := by
  have h := gap_ne_start hab hleast (t := m - 1) (by omega)
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h

/-- **The corner is a pinch.** -/
theorem pinch_sameCycle (hb : M.sigma b = M.alpha a) (hab : (M.facePerm ^ (m + 1)) a = b) :
    M.sigma.SameCycle (M.alpha ((M.facePerm ^ m) a)) (M.alpha a) := by
  have h1 : M.sigma (M.alpha ((M.facePerm ^ m) a)) = b := facePerm_last hab
  rw [← hb, ← h1]
  exact Perm.SameCycle.rfl.apply_right.apply_right

variable [DecidableEq M.Dart]

/-- The joined map moves a dart off the pair like `M`. -/
theorem joined_sigma_apply_of_ne {p e u : M.Dart} (hp : u ≠ M.alpha p) (he : u ≠ M.alpha e) :
    (FoldMap.joined M p e).sigma u = M.sigma u := by
  show M.sigma (Equiv.swap (M.alpha p) (M.alpha e) u) = M.sigma u
  rw [Equiv.swap_apply_of_ne_of_ne hp he]

theorem joined_sigma_alpha_left (p e : M.Dart) :
    (FoldMap.joined M p e).sigma (M.alpha p) = M.facePerm e := by
  show M.sigma (Equiv.swap (M.alpha p) (M.alpha e) (M.alpha p)) = M.sigma (M.alpha e)
  rw [Equiv.swap_apply_left]

theorem joined_sigma_alpha_right (p e : M.Dart) :
    (FoldMap.joined M p e).sigma (M.alpha e) = M.facePerm p := by
  show M.sigma (Equiv.swap (M.alpha p) (M.alpha e) (M.alpha e)) = M.sigma (M.alpha p)
  rw [Equiv.swap_apply_right]

/-- A dart off the pair reaches its face successor in the joined map. -/
theorem joined_reach_facePerm {p e x : M.Dart} (hp : x ≠ p) (he : x ≠ e) :
    Relation.EqvGen (FoldMap.joined M p e).Adjacent x (M.facePerm x) := by
  have h := PinchLemma.eqvGen_facePerm (M := FoldMap.joined M p e) x
  rwa [FoldMap.joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne hp he] at h

/-- The darts of a face off the pair stay together in the joined map. -/
theorem joined_reach_of_faceOf_eq {p e x z : M.Dart} (hp : M.faceOf x ≠ M.faceOf p)
    (he : M.faceOf x ≠ M.faceOf e) (hxz : M.faceOf x = M.faceOf z) :
    Relation.EqvGen (FoldMap.joined M p e).Adjacent x z := by
  have hpow : ∀ n : ℕ,
      Relation.EqvGen (FoldMap.joined M p e).Adjacent x ((M.facePerm ^ n) x) := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, Perm.one_apply]
        exact Relation.EqvGen.refl _
    | succ n ih =>
        have hn := faceOf_pow_apply x n
        refine Relation.EqvGen.trans _ _ _ ih ?_
        rw [pow_succ', Perm.mul_apply]
        refine joined_reach_facePerm ?_ ?_
        · intro h
          exact hp (by rw [← hn, h])
        · intro h
          exact he (by rw [← hn, h])
  obtain ⟨n, hn⟩ := ((M.faceOf_eq_iff x z).mp hxz).exists_nat_pow_eq
  rw [← hn]
  exact hpow n

/-- **Every dart reaches one of the two new face successors.**  After joining the vertices after
`α p` and `α e`, every dart of a connected map is reached from `facePerm p` or `facePerm e`. -/
theorem reach_or_reach (hM : M.IsConnected) (p e x : M.Dart) :
    Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.facePerm p) x ∨
      Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.facePerm e) x := by
  let P : M.Dart → Prop := fun y =>
    Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.facePerm p) y ∨
      Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.facePerm e) y
  have hsame : ∀ y z, (FoldMap.joined M p e).Adjacent y z → (P y ↔ P z) := fun _ _ h =>
    or_congr (eqvGen_iff_of_adjacent h) (eqvGen_iff_of_adjacent h)
  have hstep : ∀ y z, M.Adjacent y z → (P y ↔ P z) := by
    intro y z hyz
    rcases hyz with h | h
    · exact hsame y z (Or.inl h)
    · by_cases hy1 : y = M.alpha p
      · subst hy1
        subst h
        have hPy : P (M.alpha p) := Or.inr (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ (Or.inr (joined_sigma_alpha_left p e))))
        exact ⟨fun _ => Or.inl (Relation.EqvGen.refl _), fun _ => hPy⟩
      · by_cases hy2 : y = M.alpha e
        · subst hy2
          subst h
          have hPy : P (M.alpha e) := Or.inl (Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ (Or.inr (joined_sigma_alpha_right p e))))
          exact ⟨fun _ => Or.inr (Relation.EqvGen.refl _), fun _ => hPy⟩
        · exact hsame y z (Or.inr ((joined_sigma_apply_of_ne hy1 hy2).trans h))
  have hgen : ∀ y z, Relation.EqvGen M.Adjacent y z → (P y ↔ P z) := by
    intro y z hyz
    induction hyz with
    | rel y z h => exact hstep y z h
    | refl y => exact Iff.rfl
    | symm y z _ ih => exact ih.symm
    | trans y z w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hgen (M.facePerm p) x (hM _ x)).mp (Or.inl (Relation.EqvGen.refl _))

/-- **The two sides of a pinch are apart.** -/
theorem not_reach (hM : M.IsPlanar) {p e : M.Dart} (hpe : p ≠ e)
    (hface : M.faceOf p = M.faceOf e) (hpinch : M.sigma.SameCycle (M.alpha p) (M.alpha e)) :
    ¬ Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.facePerm p) (M.facePerm e) := by
  intro hpe'
  have hall : ∀ x, Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.facePerm p) x := fun x =>
    (reach_or_reach hM.1 p e x).elim id (fun h => Relation.EqvGen.trans _ _ _ hpe' h)
  have hconn : (FoldMap.joined M p e).IsConnected := fun x y =>
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall x)) (hall y)
  have hle := (FoldMap.joined M p e).eulerCharacteristic_le_two hconn
  rw [PinchLemma.split_euler hM hpe hface hpinch] at hle
  norm_num at hle

/-- **The two sides of a junction are apart**: once the corner is split, `b` does not reach
`facePerm a`. -/
theorem junction_not_reach (hM : M.IsPlanar) (hm : m ≠ 0) (hb : M.sigma b = M.alpha a)
    (hab : (M.facePerm ^ (m + 1)) a = b) (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b) :
    ¬ Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m) a) a).Adjacent b (M.facePerm a) := by
  have h := not_reach hM (last_ne_start hm hab hleast) (faceOf_pow_apply a m)
    (pinch_sameCycle hb hab)
  rwa [facePerm_last hab] at h

/-- The gap is on the gap side. -/
theorem reach_gap (hab : (M.facePerm ^ (m + 1)) a = b)
    (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b) {t : ℕ} (ht : t < m) :
    Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m) a) a).Adjacent (M.facePerm a)
      ((M.facePerm ^ (t + 1)) a) := by
  induction t with
  | zero =>
      rw [Nat.zero_add, pow_one]
      exact Relation.EqvGen.refl _
  | succ t ih =>
      refine Relation.EqvGen.trans _ _ _ (ih (by omega)) ?_
      rw [pow_succ' M.facePerm (t + 1), Perm.mul_apply]
      exact joined_reach_facePerm (gap_ne_last hab hleast ht) (gap_ne_start hab hleast (by omega))

/-- The face across the corner is on the face side. -/
theorem reach_face (hface : M.faceOf (M.alpha b) ≠ M.faceOf a) {x : M.Dart}
    (hx : M.faceOf x = M.faceOf (M.alpha b)) :
    Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m) a) a).Adjacent b x := by
  refine Relation.EqvGen.trans _ (M.alpha b) _ (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_
  refine joined_reach_of_faceOf_eq ?_ hface hx.symm
  rw [faceOf_pow_apply]
  exact hface

/-- **(B) The reversed gap avoids the walk of `f`.** -/
theorem gap_alpha_faceOf_ne (hM : M.IsPlanar) (hm : m ≠ 0) (hb : M.sigma b = M.alpha a)
    (hab : (M.facePerm ^ (m + 1)) a = b) (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b)
    (hface : M.faceOf (M.alpha b) ≠ M.faceOf a) {t : ℕ} (ht : t < m) :
    M.faceOf (M.alpha ((M.facePerm ^ (t + 1)) a)) ≠ M.faceOf (M.alpha b) := by
  intro h
  apply junction_not_reach hM hm hb hab hleast
  refine Relation.EqvGen.trans _ _ _ (reach_face (m := m) hface h) ?_
  refine Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive ((M.facePerm ^ (t + 1)) a)))) ?_
  exact Relation.EqvGen.symm _ _ (reach_gap hab hleast ht)

theorem gap_last_alpha_faceOf_ne (hM : M.IsPlanar) (hm : m ≠ 0) (hb : M.sigma b = M.alpha a)
    (hab : (M.facePerm ^ (m + 1)) a = b) (hleast : ∀ t < m, (M.facePerm ^ (t + 1)) a ≠ b)
    (hface : M.faceOf (M.alpha b) ≠ M.faceOf a) :
    M.faceOf (M.alpha ((M.facePerm ^ m) a)) ≠ M.faceOf (M.alpha b) := by
  have h := gap_alpha_faceOf_ne hM hm hb hab hleast hface (t := m - 1) (by omega)
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h

/-- The last gap dart of a second junction on `f` is on the face side of the first. -/
theorem reach_face_other_last {a₁ b₁ a₂ b₂ : M.Dart} {m₁ m₂ : ℕ}
    (hb₁ : M.sigma b₁ = M.alpha a₁) (hab₁ : (M.facePerm ^ (m₁ + 1)) a₁ = b₁)
    (hab₂ : (M.facePerm ^ (m₂ + 1)) a₂ = b₂) (hface₁ : M.faceOf (M.alpha b₁) ≠ M.faceOf a₁)
    (hsame : M.faceOf (M.alpha b₂) = M.faceOf (M.alpha b₁)) (hne : b₁ ≠ b₂)
    (hgap₂ : M.faceOf (M.alpha ((M.facePerm ^ m₂) a₂)) ≠ M.faceOf (M.alpha b₂)) :
    Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₁) a₁) a₁).Adjacent b₁
      (M.alpha ((M.facePerm ^ m₂) a₂)) := by
  have hb₂ : Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₁) a₁) a₁).Adjacent b₁ b₂ :=
    Relation.EqvGen.trans _ _ _ (reach_face (m := m₁) hface₁ hsame)
      (Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive b₂)))
  refine Relation.EqvGen.trans _ _ _ hb₂
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr ?_)))
  rw [joined_sigma_apply_of_ne]
  · exact facePerm_last hab₂
  · intro h
    apply hne
    rw [← facePerm_last hab₁, ← facePerm_last hab₂, M.alpha.injective h]
  · intro h
    apply hgap₂
    rw [h, faceOf_alpha_a hb₁, hsame]

/-- **(C1) Two junctions of one face.**  If two junctions of the walk of `f` have different `b`,
every dart is on the face side of one of them.  So no dart is on the gap side of both. -/
theorem reach_face_or_reach_face (hM : M.IsPlanar) {a₁ b₁ a₂ b₂ : M.Dart} {m₁ m₂ : ℕ}
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hb₁ : M.sigma b₁ = M.alpha a₁)
    (hb₂ : M.sigma b₂ = M.alpha a₂) (hab₁ : (M.facePerm ^ (m₁ + 1)) a₁ = b₁)
    (hab₂ : (M.facePerm ^ (m₂ + 1)) a₂ = b₂)
    (hleast₁ : ∀ t < m₁, (M.facePerm ^ (t + 1)) a₁ ≠ b₁)
    (hleast₂ : ∀ t < m₂, (M.facePerm ^ (t + 1)) a₂ ≠ b₂)
    (hface₁ : M.faceOf (M.alpha b₁) ≠ M.faceOf a₁)
    (hface₂ : M.faceOf (M.alpha b₂) ≠ M.faceOf a₂)
    (hsame : M.faceOf (M.alpha b₁) = M.faceOf (M.alpha b₂)) (hne : b₁ ≠ b₂) (o : M.Dart) :
    Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₁) a₁) a₁).Adjacent b₁ o ∨
      Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₂) a₂) a₂).Adjacent b₂ o := by
  rcases reach_or_reach hM.1 ((M.facePerm ^ m₂) a₂) a₂ o with h | h
  · right
    rwa [facePerm_last hab₂] at h
  left
  have hgap₁ := gap_last_alpha_faceOf_ne hM hm₁ hb₁ hab₁ hleast₁ hface₁
  have hgap₂ := gap_last_alpha_faceOf_ne hM hm₂ hb₂ hab₂ hleast₂ hface₂
  have hn₂ := junction_not_reach hM hm₂ hb₂ hab₂ hleast₂
  have hQa₂ : Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₁) a₁) a₁).Adjacent b₁
      (M.alpha a₂) :=
    reach_face (m := m₁) hface₁ ((faceOf_alpha_a hb₂).trans hsame.symm)
  have hQb₂ : Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₁) a₁) a₁).Adjacent b₁ b₂ :=
    Relation.EqvGen.trans _ _ _ (reach_face (m := m₁) hface₁ hsame.symm)
      (Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive b₂)))
  have hQg₂ : Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₁) a₁) a₁).Adjacent b₁
      (M.facePerm a₂) := by
    refine Relation.EqvGen.trans _ _ _ hQa₂ (Relation.EqvGen.rel _ _ (Or.inr ?_))
    refine joined_sigma_apply_of_ne ?_ ?_
    · intro h'
      exact hgap₁ (by rw [← h', faceOf_alpha_a hb₂, hsame])
    · intro h'
      apply hne
      apply M.sigma.injective
      rw [hb₁, hb₂, h']
  have hUy₂ := reach_face_other_last hb₁ hab₁ hab₂ hface₁ hsame.symm hne hgap₂
  have hUy₁ := reach_face_other_last hb₂ hab₂ hab₁ hface₂ hsame hne.symm hgap₁
  have hUa₁ : Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₂) a₂) a₂).Adjacent b₂
      (M.alpha a₁) :=
    reach_face (m := m₂) hface₂ ((faceOf_alpha_a hb₁).trans hsame)
  have hP : ∀ u, Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₂) a₂) a₂).Adjacent
      (M.facePerm a₂) u → u ≠ M.alpha ((M.facePerm ^ m₁) a₁) ∧ u ≠ M.alpha a₁ := by
    intro u hu
    constructor
    · rintro rfl
      exact hn₂ (Relation.EqvGen.trans _ _ _ hUy₁ (Relation.EqvGen.symm _ _ hu))
    · rintro rfl
      exact hn₂ (Relation.EqvGen.trans _ _ _ hUa₁ (Relation.EqvGen.symm _ _ hu))
  have hinv : ∀ u w,
      Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₂) a₂) a₂).Adjacent u w →
      Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₂) a₂) a₂).Adjacent (M.facePerm a₂) u →
      (Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₁) a₁) a₁).Adjacent b₁ u ↔
        Relation.EqvGen (FoldMap.joined M ((M.facePerm ^ m₁) a₁) a₁).Adjacent b₁ w) := by
    intro u w huw
    induction huw with
    | rel u w h =>
        intro hu
        rcases h with h | h
        · exact eqvGen_iff_of_adjacent (Or.inl h)
        · by_cases hu₁ : u = M.alpha ((M.facePerm ^ m₂) a₂)
          · subst hu₁
            rw [joined_sigma_alpha_left] at h
            subst h
            exact ⟨fun _ => hQg₂, fun _ => hUy₂⟩
          · by_cases hu₂ : u = M.alpha a₂
            · subst hu₂
              rw [joined_sigma_alpha_right, facePerm_last hab₂] at h
              subst h
              exact ⟨fun _ => hQb₂, fun _ => hQa₂⟩
            · have hJ : (FoldMap.joined M ((M.facePerm ^ m₁) a₁) a₁).sigma u = w :=
                (joined_sigma_apply_of_ne (M := M) (hP u hu).1 (hP u hu).2).trans
                  ((joined_sigma_apply_of_ne (M := M) hu₁ hu₂).symm.trans h)
              exact eqvGen_iff_of_adjacent (Or.inr hJ)
    | refl u => exact fun _ => Iff.rfl
    | symm u w huw ih =>
        intro hw
        exact (ih (Relation.EqvGen.trans _ _ _ hw (Relation.EqvGen.symm _ _ huw))).symm
    | trans u w z huw _ ih₁ ih₂ =>
        intro hu
        exact (ih₁ hu).trans (ih₂ (Relation.EqvGen.trans _ _ _ hu huw))
  exact (hinv _ _ h (Relation.EqvGen.refl _)).mp hQg₂

end Map

end JunctionPocket

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.faceOf_pow_apply
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.eqvGen_iff_of_adjacent
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.facePerm_last
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.facePerm_alpha_b
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.faceOf_alpha_a
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.gap_ne_start
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.gap_ne_last
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.last_ne_start
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.pinch_sameCycle
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.joined_sigma_apply_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.joined_sigma_alpha_left
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.joined_sigma_alpha_right
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.joined_reach_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.joined_reach_of_faceOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.reach_or_reach
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.not_reach
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.junction_not_reach
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.reach_gap
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.reach_face
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.gap_alpha_faceOf_ne
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.gap_last_alpha_faceOf_ne
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.reach_face_other_last
#audit_axioms GroupApproximation.GGT.VanKampen.JunctionPocket.reach_face_or_reach_face
