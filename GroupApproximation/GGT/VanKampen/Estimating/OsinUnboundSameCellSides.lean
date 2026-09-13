import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Same-cell unbound darts: the two sides of a same-face edge

Let `d` be a dart of a planar map whose reverse lies on the same face.  That edge is a bridge, so
moves that avoid the edge split the darts into the side of `d` and the side of `α d`.  This module
records the facts that the same-cell count uses.
* Every dart lies on the side of `d` or on the side of `α d`.
* A dart is *oriented* toward a face when its side reaches that face.  One of `d` and `α d` is
  oriented toward any face that has a dart.  If `d` is not on that face, only one is.
* Two same-face edges on one face cycle do not cross.
* Let a face cycle start at an oriented dart with the longest pocket.  Then the reverse of every
  oriented dart of the cycle comes after it.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

/-- Face steps compose. -/
theorem facePerm_pow_apply_pow (M : CombMap.{u}) (a b : ℕ) (x : M.Dart) :
    (M.facePerm ^ a) ((M.facePerm ^ b) x) = (M.facePerm ^ (a + b)) x := by
  rw [pow_add, Equiv.Perm.mul_apply]

/-- Face steps keep the face. -/
theorem faceOf_facePerm_pow (M : CombMap.{u}) (x : M.Dart) (j : ℕ) :
    M.faceOf ((M.facePerm ^ j) x) = M.faceOf x := by
  induction j with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ j ih => rw [pow_succ', Equiv.Perm.mul_apply, M.faceOf_facePerm, ih]

namespace AvoidEdgeStep

variable {M : CombMap.{u}}

/-- A dart is oriented toward a face when moves that avoid its edge reach a dart of that face. -/
def Oriented (M : CombMap.{u}) (outer : M.Face) (d : M.Dart) : Prop :=
  ∃ o, M.faceOf o = outer ∧ Relation.EqvGen (AvoidEdgeStep M d) d o

/-- **The reverse dart has the same moves.** -/
theorem alpha_eq (M : CombMap.{u}) (d : M.Dart) :
    AvoidEdgeStep M (M.alpha d) = AvoidEdgeStep M d := by
  funext x y
  apply propext
  unfold AvoidEdgeStep
  rw [M.alpha_involutive d]
  constructor
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h2, h1, h3⟩
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h2, h1, h3⟩

/-- **One face step avoids the edge.** -/
theorem eqvGen_facePerm {d x : M.Dart} (hxd : x ≠ d) (hxa : x ≠ M.alpha d) :
    Relation.EqvGen (AvoidEdgeStep M d) x (M.facePerm x) := by
  have h1 : AvoidEdgeStep M d x (M.alpha x) := Or.inr ⟨hxd, hxa, rfl⟩
  have h2 : AvoidEdgeStep M d (M.alpha x) (M.facePerm x) := Or.inl rfl
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ h1) (Relation.EqvGen.rel _ _ h2)

/-- **A run of face steps that avoids the edge.** -/
theorem eqvGen_facePerm_pow_add {d : M.Dart} (x : M.Dart) (j m : ℕ)
    (havoid : ∀ t < m, (M.facePerm ^ (j + t)) x ≠ d ∧ (M.facePerm ^ (j + t)) x ≠ M.alpha d) :
    Relation.EqvGen (AvoidEdgeStep M d) ((M.facePerm ^ j) x) ((M.facePerm ^ (j + m)) x) := by
  induction m with
  | zero => exact Relation.EqvGen.refl _
  | succ m ih =>
      have h := havoid m (Nat.lt_succ_self m)
      refine Relation.EqvGen.trans _ _ _ (ih fun t ht => havoid t (Nat.lt_succ_of_lt ht)) ?_
      rw [← Nat.add_assoc, pow_succ', Equiv.Perm.mul_apply]
      exact eqvGen_facePerm h.1 h.2

/-- **A run of face steps between two positions.** -/
theorem eqvGen_facePerm_pow_of_le {d : M.Dart} (x : M.Dart) {j k : ℕ} (hjk : j ≤ k)
    (havoid : ∀ t, j ≤ t → t < k → (M.facePerm ^ t) x ≠ d ∧ (M.facePerm ^ t) x ≠ M.alpha d) :
    Relation.EqvGen (AvoidEdgeStep M d) ((M.facePerm ^ j) x) ((M.facePerm ^ k) x) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact eqvGen_facePerm_pow_add x j m fun t ht => havoid (j + t) (Nat.le_add_right j t) (by omega)

/-- **Darts of one face away from the edge are joined.**  If neither dart of the edge of `d` lies
on the face of `o`, face steps from `o` avoid the edge. -/
theorem eqvGen_of_faceOf_eq {d o o' : M.Dart} (hface : M.faceOf o = M.faceOf o')
    (hd : M.faceOf d ≠ M.faceOf o) (ha : M.faceOf (M.alpha d) ≠ M.faceOf o) :
    Relation.EqvGen (AvoidEdgeStep M d) o o' := by
  obtain ⟨j, hj⟩ := ((M.faceOf_eq_iff o o').mp hface).exists_nat_pow_eq
  have h := eqvGen_facePerm_pow_add (d := d) o 0 j fun t _ => by
    refine ⟨fun h => hd ?_, fun h => ha ?_⟩
    · rw [← h, faceOf_facePerm_pow]
    · rw [← h, faceOf_facePerm_pow]
  rw [pow_zero, Equiv.Perm.one_apply, Nat.zero_add, hj] at h
  exact h

/-- **Every dart is on one side.** -/
theorem eqvGen_or (hM : M.IsConnected) (d x : M.Dart) :
    Relation.EqvGen (AvoidEdgeStep M d) x d ∨ Relation.EqvGen (AvoidEdgeStep M d) x (M.alpha d) := by
  have key : ∀ y z, Relation.EqvGen M.Adjacent y z →
      ((Relation.EqvGen (AvoidEdgeStep M d) y d ∨
          Relation.EqvGen (AvoidEdgeStep M d) y (M.alpha d)) ↔
        (Relation.EqvGen (AvoidEdgeStep M d) z d ∨
          Relation.EqvGen (AvoidEdgeStep M d) z (M.alpha d))) := by
    intro y z h
    induction h with
    | rel y z h =>
        by_cases hstep : AvoidEdgeStep M d y z
        · have hyz := Relation.EqvGen.rel y z hstep
          have hzy := Relation.EqvGen.symm _ _ hyz
          constructor
          · rintro (h' | h')
            · exact Or.inl (Relation.EqvGen.trans _ _ _ hzy h')
            · exact Or.inr (Relation.EqvGen.trans _ _ _ hzy h')
          · rintro (h' | h')
            · exact Or.inl (Relation.EqvGen.trans _ _ _ hyz h')
            · exact Or.inr (Relation.EqvGen.trans _ _ _ hyz h')
        · have hz : (y = d ∧ z = M.alpha d) ∨ (y = M.alpha d ∧ z = d) := by
            rcases h with h | h
            · by_cases hyd : y = d
              · exact Or.inl ⟨hyd, by rw [← h, hyd]⟩
              · by_cases hya : y = M.alpha d
                · exact Or.inr ⟨hya, by rw [← h, hya, M.alpha_involutive d]⟩
                · exact (hstep (Or.inr ⟨hyd, hya, h⟩)).elim
            · exact (hstep (Or.inl h)).elim
          rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact iff_of_true (Or.inl (Relation.EqvGen.refl _)) (Or.inr (Relation.EqvGen.refl _))
          · exact iff_of_true (Or.inr (Relation.EqvGen.refl _)) (Or.inl (Relation.EqvGen.refl _))
    | refl y => exact Iff.rfl
    | symm y z _ ih => exact ih.symm
    | trans y z u _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (key d x (hM d x)).mp (Or.inl (Relation.EqvGen.refl d))

/-- **One dart of an edge is oriented.** -/
theorem oriented_or (hM : M.IsConnected) {outer : M.Face} (ho : ∃ o, M.faceOf o = outer)
    (d : M.Dart) : Oriented M outer d ∨ Oriented M outer (M.alpha d) := by
  obtain ⟨o, ho⟩ := ho
  rcases eqvGen_or hM d o with h | h
  · exact Or.inl ⟨o, ho, Relation.EqvGen.symm _ _ h⟩
  · refine Or.inr ⟨o, ho, ?_⟩
    rw [alpha_eq]
    exact Relation.EqvGen.symm _ _ h

/-- **Only one dart of a same-face edge is oriented.** -/
theorem not_oriented_both (hM : M.IsPlanar) {outer : M.Face} {d : M.Dart}
    (hface : M.faceOf d = M.faceOf (M.alpha d)) (hout : M.faceOf d ≠ outer)
    (hd : Oriented M outer d) (ha : Oriented M outer (M.alpha d)) : False := by
  obtain ⟨o, ho, hdo⟩ := hd
  obtain ⟨o', ho', hao⟩ := ha
  rw [alpha_eq] at hao
  have hoo : Relation.EqvGen (AvoidEdgeStep M d) o o' :=
    eqvGen_of_faceOf_eq (ho.trans ho'.symm) (fun h => hout (h.trans ho))
      (fun h => hout (hface.trans (h.trans ho)))
  exact not_eqvGen_alpha_of_sameFace M hM d hface
    (Relation.EqvGen.trans _ _ _ hdo
      (Relation.EqvGen.trans _ _ _ hoo (Relation.EqvGen.symm _ _ hao)))

/-- **Moves from the side of `d` avoid another edge.**  If neither dart of the edge of `e` is on
the side of `d`, every move from the side of `d` avoids the edge of `e`. -/
theorem eqvGen_transfer {d e : M.Dart} (he : ¬ Relation.EqvGen (AvoidEdgeStep M d) e d)
    (hae : ¬ Relation.EqvGen (AvoidEdgeStep M d) (M.alpha e) d) {x y : M.Dart}
    (hxy : Relation.EqvGen (AvoidEdgeStep M d) x y)
    (hx : Relation.EqvGen (AvoidEdgeStep M d) x d) :
    Relation.EqvGen (AvoidEdgeStep M e) x y := by
  induction hxy with
  | rel x y h =>
      rcases h with h | ⟨-, -, h⟩
      · exact Relation.EqvGen.rel x y (Or.inl h)
      · refine Relation.EqvGen.rel x y (Or.inr ⟨fun hxe => he ?_, fun hxe => hae ?_, h⟩)
        · rw [← hxe]
          exact hx
        · rw [← hxe]
          exact hx
  | refl x => exact Relation.EqvGen.refl x
  | symm x y hxy ih =>
      exact Relation.EqvGen.symm _ _ (ih (Relation.EqvGen.trans _ _ _ hxy hx))
  | trans x y z hxy _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ (ih₁ hx)
        (ih₂ (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hxy) hx))

/-- **A neighbouring oriented dart.**  Let `d` and `e` be oriented darts, neither on the outer
face, with the reverse of `d` on the face of `d` and the reverse of `e` off the outer face.  If
`e` is on the side of `α d` and is not a dart of the edge of `d`, then moves that avoid the edge
of `e` join `d` and `e`. -/
theorem eqvGen_of_oriented_side (hM : M.IsPlanar) {outer : M.Face} {d e : M.Dart}
    (hface : M.faceOf d = M.faceOf (M.alpha d)) (heout : M.faceOf e ≠ outer)
    (haout : M.faceOf (M.alpha e) ≠ outer) (hd : Oriented M outer d) (he : Oriented M outer e)
    (hside : Relation.EqvGen (AvoidEdgeStep M d) e (M.alpha d)) (hed : e ≠ d)
    (hea : e ≠ M.alpha d) :
    Relation.EqvGen (AvoidEdgeStep M e) d e := by
  have hbridge := not_eqvGen_alpha_of_sameFace M hM d hface
  have hnot : ¬ Relation.EqvGen (AvoidEdgeStep M d) e d := fun h =>
    hbridge (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hside)
  have hee : Relation.EqvGen (AvoidEdgeStep M d) e (M.alpha e) :=
    Relation.EqvGen.rel _ _ (Or.inr ⟨hed, hea, rfl⟩)
  have hnot' : ¬ Relation.EqvGen (AvoidEdgeStep M d) (M.alpha e) d := fun h =>
    hnot (Relation.EqvGen.trans _ _ _ hee h)
  obtain ⟨o, ho, hdo⟩ := hd
  obtain ⟨o', ho', heo⟩ := he
  have hdo' : Relation.EqvGen (AvoidEdgeStep M e) d o :=
    eqvGen_transfer hnot hnot' hdo (Relation.EqvGen.refl d)
  have hoo : Relation.EqvGen (AvoidEdgeStep M e) o o' :=
    eqvGen_of_faceOf_eq (ho.trans ho'.symm) (fun h => heout (h.trans ho))
      (fun h => haout (h.trans ho))
  exact Relation.EqvGen.trans _ _ _ hdo'
    (Relation.EqvGen.trans _ _ _ hoo (Relation.EqvGen.symm _ _ heo))

/-- **Two same-face edges on one face cycle do not cross.**  Let `x₀, f x₀, …, f^{n-1} x₀` be
distinct with `f^n x₀ = x₀`.  No two edges join positions `p < r < q < s` as `p` to `q` and `r`
to `s`. -/
theorem false_of_cross (hM : M.IsPlanar) {x₀ : M.Dart} {n : ℕ}
    (hcyc : (M.facePerm ^ n) x₀ = x₀)
    (hinj : ∀ a b, a < n → b < n → (M.facePerm ^ a) x₀ = (M.facePerm ^ b) x₀ → a = b)
    {p r q s : ℕ} (hpr : p < r) (hrq : r < q) (hqs : q < s) (hsn : s < n)
    (hp : M.alpha ((M.facePerm ^ p) x₀) = (M.facePerm ^ q) x₀)
    (hr : M.alpha ((M.facePerm ^ r) x₀) = (M.facePerm ^ s) x₀) : False := by
  have hne : ∀ a b, a < n → b < n → a ≠ b → (M.facePerm ^ a) x₀ ≠ (M.facePerm ^ b) x₀ :=
    fun a b ha hb hab h => hab (hinj a b ha hb h)
  have hrq' : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ p) x₀)) ((M.facePerm ^ r) x₀)
      ((M.facePerm ^ q) x₀) := by
    refine eqvGen_facePerm_pow_of_le x₀ hrq.le fun t hrt htq => ?_
    rw [hp]
    exact ⟨hne t p (by omega) (by omega) (by omega), hne t q (by omega) (by omega) (by omega)⟩
  have hsn' : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ p) x₀)) ((M.facePerm ^ s) x₀)
      ((M.facePerm ^ n) x₀) := by
    refine eqvGen_facePerm_pow_of_le x₀ hsn.le fun t hst htn => ?_
    rw [hp]
    exact ⟨hne t p (by omega) (by omega) (by omega), hne t q (by omega) (by omega) (by omega)⟩
  have h0p : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ p) x₀)) ((M.facePerm ^ 0) x₀)
      ((M.facePerm ^ p) x₀) := by
    refine eqvGen_facePerm_pow_of_le x₀ (Nat.zero_le p) fun t _ htp => ?_
    rw [hp]
    exact ⟨hne t p (by omega) (by omega) (by omega), hne t q (by omega) (by omega) (by omega)⟩
  rw [hcyc] at hsn'
  rw [pow_zero, Equiv.Perm.one_apply] at h0p
  have hstep : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ p) x₀)) ((M.facePerm ^ r) x₀)
      (M.alpha ((M.facePerm ^ r) x₀)) := by
    refine Relation.EqvGen.rel _ _ (Or.inr ⟨hne r p (by omega) (by omega) (by omega), ?_, rfl⟩)
    rw [hp]
    exact hne r q (by omega) (by omega) (by omega)
  rw [hr] at hstep
  have hface : M.faceOf ((M.facePerm ^ p) x₀) = M.faceOf (M.alpha ((M.facePerm ^ p) x₀)) := by
    rw [hp, faceOf_facePerm_pow, faceOf_facePerm_pow]
  refine not_eqvGen_alpha_of_sameFace M hM _ hface ?_
  rw [hp]
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h0p)
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hsn')
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hstep) hrq'))

/-- **The reverse of an oriented dart comes later.**  Let `x₀, f x₀, …, f^{n-1} x₀` be distinct
with `f^n x₀ = x₀`, off the outer face.  Let `x₀` be oriented with reverse `f^{m₀} x₀`, and let no
oriented dart `f^q x₀` reach its reverse in more than `m₀` face steps.  Then the reverse of every
oriented dart `f^q x₀` is some `f^s x₀` with `q < s`. -/
theorem lt_of_oriented (hM : M.IsPlanar) {outer : M.Face} {x₀ : M.Dart} {n m₀ : ℕ}
    (hcyc : (M.facePerm ^ n) x₀ = x₀)
    (hinj : ∀ a b, a < n → b < n → (M.facePerm ^ a) x₀ = (M.facePerm ^ b) x₀ → a = b)
    (hout : M.faceOf x₀ ≠ outer) (hx₀ : Oriented M outer x₀) (hm₀ : m₀ < n)
    (hα : M.alpha x₀ = (M.facePerm ^ m₀) x₀)
    (hmax : ∀ q s, q < n → s < n → Oriented M outer ((M.facePerm ^ q) x₀) →
      M.alpha ((M.facePerm ^ q) x₀) = (M.facePerm ^ s) x₀ → (s + n - q) % n ≤ m₀)
    {q s : ℕ} (hq : q < n) (hs : s < n) (hor : Oriented M outer ((M.facePerm ^ q) x₀))
    (hqs : M.alpha ((M.facePerm ^ q) x₀) = (M.facePerm ^ s) x₀) : q < s := by
  have hne : ∀ a b, a < n → b < n → a ≠ b → (M.facePerm ^ a) x₀ ≠ (M.facePerm ^ b) x₀ :=
    fun a b ha hb hab h => hab (hinj a b ha hb h)
  have hpos0 : (M.facePerm ^ 0) x₀ = x₀ := by rw [pow_zero, Equiv.Perm.one_apply]
  have hface : ∀ t, M.faceOf ((M.facePerm ^ t) x₀) = M.faceOf x₀ := faceOf_facePerm_pow M x₀
  have hsq : M.alpha ((M.facePerm ^ s) x₀) = (M.facePerm ^ q) x₀ := by
    rw [← hqs]
    exact M.alpha_involutive _
  by_contra hlt
  have hsq' : s < q := by
    have hsne : s ≠ q := fun h =>
      M.alpha_fixedPointFree ((M.facePerm ^ q) x₀) (by rw [hqs, h])
    omega
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · -- the reverse of `f^q x₀` is `x₀`
    have hq' : (M.facePerm ^ q) x₀ = M.alpha x₀ := by
      rw [← hsq, hs0, hpos0]
    exact not_oriented_both hM (by rw [← hq', hface]) hout hx₀ (by rw [← hq']; exact hor)
  rcases lt_trichotomy m₀ s with hms | hms | hms
  · -- a longer pocket
    have h := hmax q s hq hs hor hqs
    have hmod : (s + n - q) % n = s + n - q := Nat.mod_eq_of_lt (by omega)
    rw [hmod] at h
    omega
  · -- `f^q x₀ = x₀`
    have h : (M.facePerm ^ q) x₀ = (M.facePerm ^ 0) x₀ :=
      M.alpha.injective (by rw [hqs, hpos0, hα, hms])
    exact hne q 0 hq (by omega) (by omega) h
  rcases lt_trichotomy m₀ q with hmq | hmq | hmq
  · -- crossing edges
    exact false_of_cross hM hcyc hinj hs0 hms hmq hq (by rw [hpos0, hα]) hsq
  · -- `f^s x₀ = x₀`
    have h : (M.facePerm ^ s) x₀ = (M.facePerm ^ 0) x₀ := by
      rw [hpos0, ← hqs, ← hmq, ← hα]
      exact M.alpha_involutive x₀
    exact hne s 0 hs (by omega) (by omega) h
  -- a neighbouring oriented dart
  have hαface : M.faceOf x₀ = M.faceOf (M.alpha x₀) := by rw [hα, hface]
  have hside : Relation.EqvGen (AvoidEdgeStep M x₀) ((M.facePerm ^ q) x₀) (M.alpha x₀) := by
    rw [hα]
    refine eqvGen_facePerm_pow_of_le x₀ hmq.le fun t hqt htm => ?_
    rw [hα]
    exact ⟨fun h => hne t 0 (by omega) (by omega) (by omega) (h.trans hpos0.symm),
      hne t m₀ (by omega) hm₀ (by omega)⟩
  have hlam : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ q) x₀)) x₀
      ((M.facePerm ^ q) x₀) :=
    eqvGen_of_oriented_side hM hαface (by rw [hface]; exact hout)
      (by rw [hqs, hface]; exact hout) hx₀ hor hside
      (fun h => hne q 0 hq (by omega) (by omega) (h.trans hpos0.symm))
      (by rw [hα]; exact hne q m₀ hq hm₀ (by omega))
  have h0s : Relation.EqvGen (AvoidEdgeStep M ((M.facePerm ^ q) x₀)) ((M.facePerm ^ 0) x₀)
      ((M.facePerm ^ s) x₀) := by
    refine eqvGen_facePerm_pow_of_le x₀ (Nat.zero_le s) fun t _ hts => ?_
    rw [hqs]
    exact ⟨hne t q (by omega) hq (by omega), hne t s (by omega) hs (by omega)⟩
  rw [hpos0] at h0s
  have hqface :
      M.faceOf ((M.facePerm ^ q) x₀) = M.faceOf (M.alpha ((M.facePerm ^ q) x₀)) := by
    rw [hqs, hface, hface]
  refine not_eqvGen_alpha_of_sameFace M hM _ hqface ?_
  rw [hqs]
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hlam) h0s

end AvoidEdgeStep

/-- **Printed endpoint.**  On a planar map, two same-face edges on one face cycle do not cross. -/
def OsinUnboundSameCellNoCross : Prop :=
  ∀ (M : CombMap.{u}), M.IsPlanar → ∀ (x₀ : M.Dart) (n : ℕ), (M.facePerm ^ n) x₀ = x₀ →
    (∀ a b, a < n → b < n → (M.facePerm ^ a) x₀ = (M.facePerm ^ b) x₀ → a = b) →
    ∀ p r q s : ℕ, p < r → r < q → q < s → s < n →
      M.alpha ((M.facePerm ^ p) x₀) = (M.facePerm ^ q) x₀ →
      M.alpha ((M.facePerm ^ r) x₀) ≠ (M.facePerm ^ s) x₀

theorem osinUnboundSameCellNoCross_holds : OsinUnboundSameCellNoCross.{u} := by
  intro M hM x₀ n hcyc hinj p r q s hpr hrq hqs hsn hp hr
  exact AvoidEdgeStep.false_of_cross hM hcyc hinj hpr hrq hqs hsn hp hr

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinUnboundSameCellNoCross_holds
#audit_axioms GroupApproximation.GGT.VanKampen.AvoidEdgeStep.lt_of_oriented
#audit_axioms GroupApproximation.GGT.VanKampen.AvoidEdgeStep.eqvGen_or
