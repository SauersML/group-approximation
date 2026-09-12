import GroupApproximation.GGT.VanKampen.OneFaceWordTrivial
import GroupApproximation.Meta.AxiomGuard

/-!
# Face rotation after deleting an edge between two faces

The inductive step of the easy van Kampen lemma merges an inner face `g` into
the outer face `O` by deleting one edge `a` with `a` on `O` and `alpha a` on
`g`.  This file supplies the map-level facts that step needs.

* `CombMap.exists_dart_faceOf_alpha_ne`: in a connected map with at least two
  faces, every face has a dart whose reverse lies on a different face.
* `EdgeDeletion.value_facePerm_of_ne`: after deleting `a`, a surviving dart
  whose old successor was `a` now jumps to the successor of `alpha a`, and one
  whose old successor was `alpha a` jumps to the successor of `a`; every other
  dart keeps its successor.  Both faces are assumed to have degree at least two,
  which is the case for relator faces of length at least two.
* `EdgeDeletion.value_facePerm_pow`: along a stretch of old face rotation that
  never steps onto the deleted edge, the new rotation agrees with the old one.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv PermOrbitErasePoint

universe u

namespace CombMap

variable (M : CombMap.{u})

/-- Vertex rotation is face rotation after edge reversal. -/
theorem sigma_eq_facePerm_alpha (x : M.Dart) : M.sigma x = M.facePerm (M.alpha x) := by
  show M.sigma x = M.sigma (M.alpha (M.alpha x))
  rw [M.alpha_involutive]

/-- **A connected map with at least two faces has an edge leaving any given
face.** -/
theorem exists_dart_faceOf_alpha_ne (hM : M.IsConnected) (O : M.Face)
    (hF : 1 < M.faceCount) : ∃ d : M.Dart, M.faceOf d = O ∧ M.faceOf (M.alpha d) ≠ O := by
  by_contra hno
  have hclosed : ∀ x, M.faceOf x = O → M.faceOf (M.alpha x) = O := by
    intro x hx
    by_contra hne
    exact hno ⟨x, hx, hne⟩
  have hstep : ∀ u v : M.Dart, M.Adjacent u v → (M.faceOf u = O ↔ M.faceOf v = O) := by
    intro u v huv
    rcases huv with h | h
    · subst h
      constructor
      · exact hclosed u
      · intro hv
        have h2 := hclosed (M.alpha u) hv
        rwa [M.alpha_involutive] at h2
    · subst h
      rw [M.sigma_eq_facePerm_alpha, M.faceOf_facePerm]
      constructor
      · exact hclosed u
      · intro hv
        have h2 := hclosed (M.alpha u) hv
        rwa [M.alpha_involutive] at h2
  have hgen : ∀ u v, Relation.EqvGen M.Adjacent u v → (M.faceOf u = O ↔ M.faceOf v = O) := by
    intro u v h
    induction h with
    | rel u v h => exact hstep u v h
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨x₀, hx₀⟩ := Quotient.exists_rep O
  have hx₀' : M.faceOf x₀ = O := hx₀
  have hall : ∀ y, M.faceOf y = O := fun y => (hgen x₀ y (hM x₀ y)).mp hx₀'
  have hsub : Subsingleton M.Face := by
    constructor
    intro f g
    obtain ⟨y, hy⟩ := Quotient.exists_rep f
    obtain ⟨z, hz⟩ := Quotient.exists_rep g
    have hy' : M.faceOf y = f := hy
    have hz' : M.faceOf z = g := hz
    rw [← hy', ← hz', hall y, hall z]
  have hle : M.faceCount ≤ 1 := by
    rw [CombMap.faceCount, Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff_subsingleton.mpr hsub
  omega

end CombMap

namespace EdgeDeletionFaces

variable {D : Type u} [DecidableEq D]

/-- Erasing a point from a permutation, read on a retained point. -/
theorem erase_val_ite (p : Perm D) (b : D) (y : {x : D // x ≠ b}) :
    (erase p b y).1 = if p y.1 = b then p b else p y.1 := by
  rw [erase_val, isolate, Perm.mul_apply, Equiv.swap_apply_def]
  by_cases h1 : p y.1 = b
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    have h2 : p y.1 ≠ p b := fun h => y.2 (p.injective h)
    rw [if_neg h2]

end EdgeDeletionFaces

namespace EdgeDeletion

open EdgeDeletionFaces

variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

/-- **Face rotation after deleting an edge.**  Both sides of the deleted edge
are assumed to lie on faces of degree at least two. -/
theorem value_facePerm_of_ne (ha : M.facePerm a ≠ a)
    (hb : M.facePerm (M.alpha a) ≠ M.alpha a) (x : Dart M a) :
    value M a ((toCombMap M a).facePerm x) =
      if M.facePerm (value M a x) = a then M.facePerm (M.alpha a)
      else if M.facePerm (value M a x) = M.alpha a then M.facePerm a
      else M.facePerm (value M a x) := by
  have hp : ∀ z : M.Dart, (M.sigma * unpair M a) z =
      M.sigma (M.alpha (Equiv.swap a (M.alpha a) z)) := fun z => rfl
  have hpa : (M.sigma * unpair M a) a = M.facePerm (M.alpha a) := by
    rw [hp, Equiv.swap_apply_left, M.alpha_involutive]
    exact M.sigma_eq_facePerm_alpha a
  have hpαa : (M.sigma * unpair M a) (M.alpha a) = M.facePerm a := by
    rw [hp, Equiv.swap_apply_right]
    rfl
  have hpz : ∀ z, z ≠ a → z ≠ M.alpha a → (M.sigma * unpair M a) z = M.facePerm z := by
    intro z h1 h2
    rw [hp, Equiv.swap_apply_of_ne_of_ne h1 h2]
    rfl
  have hfirst : ∀ y : FirstDart M a, ((erase (M.sigma * unpair M a) a) y).1 =
      if (M.sigma * unpair M a) y.1 = a then M.facePerm (M.alpha a)
      else (M.sigma * unpair M a) y.1 := by
    intro y
    rw [erase_val_ite, hpa]
  have hx1 : ((erase (M.sigma * unpair M a) a) x.1).1 =
      if M.facePerm (value M a x) = a then M.facePerm (M.alpha a)
      else M.facePerm (value M a x) := by
    rw [hfirst, hpz x.1.1 (value_ne M a x) (value_ne_reverse M a x)]
    rfl
  have hra : ((erase (M.sigma * unpair M a) a) (reverseDart M a)).1 = M.facePerm a := by
    rw [hfirst]
    change (if (M.sigma * unpair M a) (M.alpha a) = a then M.facePerm (M.alpha a)
      else (M.sigma * unpair M a) (M.alpha a)) = M.facePerm a
    rw [hpαa, if_neg ha]
  rw [facePerm_eq]
  change ((erase (erase (M.sigma * unpair M a) a) (reverseDart M a)) x).1.1 = _
  rw [erase_val_ite]
  by_cases h1 : M.facePerm (value M a x) = a
  · have hne : (erase (M.sigma * unpair M a) a) x.1 ≠ reverseDart M a := by
      intro h
      have h' := congrArg Subtype.val h
      rw [hx1, if_pos h1] at h'
      exact hb h'
    rw [if_neg hne, hx1, if_pos h1, if_pos h1]
  · by_cases h2 : M.facePerm (value M a x) = M.alpha a
    · have heq : (erase (M.sigma * unpair M a) a) x.1 = reverseDart M a := by
        apply Subtype.ext
        rw [hx1, if_neg h1]
        exact h2
      rw [if_pos heq, hra, if_neg h1, if_pos h2]
    · have hne : (erase (M.sigma * unpair M a) a) x.1 ≠ reverseDart M a := by
        intro h
        have h' := congrArg Subtype.val h
        rw [hx1, if_neg h1] at h'
        exact h2 h'
      rw [if_neg hne, hx1, if_neg h1, if_neg h1, if_neg h2]

/-- **Along a stretch avoiding the deleted edge the rotation is unchanged.** -/
theorem value_facePerm_pow (ha : M.facePerm a ≠ a)
    (hb : M.facePerm (M.alpha a) ≠ M.alpha a) (x : Dart M a) (k : ℕ)
    (hk : ∀ i < k, M.facePerm ((M.facePerm ^ i) (value M a x)) ≠ a ∧
      M.facePerm ((M.facePerm ^ i) (value M a x)) ≠ M.alpha a) :
    value M a (((toCombMap M a).facePerm ^ k) x) = (M.facePerm ^ k) (value M a x) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Perm.one_apply, Perm.one_apply]
  | succ k ih =>
      rw [pow_succ', Perm.mul_apply, value_facePerm_of_ne M a ha hb,
        ih (fun i hi => hk i (by omega)), if_neg (hk k (by omega)).1,
        if_neg (hk k (by omega)).2, pow_succ' M.facePerm, Perm.mul_apply]

end EdgeDeletion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.sigma_eq_facePerm_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.exists_dart_faceOf_alpha_ne
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletionFaces.erase_val_ite
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.value_facePerm_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.value_facePerm_pow
