import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCycPerm
import GroupApproximation.Meta.AxiomGuard

/-!
# One orbit of the face permutation per outside face class

Lane gl-p10-44.  Notation as in `ExtremalJordanPickCycClass`: `M = X.toCombMap`,
`c = K.boundary.cycle`, `R = FaceClassStep M (walkKeep M c)`, `P = walkMap M c`,
`f = extremalJordanPickCountParity_perm K`.

**Theorem** (`extremalJordanPickCyc_sameCycle_of_class`).  For `d, d' ∈ c`, if
`α d ~R α d'` then `SameCycle f d d'`.

**Proof.**
1. For `x ∈ c`, the reversed dart `α x` is a dart of `P`, and `α_P (α x) = x`.  So
   `facePerm_P (α x) = σ_P (α_P (α x)) = σ_P x`.  By definition `f x = α (σ_P x)`, so the
   value of `facePerm_P (α x)` is `α (f x)` (`extremalJordanPickCyc_facePerm_val`).
2. Since `f` maps `c` into `c`, induction on `n` gives that the value of
   `(facePerm_P)^n (α d)` is `α (f^n d)` (`extremalJordanPickCyc_facePerm_pow_val`).
3. The keep predicate `walkKeep M c` is the range of the inclusion of `P`, so `α d ~R α d'` is a
   face-class relation for the restriction `P` of `M`.  `M` is planar and `P` is connected
   (the walk is a closed walk), so the separation theorem
   `IsRestriction.faceOf_eq_of_faceClass` puts `α d` and `α d'` on one face of `P`.  Hence
   `α d' = (facePerm_P)^n (α d)` for some `n : ℕ`.  By 2, `α d' = α (f^n d)`, so `d' = f^n d`,
   and `d, d'` lie in one cycle of `f`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section CycFace

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Step 1**: on a reversed walk dart `α x`, the face permutation of the walk map has value
`α (f x)`. -/
theorem extremalJordanPickCyc_facePerm_val (K : PocketFaceSet D eps X lo hi)
    {x : X.toCombMap.Dart} (hx : x ∈ K.boundary.cycle)
    (hx' : walkKeep X.toCombMap K.boundary.cycle (X.toCombMap.alpha x)) :
    ((walkMap X.toCombMap K.boundary.cycle).facePerm ⟨X.toCombMap.alpha x, hx'⟩).1 =
      X.toCombMap.alpha (extremalJordanPickCountParity_perm K x) := by
  have h1 : (walkMap X.toCombMap K.boundary.cycle).alpha ⟨X.toCombMap.alpha x, hx'⟩ =
      ⟨x, Or.inl hx⟩ := Subtype.ext (X.toCombMap.alpha_involutive x)
  rw [CombMap.facePerm, Equiv.Perm.mul_apply, h1, extremalJordanPickCountParity_perm_apply,
    extremalJordanPickCountParity_fun_of_mem K hx]
  exact (X.toCombMap.alpha_involutive _).symm

/-- **Step 2**: the powers of the face permutation of the walk map track the powers of `f`. -/
theorem extremalJordanPickCyc_facePerm_pow_val (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle)
    (hd' : walkKeep X.toCombMap K.boundary.cycle (X.toCombMap.alpha d)) (n : ℕ) :
    (((walkMap X.toCombMap K.boundary.cycle).facePerm ^ n) ⟨X.toCombMap.alpha d, hd'⟩).1 =
      X.toCombMap.alpha ((extremalJordanPickCountParity_perm K ^ n) d) := by
  induction n with
  | zero => simp only [pow_zero, Equiv.Perm.one_apply]
  | succ n ih =>
    have hm : (extremalJordanPickCountParity_perm K ^ n) d ∈ K.boundary.cycle :=
      extremalJordanPickCyc_pow_mem K hd n
    have hk : walkKeep X.toCombMap K.boundary.cycle
        (X.toCombMap.alpha ((extremalJordanPickCountParity_perm K ^ n) d)) :=
      (walkKeep_alpha X.toCombMap K.boundary.cycle _).mpr (Or.inl hm)
    have hsub : ((walkMap X.toCombMap K.boundary.cycle).facePerm ^ n)
        ⟨X.toCombMap.alpha d, hd'⟩ =
        ⟨X.toCombMap.alpha ((extremalJordanPickCountParity_perm K ^ n) d), hk⟩ :=
      Subtype.ext ih
    rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, hsub]
    exact extremalJordanPickCyc_facePerm_val K hm hk

/-- **Step 3, (⇒)**: one face class of reversed walk darts gives one cycle of `f`. -/
theorem extremalJordanPickCyc_sameCycle_of_class (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) {d d' : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle)
    (hd' : d' ∈ K.boundary.cycle)
    (h : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (walkKeep X.toCombMap K.boundary.cycle)) (X.toCombMap.alpha d) (X.toCombMap.alpha d')) :
    (extremalJordanPickCountParity_perm K).SameCycle d d' := by
  have hk : walkKeep X.toCombMap K.boundary.cycle (X.toCombMap.alpha d) :=
    (walkKeep_alpha X.toCombMap K.boundary.cycle d).mpr (Or.inl hd)
  have hk' : walkKeep X.toCombMap K.boundary.cycle (X.toCombMap.alpha d') :=
    (walkKeep_alpha X.toCombMap K.boundary.cycle d').mpr (Or.inl hd')
  have h' : Relation.EqvGen (CombMap.FaceClassStep X.toCombMap
      (· ∈ Set.range (Function.Embedding.subtype (walkKeep X.toCombMap K.boundary.cycle))))
      (X.toCombMap.alpha d) (X.toCombMap.alpha d') :=
    SimpleClosedWalkSides.faceClass_mono X.toCombMap
      (fun x hx => by rintro ⟨z, rfl⟩; exact hx z.2) h
  have hface := (walkMap_isRestriction X.toCombMap K.boundary.cycle).faceOf_eq_of_faceClass
    X.planar (FirstTurnEnclosure.walkMap_connected K.boundary.cycle_nonempty hK.1)
    (d := ⟨X.toCombMap.alpha d, hk⟩) (d' := ⟨X.toCombMap.alpha d', hk'⟩) h'
  obtain ⟨n, hn⟩ :=
    (((walkMap X.toCombMap K.boundary.cycle).faceOf_eq_iff _ _).mp hface).exists_nat_pow_eq
  have hv := extremalJordanPickCyc_facePerm_pow_val K hd hk n
  rw [hn] at hv
  have hv' : X.toCombMap.alpha ((extremalJordanPickCountParity_perm K ^ n) d) =
      X.toCombMap.alpha d' := hv.symm
  have he : (extremalJordanPickCountParity_perm K ^ n) d = d' := X.toCombMap.alpha.injective hv'
  subst he
  exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)

end CycFace

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_facePerm_val
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_facePerm_pow_val
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_sameCycle_of_class
