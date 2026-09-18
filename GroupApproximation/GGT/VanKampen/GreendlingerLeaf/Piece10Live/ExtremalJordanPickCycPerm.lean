import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCycClass
import GroupApproximation.Meta.AxiomGuard

/-!
# One outside class per orbit of the face permutation

Lane gl-p10-44.  Notation as in `ExtremalJordanPickCycClass`: `M = X.toCombMap`,
`c = K.boundary.cycle`, `R = FaceClassStep M (walkKeep M c)`, `P = walkMap M c`,
`f = extremalJordanPickCountParity_perm K`.

**Theorem.**  For `d, d' ∈ c`: `α d ~R α d'` if and only if `SameCycle f d d'`.

**Proof.**
* `f` maps `c` into `c` (`extremalJordanPickCountParity_alpha_sigma_mem`), so `f^n d ∈ c`.
* (⇐) Let `d ∈ c`.  `σ_P d = σ^m d` with `m > 0`, and `σ^t d` is unkept for `0 < t < m`
  (`extremalJordanPickCountParity_sigma_spec`).  Since `σ^t (α (α d)) = σ^t d`, the run lemma
  `faceClass_run` gives `α d ~R σ^m d = σ_P d = α (f d)`.  Iterating, `α d ~R α (f^n d)`.  A
  `SameCycle` pair is `d' = f^n d` for some `n : ℕ`.
* (⇒) Let `α d ~R α d'`.  `P` is a connected restriction of the planar map `M`, so the
  separation theorem `IsRestriction.faceOf_eq_of_faceClass` puts the darts `α d`, `α d'` of `P`
  on one face of `P`: `α d' = (facePerm_P)^n (α d)` for some `n`.  For `e ∈ c`,
  `facePerm_P (α e) = σ_P (α_P (α e)) = σ_P e`, whose value is `α (f e)`.  By induction,
  `(facePerm_P)^n (α d)` has value `α (f^n d)`.  So `α d' = α (f^n d)` and `d' = f^n d`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section CycPerm

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The face permutation maps walk darts to walk darts. -/
theorem extremalJordanPickCyc_perm_mem (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) :
    extremalJordanPickCountParity_perm K d ∈ K.boundary.cycle := by
  rw [extremalJordanPickCountParity_perm_apply, extremalJordanPickCountParity_fun_of_mem K hd]
  exact extremalJordanPickCountParity_alpha_sigma_mem K hd

/-- The powers of the face permutation map walk darts to walk darts. -/
theorem extremalJordanPickCyc_pow_mem (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) (n : ℕ) :
    (extremalJordanPickCountParity_perm K ^ n) d ∈ K.boundary.cycle := by
  induction n with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]; exact hd
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact extremalJordanPickCyc_perm_mem K ih

/-- **One step**: `α d` and `α (f d)` lie in one face class off the walk. -/
theorem extremalJordanPickCyc_class_perm (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
      (X.toCombMap.alpha d) (X.toCombMap.alpha (extremalJordanPickCountParity_perm K d)) := by
  obtain ⟨m, hm, hpm, hfree⟩ := extremalJordanPickCountParity_sigma_spec K d (Or.inl hd)
  have hrun := faceClass_run X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
    (X.toCombMap.alpha d) m (fun k hk hkm => by
      rw [X.toCombMap.alpha_involutive d]
      exact hfree k hk hkm) m hm le_rfl
  rw [X.toCombMap.alpha_involutive d, hpm] at hrun
  have he : X.toCombMap.alpha (extremalJordanPickCountParity_perm K d) =
      (CombMap.PredicateRestriction.sigma X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)
        ⟨d, Or.inl hd⟩).1 := by
    rw [extremalJordanPickCountParity_perm_apply, extremalJordanPickCountParity_fun_of_mem K hd]
    exact X.toCombMap.alpha_involutive _
  rw [he]
  exact hrun

/-- **Iterated steps**: `α d` and `α (f^n d)` lie in one face class off the walk. -/
theorem extremalJordanPickCyc_class_pow (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) (n : ℕ) :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
      (X.toCombMap.alpha d)
      (X.toCombMap.alpha ((extremalJordanPickCountParity_perm K ^ n) d)) := by
  induction n with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]; exact Relation.EqvGen.refl _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact Relation.EqvGen.trans _ _ _ ih
      (extremalJordanPickCyc_class_perm K (extremalJordanPickCyc_pow_mem K hd n))

/-- **(⇐)**: one cycle of `f` gives one face class of the reversed darts. -/
theorem extremalJordanPickCyc_class_of_sameCycle (K : PocketFaceSet D eps X lo hi)
    {d d' : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle)
    (h : (extremalJordanPickCountParity_perm K).SameCycle d d') :
    Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
      (X.toCombMap.alpha d) (X.toCombMap.alpha d') := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact extremalJordanPickCyc_class_pow K hd n

end CycPerm

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_perm_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_pow_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_class_perm
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_class_pow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCyc_class_of_sameCycle
