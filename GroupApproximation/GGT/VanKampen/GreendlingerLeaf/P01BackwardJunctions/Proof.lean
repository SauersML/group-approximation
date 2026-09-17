import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BoundaryJunctionBudget
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94JunctionPocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: at most `n + 1` backward junctions

Target: `OsinLemma94BackwardJunctionCountInput`.  Summed over the relator polygons, the backward
boundary junctions number at most `n + 1`, where `n` is the number of relator cells.

## Route

Write `w = outerDarts Δ` (length `m`), `M` for the map of `Δ`, `O` for the outer face.  The
outer walk satisfies `σ w[q+1] = α w[q]` (the face chain of `O`, reversed and reflected by `α`),
`w` has no repeated darts, and `faceOf (α w[q]) = O`.

A backward junction `s` of polygon `k` gives darts `e` (last dart of side `s`) and `e'` (first
dart of the next side), both on `w`, with `facePerm e = e'`, i.e. `σ (α w[a]) = w[b]`, where
`a = idxOf e`, `b = idxOf e'` and `b ≤ a`.  Call it *degenerate* when `e = w[m-1]`.

1. **Pocket.**  Take a non-degenerate junction `(a, b)`, so `a + 1 < m`.  The darts
   `p = α w[b]` and `q = α w[a+1]` lie on `O` and `σ` has `α p = w[b]` and
   `α q = w[a+1]` in one cycle (`σ² w[a+1] = w[b]`).  `JunctionPocket.not_reach` says
   `facePerm p` and `facePerm q` are apart in the joined map.  `facePerm q = α w[a]` is next to
   `w[a]`.  For every `c < b` or `c > a`, the dart `w[c]` is reached from `facePerm p`: walking
   along `w` by `α` and `σ` never touches `α p, α q` outside `[b, a+1]`, and the joined map
   turns `w[a+1]` into `facePerm p` (`not_reach_outside`).  So `w[a]` does not reach `w[c]`.
2. **Cell link.**  If two junctions `(a, b)` and `(c, d)` belong to polygons with a common
   relator cell `j`, then `w[a]` reaches `w[c]` in every join at two darts of `O`: go inside
   polygon face, cross to cell `j` and back (`reach_via_cell`).  With step 1 in both directions
   `b ≤ c ≤ a` and `d ≤ a ≤ c`, so `a = c` (`index_eq`).
3. **Count.**  Label a junction by `none` when degenerate, else by the first cell of its polygon.
   Equal labels force equal last darts `e`, and `e` determines polygon and side (the face of
   `e`, disjoint sides).  So the junctions inject into `Option (Fin n)`, of size `n + 1`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01BackwardJunctions

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

section Pocket

variable {M : CombMap.{v}} [DecidableEq M.Dart]

/-- Walking backward along the outer walk in the joined map, away from the joined darts. -/
theorem reach_chain {f : ℕ → M.Dart} {m : ℕ}
    (hstep : ∀ q, q + 1 < m → M.sigma (f (q + 1)) = M.alpha (f q)) {p e : M.Dart} (i : ℕ) :
    ∀ d, i + d < m → (∀ q, i < q → q ≤ i + d → f q ≠ M.alpha p ∧ f q ≠ M.alpha e) →
      Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.alpha (f (i + d))) (M.alpha (f i)) := by
  intro d
  induction d with
  | zero =>
      intro _ _
      exact Relation.EqvGen.refl _
  | succ d ih =>
      intro hd hq
      have hq' := hq (i + d + 1) (by omega) (by omega)
      have h1 : Relation.EqvGen (FoldMap.joined M p e).Adjacent (M.alpha (f (i + d + 1)))
          (f (i + d + 1)) :=
        Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive (f (i + d + 1))))
      have h2 : Relation.EqvGen (FoldMap.joined M p e).Adjacent (f (i + d + 1))
          (M.alpha (f (i + d))) :=
        Relation.EqvGen.rel _ _
          (Or.inr ((JunctionPocket.joined_sigma_apply_of_ne hq'.1 hq'.2).trans
            (hstep (i + d) (by omega))))
      exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.trans _ _ _ h2
        (ih (by omega) fun q hq1 hq2 => hq q hq1 (by omega)))

/-- Outside the pocket `[b, a]`, every outer dart is reached from `facePerm (α w[b])`. -/
theorem reach_outside {f : ℕ → M.Dart} {m : ℕ}
    (hstep : ∀ q, q + 1 < m → M.sigma (f (q + 1)) = M.alpha (f q))
    (hinj : ∀ i j, i < m → j < m → f i = f j → i = j)
    {a b c : ℕ} (hba : b ≤ a) (ham : a + 1 < m) (hcm : c < m) (hc : c < b ∨ a < c) :
    Relation.EqvGen (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).Adjacent
      (M.facePerm (M.alpha (f b))) (f c) := by
  have hcα : Relation.EqvGen (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).Adjacent
      (M.alpha (f c)) (f c) := Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive (f c)))
  rcases hc with hcb | hac
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hfp : M.facePerm (M.alpha (f (b' + 1))) = M.alpha (f b') := by
      show M.sigma (M.alpha (M.alpha (f (b' + 1)))) = M.alpha (f b')
      rw [M.alpha_involutive (f (b' + 1))]
      exact hstep b' (by omega)
    have hch := reach_chain hstep (p := M.alpha (f (b' + 1))) (e := M.alpha (f (a + 1))) c (b' - c)
      (by omega) fun q hq1 hq2 => by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [M.alpha_involutive] at h
          have := hinj q (b' + 1) (by omega) (by omega) h
          omega
        · rw [M.alpha_involutive] at h
          have := hinj q (a + 1) (by omega) ham h
          omega
    rw [show c + (b' - c) = b' by omega] at hch
    rw [hfp]
    exact Relation.EqvGen.trans _ _ _ hch hcα
  · have hsig : (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).sigma (f (a + 1)) =
        M.facePerm (M.alpha (f b)) := by
      have h := JunctionPocket.joined_sigma_alpha_right (M := M) (M.alpha (f b)) (M.alpha (f (a + 1)))
      rwa [M.alpha_involutive (f (a + 1))] at h
    have hch := reach_chain hstep (p := M.alpha (f b)) (e := M.alpha (f (a + 1))) (a + 1)
      (c - (a + 1)) (by omega) fun q hq1 hq2 => by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [M.alpha_involutive] at h
          have := hinj q b (by omega) (by omega) h
          omega
        · rw [M.alpha_involutive] at h
          have := hinj q (a + 1) (by omega) ham h
          omega
    rw [show a + 1 + (c - (a + 1)) = c by omega] at hch
    refine Relation.EqvGen.trans _ (f (a + 1)) _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr hsig))) ?_
    refine Relation.EqvGen.trans _ (M.alpha (f (a + 1))) _
      (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hch) hcα

/-- **The pocket.**  At a junction `σ (α w[a]) = w[b]` with `b ≤ a < m - 1`, joining `α w[b]`
and `α w[a+1]` separates `w[a]` from every outer dart outside `[b, a]`. -/
theorem not_reach_outside (hM : M.IsPlanar) {f : ℕ → M.Dart} {m : ℕ} {O : M.Face}
    (hstep : ∀ q, q + 1 < m → M.sigma (f (q + 1)) = M.alpha (f q))
    (hinj : ∀ i j, i < m → j < m → f i = f j → i = j)
    (hout : ∀ q, q < m → M.faceOf (M.alpha (f q)) = O)
    {a b c : ℕ} (hba : b ≤ a) (ham : a + 1 < m) (hjun : M.sigma (M.alpha (f a)) = f b)
    (hcm : c < m) (hc : c < b ∨ a < c) :
    ¬ Relation.EqvGen (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).Adjacent
      (f a) (f c) := by
  intro hac
  have hpe : M.alpha (f b) ≠ M.alpha (f (a + 1)) := fun h => by
    have := hinj b (a + 1) (by omega) ham (M.alpha.injective h)
    omega
  have hface : M.faceOf (M.alpha (f b)) = M.faceOf (M.alpha (f (a + 1))) :=
    (hout b (by omega)).trans (hout (a + 1) ham).symm
  have hpinch : M.sigma.SameCycle (M.alpha (M.alpha (f b))) (M.alpha (M.alpha (f (a + 1)))) := by
    rw [M.alpha_involutive (f b), M.alpha_involutive (f (a + 1)), ← hjun, ← hstep a ham]
    exact (Equiv.Perm.SameCycle.rfl.apply_right.apply_right).symm
  have hA : Relation.EqvGen (FoldMap.joined M (M.alpha (f b)) (M.alpha (f (a + 1)))).Adjacent
      (M.facePerm (M.alpha (f (a + 1)))) (f a) := by
    have h : M.facePerm (M.alpha (f (a + 1))) = M.alpha (f a) := by
      show M.sigma (M.alpha (M.alpha (f (a + 1)))) = M.alpha (f a)
      rw [M.alpha_involutive (f (a + 1))]
      exact hstep a ham
    rw [h]
    exact Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive (f a)))
  have hB := reach_outside hstep hinj hba ham hcm hc
  exact JunctionPocket.not_reach hM hpe hface hpinch
    (Relation.EqvGen.trans _ _ _ hB
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hac) (Relation.EqvGen.symm _ _ hA)))

/-- **The cell link.**  Two darts of inner faces joined across one inner face stay together
after any join at two darts of `O`. -/
theorem reach_via_cell {O : M.Face} {p e x₁ x₂ y₁ y₂ : M.Dart}
    (hp : M.faceOf p = O) (he : M.faceOf e = O)
    (h₁ : M.faceOf x₁ = M.faceOf y₁) (h₁O : M.faceOf x₁ ≠ O)
    (h₂ : M.faceOf x₂ = M.faceOf y₂) (h₂O : M.faceOf x₂ ≠ O)
    (hc : M.faceOf (M.alpha y₁) = M.faceOf (M.alpha y₂)) (hcO : M.faceOf (M.alpha y₁) ≠ O) :
    Relation.EqvGen (FoldMap.joined M p e).Adjacent x₁ x₂ := by
  have hr : ∀ x z : M.Dart, M.faceOf x ≠ O → M.faceOf x = M.faceOf z →
      Relation.EqvGen (FoldMap.joined M p e).Adjacent x z := fun x z hx hxz =>
    JunctionPocket.joined_reach_of_faceOf_eq (by rw [hp]; exact hx) (by rw [he]; exact hx) hxz
  refine Relation.EqvGen.trans _ y₁ _ (hr _ _ h₁O h₁) ?_
  refine Relation.EqvGen.trans _ (M.alpha y₁) _ (Relation.EqvGen.rel _ _ (Or.inl rfl)) ?_
  refine Relation.EqvGen.trans _ (M.alpha y₂) _ (hr _ _ hcO hc) ?_
  refine Relation.EqvGen.trans _ y₂ _
    (Relation.EqvGen.rel _ _ (Or.inl (M.alpha_involutive y₂))) ?_
  exact Relation.EqvGen.symm _ _ (hr _ _ h₂O h₂)

/-- **Linked junctions coincide.** -/
theorem index_eq (hM : M.IsPlanar) {f : ℕ → M.Dart} {m : ℕ} {O : M.Face}
    (hstep : ∀ q, q + 1 < m → M.sigma (f (q + 1)) = M.alpha (f q))
    (hinj : ∀ i j, i < m → j < m → f i = f j → i = j)
    (hout : ∀ q, q < m → M.faceOf (M.alpha (f q)) = O)
    {a b c d : ℕ} (hba : b ≤ a) (ham : a + 1 < m) (hjab : M.sigma (M.alpha (f a)) = f b)
    (hdc : d ≤ c) (hcm : c + 1 < m) (hjcd : M.sigma (M.alpha (f c)) = f d)
    (hcls : ∀ p e : M.Dart, M.faceOf p = O → M.faceOf e = O →
      Relation.EqvGen (FoldMap.joined M p e).Adjacent (f a) (f c)) : a = c := by
  have hca : c ≤ a := not_lt.1 fun hlt =>
    not_reach_outside hM hstep hinj hout hba ham hjab (by omega) (Or.inr hlt)
      (hcls _ _ (hout b (by omega)) (hout (a + 1) ham))
  have hac : a ≤ c := not_lt.1 fun hlt =>
    not_reach_outside hM hstep hinj hout hdc hcm hjcd (by omega) (Or.inr hlt)
      (Relation.EqvGen.symm _ _ (hcls _ _ (hout d (by omega)) (hout (c + 1) hcm)))
  exact Nat.le_antisymm hac hca

/-- A non-last dart of a list has a successor index. -/
theorem idx_succ_lt {α : Type*} [DecidableEq α] {w l : List α} {e : α} (hmem : e ∈ w)
    (he : e ∈ l.getLast?) (hnd : l.getLast? ≠ w.getLast?) : w.idxOf e + 1 < w.length := by
  have h := List.idxOf_lt_length_of_mem hmem
  by_contra hge
  apply hnd
  have heq : w.length - 1 = w.idxOf e := by omega
  rw [Option.mem_def.1 he, List.getLast?_eq_getElem?, heq, List.getElem?_eq_getElem h,
    List.getElem_idxOf h]

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01BackwardJunctions
