import GroupApproximation.GGT.VanKampen.DartExpansion

/-! # Actual path endpoints under a dart expansion -/

namespace GroupApproximation.GGT.VanKampen.DartExpansion

open Equiv
universe u v
variable {M : CombMap.{u}} {N : CombMap.{v}} (E : DartExpansion M N)

def first (d : M.Dart) : N.Dart := (E.darts d).head (E.nonempty d)
def last (d : M.Dart) : N.Dart := (E.darts d).getLast (E.nonempty d)

theorem first_alpha (d : M.Dart) : E.first (M.alpha d) = N.alpha (E.last d) := by
  have h := congrArg List.head? (E.reverse d)
  simp only [List.head?_map, List.head?_reverse,
    List.head?_eq_some_head (E.nonempty (M.alpha d)),
    List.getLast?_eq_some_getLast (E.nonempty d), Option.map_some, Option.some.injEq] at h
  exact h

theorem last_alpha (d : M.Dart) : E.last (M.alpha d) = N.alpha (E.first d) := by
  have h := congrArg List.getLast? (E.reverse d)
  simp only [List.getLast?_map, List.getLast?_reverse,
    List.getLast?_eq_some_getLast (E.nonempty (M.alpha d)),
    List.head?_eq_some_head (E.nonempty d), Option.map_some, Option.some.injEq] at h
  exact h

theorem first_sigma (d : M.Dart) : N.sigma (E.first d) = E.first (M.sigma d) := by
  have h := E.join (M.alpha d)
  change N.facePerm (E.last (M.alpha d)) = E.first (M.facePerm (M.alpha d)) at h
  rw [E.last_alpha] at h
  simpa only [CombMap.facePerm, Perm.mul_apply, N.alpha_involutive (E.first d),
    M.alpha_involutive d] using h

theorem vertex_first_sigma (d : M.Dart) :
    N.vertexOf (E.first (M.sigma d)) = N.vertexOf (E.first d) :=
  (congrArg N.vertexOf (E.first_sigma d)).symm.trans (N.vertexOf_sigma _)

/-- Old vertices map to the initial vertices of their expanded darts. -/
def vertexMap : M.Vertex → N.Vertex :=
  Quotient.lift (fun d => N.vertexOf (E.first d)) (fun _ _ h =>
    OrbitClassifier.eq_of_sameCycle M.sigma (fun d => N.vertexOf (E.first d))
      E.vertex_first_sigma h)

theorem vertex_first (d : M.Dart) : N.vertexOf (E.first d) = E.vertexMap (M.vertexOf d) := rfl

theorem vertex_last (d : M.Dart) :
    N.vertexOf (N.alpha (E.last d)) = E.vertexMap (M.vertexOf (M.alpha d)) :=
  (congrArg N.vertexOf (E.first_alpha d)).symm

theorem first_injective : Function.Injective E.first := by
  classical
  intro d e h
  by_contra hde
  have hnd : (E.darts d ++ E.darts e).Nodup := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      E.nodup [d, e] (by simp [hde])
  have hdis := (List.nodup_append.mp hnd).2.2
  exact hdis (E.first d) (List.head_mem (E.nonempty d))
    (E.first e) (List.head_mem (E.nonempty e)) h

theorem first_sigma_pow (n : ℕ) (d : M.Dart) :
    (N.sigma ^ n) (E.first d) = E.first ((M.sigma ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih, E.first_sigma]

/-- Subdivision retains distinct old vertices. New internal vertices may be added. -/
theorem vertexMap_injective : Function.Injective E.vertexMap := by
  intro f g
  refine Quotient.inductionOn' f ?_
  intro d
  refine Quotient.inductionOn' g ?_
  intro e h
  change N.vertexOf (E.first d) = N.vertexOf (E.first e) at h
  obtain ⟨n, hn⟩ := ((N.vertexOf_eq_iff _ _).mp h).exists_nat_pow_eq
  have heq : (M.sigma ^ n) d = e := E.first_injective ((E.first_sigma_pow n d).symm.trans hn)
  have hvertex : ∀ k : ℕ, M.vertexOf ((M.sigma ^ k) d) = M.vertexOf d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Perm.mul_apply, M.vertexOf_sigma, ih]
  exact (hvertex n).symm.trans (congrArg M.vertexOf heq)

/-- The expanded face walk is also an actual edge path in the one-skeleton. -/
theorem path_chain (d : M.Dart) :
    (E.darts d).IsChain (fun x y => N.vertexOf (N.alpha x) = N.vertexOf y) := by
  apply (E.chain d).imp
  intro x y h
  exact (N.vertexOf_sigma (N.alpha x)).symm.trans (congrArg N.vertexOf h)

end GroupApproximation.GGT.VanKampen.DartExpansion

#audit_axioms GroupApproximation.GGT.VanKampen.DartExpansion.vertexMap
#audit_axioms GroupApproximation.GGT.VanKampen.DartExpansion.vertex_last
#audit_axioms GroupApproximation.GGT.VanKampen.DartExpansion.vertexMap_injective
#audit_axioms GroupApproximation.GGT.VanKampen.DartExpansion.path_chain
