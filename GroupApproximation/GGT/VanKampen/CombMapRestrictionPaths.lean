import GroupApproximation.GGT.VanKampen.CombMapRestriction
import GroupApproximation.GGT.VanKampen.CombMapEdgeInsertion

/-!
# Paths, full retention, and a frontier for map restrictions

A nonempty proper restriction of a connected map has a missing dart directly
after a retained dart in vertex rotation. This will let us grow a connected
retained core one actual edge at a time, without assuming a deletion order.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv
universe u v

namespace PermFirstReturn

theorem apply_eq_of_mem_range {A : Type u} {B : Type v}
    (p : Perm A) (q : Perm B) (e : B ↪ A) (h : IsFirstReturn p q e)
    (b : B) (hb : p (e b) ∈ Set.range e) : p (e b) = e (q b) := by
  obtain ⟨m, hm, hnext, hskip⟩ := h b
  have hm1 : m = 1 := by
    have hle : ¬ 1 < m := fun hlt => hskip 1 (by omega) hlt (by simpa using hb)
    omega
  simpa only [hm1, pow_one] using hnext

end PermFirstReturn

namespace CombMap.IsRestriction

variable {M : CombMap.{u}} {N : CombMap.{v}} {e : N.Dart ↪ M.Dart}

theorem reachable (h : M.IsRestriction N e) {d d' : N.Dart}
    (hp : Relation.EqvGen N.Adjacent d d') : Relation.EqvGen M.Adjacent (e d) (e d') := by
  induction hp with
  | rel d d' hp =>
      rcases hp with rfl | rfl
      · rw [h.alpha_map]
        exact .rel _ _ (Or.inl rfl)
      · obtain ⟨n, _, hn, _⟩ := h.sigma_firstReturn d
        exact M.eqvGen_of_sameCycle_sigma
          ⟨(n : ℤ), by simpa only [zpow_natCast] using hn⟩
  | refl d => exact .refl _
  | symm d d' _ ih => exact ih.symm
  | trans d d' d'' _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Intertwined permutations preserve and reflect membership in the image. -/
theorem range_perm_iff {A : Type u} {B : Type v} (p : Perm A) (q : Perm B)
    (f : B ↪ A) (hf : ∀ b, f (q b) = p (f b)) (a : A) :
    p a ∈ Set.range f ↔ a ∈ Set.range f := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨q.symm b, p.injective ?_⟩
    rw [← hf, q.apply_symm_apply]
    exact hb
  · rintro ⟨b, rfl⟩
    exact ⟨q b, hf b⟩

theorem range_alpha_iff (h : M.IsRestriction N e) (a : M.Dart) :
    M.alpha a ∈ Set.range e ↔ a ∈ Set.range e :=
  range_perm_iff M.alpha N.alpha e h.alpha_map a

/-- A proper retained core has an edge available for growth at one of its
vertices. The frontier is an actual single vertex-rotation step. -/
theorem exists_sigma_frontier (h : M.IsRestriction N e) (hM : M.IsConnected)
    (d : N.Dart) (hne : ¬ Function.Surjective e) :
    ∃ b : N.Dart, M.sigma (e b) ∉ Set.range e := by
  classical
  by_contra hfront
  push Not at hfront
  have hs (b : N.Dart) : e (N.sigma b) = M.sigma (e b) :=
    (PermFirstReturn.apply_eq_of_mem_range _ _ _ h.sigma_firstReturn b (hfront b)).symm
  have hpath {a b : M.Dart} (hp : Relation.EqvGen M.Adjacent a b) :
      a ∈ Set.range e ↔ b ∈ Set.range e := by
    induction hp with
    | rel a b hp =>
        rcases hp with rfl | rfl
        · exact (h.range_alpha_iff a).symm
        · exact (range_perm_iff M.sigma N.sigma e hs a).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact hne (fun a => (hpath (hM (e d) a)).mp ⟨d, rfl⟩)

/-- Retaining every dart preserves each map permutation and all counts. -/
theorem euler_eq_of_surjective (h : M.IsRestriction N e) (he : Function.Surjective e) :
    N.eulerCharacteristic = M.eulerCharacteristic := by
  let E : N.Dart ≃ M.Dart := Equiv.ofBijective e ⟨e.injective, he⟩
  have hs (d : N.Dart) : e (N.sigma d) = M.sigma (e d) :=
    (PermFirstReturn.apply_eq_of_mem_range _ _ _ h.sigma_firstReturn d (he _)).symm
  have hsigma : M.sigma = E.permCongr N.sigma := by
    apply Equiv.ext
    intro x
    obtain ⟨d, rfl⟩ := E.surjective x
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    simpa only [E, Equiv.ofBijective_apply] using (hs d).symm
  have hface : M.facePerm = E.permCongr N.facePerm := by
    apply Equiv.ext
    intro x
    obtain ⟨d, rfl⟩ := E.surjective x
    have hd : e (N.facePerm d) = M.facePerm (e d) :=
      (hs (N.alpha d)).trans (congrArg M.sigma (h.alpha_map d))
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    simpa only [E, Equiv.ofBijective_apply] using hd.symm
  have hv : M.vertexCount = N.vertexCount := by
    change Nat.card (CombMap.Orbit M.sigma) = Nat.card (CombMap.Orbit N.sigma)
    rw [hsigma]
    exact (Nat.card_congr (orbitPermCongr E N.sigma)).symm
  have hf : M.faceCount = N.faceCount := by
    change Nat.card (CombMap.Orbit M.facePerm) = Nat.card (CombMap.Orbit N.facePerm)
    rw [hface]
    exact (Nat.card_congr (orbitPermCongr E N.facePerm)).symm
  have hd : M.dartCount = N.dartCount := (Nat.card_congr E).symm
  have hedge : M.edgeCount = N.edgeCount := by
    rw [M.dartCount_eq_two_mul_edgeCount, N.dartCount_eq_two_mul_edgeCount] at hd
    omega
  simp only [CombMap.eulerCharacteristic, hv, hf, hedge]

end CombMap.IsRestriction

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.IsRestriction.exists_sigma_frontier
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.IsRestriction.euler_eq_of_surjective
