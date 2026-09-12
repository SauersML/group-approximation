import GroupApproximation.Kazhdan.GHBQuotientVertexForms

/-!
# No short alternating relations in the vertex groups of `GHB(7)`

CCKW Theorem 3.1 rests on the links of the coset complex of the triangle of groups
having girth at least six.  The link of the vertex `Pᵢ` is the coset graph of `Pᵢ` with
respect to its two edge groups, and it is bipartite, so its girth is at least six exactly
when there is no relation `x₁ y₁ x₂ y₂ = 1` with the `xₖ` nontrivial in one edge group
and the `yₖ` nontrivial in the other.  This module proves that, at each of the three
vertex groups `P₀ = ⟨a,b⟩`, `P₁ = ⟨c,b⟩`, `P₂ = ⟨c,a⟩` of `GHB(7)`.

The edge groups enter only through the intersections of vertex groups, so the statements
take `x ∈ Pᵢ ⊓ Pⱼ`.  The proof pushes the relation through `ψ`
(`Kazhdan/GHBQuotientVertexForms.lean`): the image of `Pᵢ ⊓ Pⱼ` lies in the
one-parameter subfamily shared by two matrix families, `ψ` is injective on the vertex
group over the order bounds `|U₃(7)| ≤ 7³`, `|U₄(7)| ≤ 7⁴`, and a kernel evaluation of the
parameter law over `F₇⁴` excludes the relation.
-/

namespace GroupApproximation
namespace KMSGroup
namespace GHBQuotient

/-! ## Where two matrix families meet -/

theorem eq_of_matAB_eq_matCB {t : P3} {s : P4} (h : matAB t = matCB s) :
    t = (0, t.2.1, 0) := by
  obtain ⟨i, j, x⟩ := t
  have h1 := congrFun (congrFun h 0) 3
  have h2 := congrFun (congrFun h 1) 3
  simp [matAB, matCB] at h1 h2
  simp [h1, h2]

theorem eq_of_matAB_eq_matCA {t : P3} {s : P4} (h : matAB t = matCA s) :
    t = (t.1, 0, 0) := by
  obtain ⟨i, j, x⟩ := t
  have h1 := congrFun (congrFun h 1) 0
  have h2 := congrFun (congrFun h 1) 3
  simp [matAB, matCA] at h1 h2
  simp [h1, h2]

theorem eq_of_matCB_eq_matAB {s : P4} {t : P3} (h : matCB s = matAB t) :
    s = (0, s.2.1, 0, 0) := by
  obtain ⟨i, j, k, u⟩ := s
  have h1 := congrFun (congrFun h 3) 1
  have h2 := congrFun (congrFun h 2) 1
  have h3 := congrFun (congrFun h 2) 0
  simp [matCB, matAB] at h1 h2 h3
  simp [h1, h2, h3]

theorem eq_of_matCB_eq_matCA {s s' : P4} (h : matCB s = matCA s') :
    s = (s.1, 0, 0, 0) := by
  obtain ⟨i, j, k, u⟩ := s
  have h1 := congrFun (congrFun h 1) 0
  have h2 := congrFun (congrFun h 2) 1
  have h3 := congrFun (congrFun h 2) 0
  simp [matCB, matCA] at h1 h2 h3
  simp [h1, h2, h3]

theorem eq_of_matCA_eq_matAB {s : P4} {t : P3} (h : matCA s = matAB t) :
    s = (0, s.2.1, 0, 0) := by
  obtain ⟨i, j, k, w⟩ := s
  have h1 := congrFun (congrFun h 3) 1
  have h2 := congrFun (congrFun h 0) 1
  have h3 := congrFun (congrFun h 0) 2
  simp [matCA, matAB] at h1 h2 h3
  simp [h1, h2, h3]

theorem eq_of_matCA_eq_matCB {s s' : P4} (h : matCA s = matCB s') :
    s = (s.1, 0, 0, 0) := by
  obtain ⟨i, j, k, w⟩ := s
  have h1 := congrFun (congrFun h 0) 3
  have h2 := congrFun (congrFun h 0) 1
  have h3 := congrFun (congrFun h 0) 2
  simp [matCA, matCB] at h1 h2 h3
  simp [h1, h2, h3]

/-! ## The images of the edge groups -/

theorem exists_matAB_b {x : GHB 7} (h₀ : x ∈ Subgroup.closure {a 7, b 7})
    (h₁ : x ∈ Subgroup.closure {c 7, b 7}) : ∃ j, (psi x : Mat) = matAB (0, j, 0) := by
  obtain ⟨t, ht⟩ := exists_matAB_of_mem_closure (psi_mem_closure_ab h₀)
  obtain ⟨s, hs⟩ := exists_matCB_of_mem_closure (psi_mem_closure_cb h₁)
  refine ⟨t.2.1, ?_⟩
  rw [ht, ← eq_of_matAB_eq_matCB (ht.symm.trans hs)]

theorem exists_matAB_a {x : GHB 7} (h₀ : x ∈ Subgroup.closure {a 7, b 7})
    (h₂ : x ∈ Subgroup.closure {c 7, a 7}) : ∃ i, (psi x : Mat) = matAB (i, 0, 0) := by
  obtain ⟨t, ht⟩ := exists_matAB_of_mem_closure (psi_mem_closure_ab h₀)
  obtain ⟨s, hs⟩ := exists_matCA_of_mem_closure (psi_mem_closure_ca h₂)
  refine ⟨t.1, ?_⟩
  rw [ht, ← eq_of_matAB_eq_matCA (ht.symm.trans hs)]

theorem exists_matCB_b {x : GHB 7} (h₁ : x ∈ Subgroup.closure {c 7, b 7})
    (h₀ : x ∈ Subgroup.closure {a 7, b 7}) : ∃ j, (psi x : Mat) = matCB (0, j, 0, 0) := by
  obtain ⟨s, hs⟩ := exists_matCB_of_mem_closure (psi_mem_closure_cb h₁)
  obtain ⟨t, ht⟩ := exists_matAB_of_mem_closure (psi_mem_closure_ab h₀)
  refine ⟨s.2.1, ?_⟩
  rw [hs, ← eq_of_matCB_eq_matAB (hs.symm.trans ht)]

theorem exists_matCB_c {x : GHB 7} (h₁ : x ∈ Subgroup.closure {c 7, b 7})
    (h₂ : x ∈ Subgroup.closure {c 7, a 7}) : ∃ i, (psi x : Mat) = matCB (i, 0, 0, 0) := by
  obtain ⟨s, hs⟩ := exists_matCB_of_mem_closure (psi_mem_closure_cb h₁)
  obtain ⟨s', hs'⟩ := exists_matCA_of_mem_closure (psi_mem_closure_ca h₂)
  refine ⟨s.1, ?_⟩
  rw [hs, ← eq_of_matCB_eq_matCA (hs.symm.trans hs')]

theorem exists_matCA_a {x : GHB 7} (h₂ : x ∈ Subgroup.closure {c 7, a 7})
    (h₀ : x ∈ Subgroup.closure {a 7, b 7}) : ∃ j, (psi x : Mat) = matCA (0, j, 0, 0) := by
  obtain ⟨s, hs⟩ := exists_matCA_of_mem_closure (psi_mem_closure_ca h₂)
  obtain ⟨t, ht⟩ := exists_matAB_of_mem_closure (psi_mem_closure_ab h₀)
  refine ⟨s.2.1, ?_⟩
  rw [hs, ← eq_of_matCA_eq_matAB (hs.symm.trans ht)]

theorem exists_matCA_c {x : GHB 7} (h₂ : x ∈ Subgroup.closure {c 7, a 7})
    (h₁ : x ∈ Subgroup.closure {c 7, b 7}) : ∃ i, (psi x : Mat) = matCA (i, 0, 0, 0) := by
  obtain ⟨s, hs⟩ := exists_matCA_of_mem_closure (psi_mem_closure_ca h₂)
  obtain ⟨s', hs'⟩ := exists_matCB_of_mem_closure (psi_mem_closure_cb h₁)
  refine ⟨s.1, ?_⟩
  rw [hs, ← eq_of_matCA_eq_matCB (hs.symm.trans hs')]

/-! ## `ψ` is nontrivial on nontrivial elements of a vertex group -/

theorem psi_ne_one_of_mem_ab [Finite (U3 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3) {x : GHB 7}
    (hx : x ∈ Subgroup.closure {a 7, b 7}) (hx1 : x ≠ 1) : psi x ≠ 1 := by
  intro h1
  rw [← range_u3ToAB] at hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  have hy : y = 1 := injective_psi_comp_u3ToAB h3 (by simpa using h1)
  exact hx1 (by simp [hy])

theorem psi_ne_one_of_mem_cb [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {x : GHB 7}
    (hx : x ∈ Subgroup.closure {c 7, b 7}) (hx1 : x ≠ 1) : psi x ≠ 1 := by
  intro h1
  rw [← range_u4ToCB] at hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  have hy : y = 1 := injective_psi_comp_u4ToCB h4 (by simpa using h1)
  exact hx1 (by simp [hy])

theorem psi_ne_one_of_mem_ca [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {x : GHB 7}
    (hx : x ∈ Subgroup.closure {c 7, a 7}) (hx1 : x ≠ 1) : psi x ≠ 1 := by
  intro h1
  rw [← range_u4ToCA] at hx
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  have hy : y = 1 := injective_psi_comp_u4ToCA h4 (by simpa using h1)
  exact hx1 (by simp [hy])

/-! ## The parameter laws admit no alternating relation of length four -/

theorem mulAB_alternating_ne_zero : ∀ j i l k : ZMod 7, j ≠ 0 → i ≠ 0 → l ≠ 0 → k ≠ 0 →
    mulAB (mulAB (mulAB (0, j, 0) (i, 0, 0)) (0, l, 0)) (k, 0, 0) ≠ 0 := by
  decide +kernel

theorem mulCB_alternating_ne_zero : ∀ j i l k : ZMod 7, j ≠ 0 → i ≠ 0 → l ≠ 0 → k ≠ 0 →
    mulCB (mulCB (mulCB (0, j, 0, 0) (i, 0, 0, 0)) (0, l, 0, 0)) (k, 0, 0, 0) ≠ 0 := by
  decide +kernel

theorem mulCA_alternating_ne_zero : ∀ j i l k : ZMod 7, j ≠ 0 → i ≠ 0 → l ≠ 0 → k ≠ 0 →
    mulCA (mulCA (mulCA (0, j, 0, 0) (i, 0, 0, 0)) (0, l, 0, 0)) (k, 0, 0, 0) ≠ 0 := by
  decide +kernel

/-! ## The alternating relations -/

/-- **At `P₀ = ⟨a,b⟩`**: no relation `x₁ y₁ x₂ y₂ = 1` with `xₖ ∈ P₀ ⊓ P₁` and
`yₖ ∈ P₀ ⊓ P₂` nontrivial. -/
theorem alternating_ne_one_ab [Finite (U3 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    {x₁ y₁ x₂ y₂ : GHB 7}
    (hx₁ : x₁ ∈ Subgroup.closure {a 7, b 7} ⊓ Subgroup.closure {c 7, b 7})
    (hy₁ : y₁ ∈ Subgroup.closure {a 7, b 7} ⊓ Subgroup.closure {c 7, a 7})
    (hx₂ : x₂ ∈ Subgroup.closure {a 7, b 7} ⊓ Subgroup.closure {c 7, b 7})
    (hy₂ : y₂ ∈ Subgroup.closure {a 7, b 7} ⊓ Subgroup.closure {c 7, a 7})
    (hx₁1 : x₁ ≠ 1) (hy₁1 : y₁ ≠ 1) (hx₂1 : x₂ ≠ 1) (hy₂1 : y₂ ≠ 1) :
    x₁ * y₁ * x₂ * y₂ ≠ 1 := by
  intro hrel
  have hne : ∀ {z : GHB 7} {t : P3}, z ∈ Subgroup.closure {a 7, b 7} → z ≠ 1 →
      (psi z : Mat) = matAB t → t ≠ 0 := by
    intro z t hz hz1 ht h0
    apply psi_ne_one_of_mem_ab h3 hz hz1
    apply Units.ext
    rw [ht, h0, matAB_zero, Units.val_one]
  obtain ⟨j₁, hj₁⟩ := exists_matAB_b (Subgroup.mem_inf.mp hx₁).1 (Subgroup.mem_inf.mp hx₁).2
  obtain ⟨i₁, hi₁⟩ := exists_matAB_a (Subgroup.mem_inf.mp hy₁).1 (Subgroup.mem_inf.mp hy₁).2
  obtain ⟨j₂, hj₂⟩ := exists_matAB_b (Subgroup.mem_inf.mp hx₂).1 (Subgroup.mem_inf.mp hx₂).2
  obtain ⟨i₂, hi₂⟩ := exists_matAB_a (Subgroup.mem_inf.mp hy₂).1 (Subgroup.mem_inf.mp hy₂).2
  have h := congrArg (fun g : GHB 7 => ((psi g : GL4) : Mat)) hrel
  simp only [map_mul, Units.val_mul, map_one, Units.val_one, hj₁, hi₁, hj₂, hi₂,
    matAB_mul] at h
  rw [← matAB_zero] at h
  exact mulAB_alternating_ne_zero j₁ i₁ j₂ i₂
    (fun hj => hne (Subgroup.mem_inf.mp hx₁).1 hx₁1 hj₁ (by simp [hj])) (fun hi => hne (Subgroup.mem_inf.mp hy₁).1 hy₁1 hi₁ (by simp [hi]))
    (fun hj => hne (Subgroup.mem_inf.mp hx₂).1 hx₂1 hj₂ (by simp [hj])) (fun hi => hne (Subgroup.mem_inf.mp hy₂).1 hy₂1 hi₂ (by simp [hi]))
    (matAB_injective h)

/-- **At `P₁ = ⟨c,b⟩`**: no relation `x₁ y₁ x₂ y₂ = 1` with `xₖ ∈ P₁ ⊓ P₀` and
`yₖ ∈ P₁ ⊓ P₂` nontrivial. -/
theorem alternating_ne_one_cb [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4)
    {x₁ y₁ x₂ y₂ : GHB 7}
    (hx₁ : x₁ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₁ : y₁ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {c 7, a 7})
    (hx₂ : x₂ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₂ : y₂ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {c 7, a 7})
    (hx₁1 : x₁ ≠ 1) (hy₁1 : y₁ ≠ 1) (hx₂1 : x₂ ≠ 1) (hy₂1 : y₂ ≠ 1) :
    x₁ * y₁ * x₂ * y₂ ≠ 1 := by
  intro hrel
  have hne : ∀ {z : GHB 7} {t : P4}, z ∈ Subgroup.closure {c 7, b 7} → z ≠ 1 →
      (psi z : Mat) = matCB t → t ≠ 0 := by
    intro z t hz hz1 ht h0
    apply psi_ne_one_of_mem_cb h4 hz hz1
    apply Units.ext
    rw [ht, h0, matCB_zero, Units.val_one]
  obtain ⟨j₁, hj₁⟩ := exists_matCB_b (Subgroup.mem_inf.mp hx₁).1 (Subgroup.mem_inf.mp hx₁).2
  obtain ⟨i₁, hi₁⟩ := exists_matCB_c (Subgroup.mem_inf.mp hy₁).1 (Subgroup.mem_inf.mp hy₁).2
  obtain ⟨j₂, hj₂⟩ := exists_matCB_b (Subgroup.mem_inf.mp hx₂).1 (Subgroup.mem_inf.mp hx₂).2
  obtain ⟨i₂, hi₂⟩ := exists_matCB_c (Subgroup.mem_inf.mp hy₂).1 (Subgroup.mem_inf.mp hy₂).2
  have h := congrArg (fun g : GHB 7 => ((psi g : GL4) : Mat)) hrel
  simp only [map_mul, Units.val_mul, map_one, Units.val_one, hj₁, hi₁, hj₂, hi₂,
    matCB_mul] at h
  rw [← matCB_zero] at h
  exact mulCB_alternating_ne_zero j₁ i₁ j₂ i₂
    (fun hj => hne (Subgroup.mem_inf.mp hx₁).1 hx₁1 hj₁ (by simp [hj])) (fun hi => hne (Subgroup.mem_inf.mp hy₁).1 hy₁1 hi₁ (by simp [hi]))
    (fun hj => hne (Subgroup.mem_inf.mp hx₂).1 hx₂1 hj₂ (by simp [hj])) (fun hi => hne (Subgroup.mem_inf.mp hy₂).1 hy₂1 hi₂ (by simp [hi]))
    (matCB_injective h)

/-- **At `P₂ = ⟨c,a⟩`**: no relation `x₁ y₁ x₂ y₂ = 1` with `xₖ ∈ P₂ ⊓ P₀` and
`yₖ ∈ P₂ ⊓ P₁` nontrivial. -/
theorem alternating_ne_one_ca [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4)
    {x₁ y₁ x₂ y₂ : GHB 7}
    (hx₁ : x₁ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₁ : y₁ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {c 7, b 7})
    (hx₂ : x₂ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₂ : y₂ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {c 7, b 7})
    (hx₁1 : x₁ ≠ 1) (hy₁1 : y₁ ≠ 1) (hx₂1 : x₂ ≠ 1) (hy₂1 : y₂ ≠ 1) :
    x₁ * y₁ * x₂ * y₂ ≠ 1 := by
  intro hrel
  have hne : ∀ {z : GHB 7} {t : P4}, z ∈ Subgroup.closure {c 7, a 7} → z ≠ 1 →
      (psi z : Mat) = matCA t → t ≠ 0 := by
    intro z t hz hz1 ht h0
    apply psi_ne_one_of_mem_ca h4 hz hz1
    apply Units.ext
    rw [ht, h0, matCA_zero, Units.val_one]
  obtain ⟨j₁, hj₁⟩ := exists_matCA_a (Subgroup.mem_inf.mp hx₁).1 (Subgroup.mem_inf.mp hx₁).2
  obtain ⟨i₁, hi₁⟩ := exists_matCA_c (Subgroup.mem_inf.mp hy₁).1 (Subgroup.mem_inf.mp hy₁).2
  obtain ⟨j₂, hj₂⟩ := exists_matCA_a (Subgroup.mem_inf.mp hx₂).1 (Subgroup.mem_inf.mp hx₂).2
  obtain ⟨i₂, hi₂⟩ := exists_matCA_c (Subgroup.mem_inf.mp hy₂).1 (Subgroup.mem_inf.mp hy₂).2
  have h := congrArg (fun g : GHB 7 => ((psi g : GL4) : Mat)) hrel
  simp only [map_mul, Units.val_mul, map_one, Units.val_one, hj₁, hi₁, hj₂, hi₂,
    matCA_mul] at h
  rw [← matCA_zero] at h
  exact mulCA_alternating_ne_zero j₁ i₁ j₂ i₂
    (fun hj => hne (Subgroup.mem_inf.mp hx₁).1 hx₁1 hj₁ (by simp [hj])) (fun hi => hne (Subgroup.mem_inf.mp hy₁).1 hy₁1 hi₁ (by simp [hi]))
    (fun hj => hne (Subgroup.mem_inf.mp hx₂).1 hx₂1 hj₂ (by simp [hj])) (fun hi => hne (Subgroup.mem_inf.mp hy₂).1 hy₂1 hi₂ (by simp [hi]))
    (matCA_injective h)

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.alternating_ne_one_ab
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.alternating_ne_one_cb
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.alternating_ne_one_ca
