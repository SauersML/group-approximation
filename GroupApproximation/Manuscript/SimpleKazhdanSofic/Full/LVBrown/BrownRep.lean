import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVBrown.Action
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's criterion: representatives of generators (T1d)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735, leaf **T1d** (Khanh,
arXiv:2609.08428, Thm 5.1; K. S. Brown 1984, Thm 1).

The group `G` acts on an ordered 2-complex, and its action is transitive on ordered edges
`(v0, v1)`.  Write `J` for the vertex stabilizer `MulAction.stabilizer G v0`.  We are given a
homomorphism `f : J →* Q` and an element `t : Q`, which is to be the image of `τ`.

`Rep v0 τ f t g q` says that `q` is a candidate image of `g`.  Either `g ∈ J` and `q = f g`, or
`g = k τ j` with `k, j ∈ J` and `q = f k · t · f j`.

* `rep_exists`: a generator `g` of the Brown presentation, i.e. an element with `g • v0` near
  `v0`, has a representative (edge transitivity).
* `rep_unique`: representatives are unique (the edge relation, `t² = f(τ²)` and the braid
  relation `t h t = h t h`).
-/

namespace GroupApproximation.Full.LVBrown

open GroupApproximation.Full.LVFrame

section Algebra

variable {Q : Type*} [Group Q]

/-- The algebra behind uniqueness when both representatives go through `τ`. -/
theorem alg_bb {t Fk Fk' Fa Fj Fj' Fb : Q} (hk : Fk = Fk' * Fa) (hj : Fj' = Fb * Fj)
    (he : t * Fb * t⁻¹ = Fa) : Fk * t * Fj = Fk' * t * Fj' := by
  subst hk
  subst hj
  subst he
  group

/-- The algebra behind uniqueness when `τ` lies in the vertex stabilizer. -/
theorem alg_ab {t U Hq : Q} (hc : t * U * t⁻¹ = U) (h2 : t * t = U * U)
    (hh : t * Hq * t⁻¹ = U * Hq * U⁻¹) (hb : U * Hq * U = Hq * U * Hq)
    (hbr : t * Hq * t = Hq * t * Hq) : t = U := by
  obtain ⟨z, rfl⟩ : ∃ z, t = U * z := ⟨U⁻¹ * t, by group⟩
  have c1 : z * U = U * z := by
    calc z * U = U⁻¹ * (U * z * U * (U * z)⁻¹) * U * z := by group
      _ = U⁻¹ * U * U * z := by rw [hc]
      _ = U * z := by group
  have c2 : z * z = 1 := by
    calc z * z = U⁻¹ * U⁻¹ * (U * (U * z) * z) := by group
      _ = U⁻¹ * U⁻¹ * (U * (z * U) * z) := by rw [c1]
      _ = U⁻¹ * U⁻¹ * (U * z * (U * z)) := by group
      _ = U⁻¹ * U⁻¹ * (U * U) := by rw [h2]
      _ = 1 := by group
  have c3 : z * Hq = Hq * z := by
    calc z * Hq = U⁻¹ * (U * z * Hq * (U * z)⁻¹) * U * z := by group
      _ = U⁻¹ * (U * Hq * U⁻¹) * U * z := by rw [hh]
      _ = Hq * z := by group
  have key : Hq * U * Hq * z = Hq * U * Hq := by
    calc Hq * U * Hq * z = Hq * U * (Hq * z) := by group
      _ = Hq * U * (z * Hq) := by rw [c3]
      _ = Hq * (U * z) * Hq := by group
      _ = U * z * Hq * (U * z) := by rw [hbr]
      _ = U * (z * Hq) * U * z := by group
      _ = U * (Hq * z) * U * z := by rw [c3]
      _ = U * Hq * (z * U) * z := by group
      _ = U * Hq * (U * z) * z := by rw [c1]
      _ = U * Hq * U * (z * z) := by group
      _ = U * Hq * U * 1 := by rw [c2]
      _ = U * Hq * U := by group
      _ = Hq * U * Hq := hb
  have hz : z = 1 := by
    calc z = (Hq * U * Hq)⁻¹ * (Hq * U * Hq * z) := by group
      _ = (Hq * U * Hq)⁻¹ * (Hq * U * Hq) := by rw [key]
      _ = 1 := by group
  rw [hz, mul_one]

/-- The algebra behind the triangle case of the core lemma. -/
theorem alg_tri {t G' P' Hq Gq Pq : Q} (h1 : t * G' * t⁻¹ = Gq) (h2 : t * P' * t⁻¹ = Pq)
    (h3 : t * Hq * t = Hq * t * Hq) : t * (G' * Hq * Pq) * t = Gq * Hq * t * (Hq * P') := by
  subst h1
  subst h2
  calc t * (G' * Hq * (t * P' * t⁻¹)) * t = t * G' * t⁻¹ * (t * Hq * t) * P' := by group
    _ = t * G' * t⁻¹ * (Hq * t * Hq) * P' := by rw [h3]
    _ = t * G' * t⁻¹ * Hq * t * (Hq * P') := by group

end Algebra

variable {G V Q : Type*} [Group G] [MulAction G V] [Group Q]

/-- `q` is a candidate image of `g`.  Either `g ∈ J` and `q = f g`, or `g = k τ j` with
`k, j ∈ J` and `q = f k · t · f j`. -/
def Rep (v0 : V) (τ : G) (f : MulAction.stabilizer G v0 →* Q) (t : Q) (g : G) (q : Q) : Prop :=
  (∃ j : MulAction.stabilizer G v0, (j : G) = g ∧ q = f j) ∨
    ∃ k j : MulAction.stabilizer G v0, g = (k : G) * τ * (j : G) ∧ q = f k * t * f j

theorem smul_stab {v0 : V} (j : MulAction.stabilizer G v0) : (j : G) • v0 = v0 :=
  MulAction.mem_stabilizer_iff.mp j.2

theorem rep_of_mem {v0 : V} {τ : G} {t : Q} (f : MulAction.stabilizer G v0 →* Q)
    (j : MulAction.stabilizer G v0) : Rep v0 τ f t (j : G) (f j) :=
  Or.inl ⟨j, rfl, rfl⟩

theorem rep_tau {v0 : V} (τ : G) (f : MulAction.stabilizer G v0 →* Q) (t : Q) :
    Rep v0 τ f t τ t :=
  Or.inr ⟨1, 1, by simp, by simp⟩

theorem rep_mul_left {v0 : V} {τ : G} {f : MulAction.stabilizer G v0 →* Q} {t : Q} {g : G}
    {q : Q} (j : MulAction.stabilizer G v0) (h : Rep v0 τ f t g q) :
    Rep v0 τ f t ((j : G) * g) (f j * q) := by
  rcases h with ⟨i, rfl, rfl⟩ | ⟨k, i, rfl, rfl⟩
  · exact Or.inl ⟨j * i, rfl, (map_mul f j i).symm⟩
  · refine Or.inr ⟨j * k, i, ?_, ?_⟩
    · show (j : G) * ((k : G) * τ * (i : G)) = (j : G) * (k : G) * τ * (i : G)
      simp only [mul_assoc]
    · simp only [map_mul, mul_assoc]

theorem rep_mul_right {v0 : V} {τ : G} {f : MulAction.stabilizer G v0 →* Q} {t : Q} {g : G}
    {q : Q} (j : MulAction.stabilizer G v0) (h : Rep v0 τ f t g q) :
    Rep v0 τ f t (g * (j : G)) (q * f j) := by
  rcases h with ⟨i, rfl, rfl⟩ | ⟨k, i, rfl, rfl⟩
  · exact Or.inl ⟨i * j, rfl, (map_mul f i j).symm⟩
  · refine Or.inr ⟨k, i * j, ?_, ?_⟩
    · show (k : G) * τ * (i : G) * (j : G) = (k : G) * τ * ((i : G) * (j : G))
      simp only [mul_assoc]
    · simp only [map_mul, mul_assoc]

theorem rep_congr {v0 : V} {τ : G} {f : MulAction.stabilizer G v0 →* Q} {t : Q} {g g' : G}
    {q q' : Q} (h : Rep v0 τ f t g q) (hg : g = g') (hq : q = q') : Rep v0 τ f t g' q' := by
  subst hg
  subst hq
  exact h

/-- **Existence.**  An element carrying `v0` to a vertex near `v0` has a representative. -/
theorem rep_exists {X : OrderedTwoComplex V} {v0 v1 : V} {τ : G}
    (edge_transitive : ∀ a b, X.edge a b → ∃ g : G, g • v0 = a ∧ g • v1 = b)
    (hτ0 : τ • v0 = v1) (hτ2 : (τ * τ) • v0 = v0) (f : MulAction.stabilizer G v0 →* Q) (t : Q)
    {g : G} (hn : Near X v0 (g • v0)) : ∃ q, Rep v0 τ f t g q := by
  rcases hn with h | h | h
  · exact ⟨f ⟨g, MulAction.mem_stabilizer_iff.mpr h.symm⟩,
      Or.inl ⟨⟨g, MulAction.mem_stabilizer_iff.mpr h.symm⟩, rfl, rfl⟩⟩
  · obtain ⟨k, hk0, hk1⟩ := edge_transitive _ _ h
    have hj : τ⁻¹ * k⁻¹ * g ∈ MulAction.stabilizer G v0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hk1, inv_smul_smul, ← hτ0,
        inv_smul_smul]
    refine ⟨f ⟨k, MulAction.mem_stabilizer_iff.mpr hk0⟩ * t * f ⟨τ⁻¹ * k⁻¹ * g, hj⟩,
      Or.inr ⟨⟨k, MulAction.mem_stabilizer_iff.mpr hk0⟩, ⟨τ⁻¹ * k⁻¹ * g, hj⟩, ?_, rfl⟩⟩
    show g = k * τ * (τ⁻¹ * k⁻¹ * g)
    group
  · obtain ⟨m, hm0, hm1⟩ := edge_transitive _ _ h
    have hk : m * τ ∈ MulAction.stabilizer G v0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hτ0, hm1]
    have hj : (τ * τ)⁻¹ * m⁻¹ * g ∈ MulAction.stabilizer G v0 := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hm0, inv_smul_smul]
      exact inv_smul_eq_iff.mpr hτ2.symm
    refine ⟨f ⟨m * τ, hk⟩ * t * f ⟨(τ * τ)⁻¹ * m⁻¹ * g, hj⟩,
      Or.inr ⟨⟨m * τ, hk⟩, ⟨(τ * τ)⁻¹ * m⁻¹ * g, hj⟩, ?_, rfl⟩⟩
    show g = m * τ * τ * ((τ * τ)⁻¹ * m⁻¹ * g)
    group

/-- Uniqueness when both representatives go through `τ`. -/
theorem unique_bb {v0 v1 : V} {τ : G} (hτ1 : τ • v1 = v0) (f : MulAction.stabilizer G v0 →* Q)
    (t : Q)
    (hedge : ∀ a b : MulAction.stabilizer G v0, (a : G) • v1 = v1 → (b : G) = τ * a * τ⁻¹ →
      t * f a * t⁻¹ = f b)
    {g : G} {k j k' j' : MulAction.stabilizer G v0} (hg : g = (k : G) * τ * (j : G))
    (hg' : g = (k' : G) * τ * (j' : G)) : f k * t * f j = f k' * t * f j' := by
  have heq : (k : G) * τ * (j : G) = (k' : G) * τ * (j' : G) := hg.symm.trans hg'
  have hτinv0 : τ⁻¹ • v0 = v1 := by rw [← hτ1, inv_smul_smul]
  have ha' : (k' : G)⁻¹ * (k : G) = τ * ((j' : G) * (j : G)⁻¹) * τ⁻¹ := by
    calc (k' : G)⁻¹ * (k : G) = (k' : G)⁻¹ * ((k : G) * τ * (j : G)) * (j : G)⁻¹ * τ⁻¹ := by
          group
      _ = (k' : G)⁻¹ * ((k' : G) * τ * (j' : G)) * (j : G)⁻¹ * τ⁻¹ := by rw [heq]
      _ = τ * ((j' : G) * (j : G)⁻¹) * τ⁻¹ := by group
  have ha0 : ((k' : G)⁻¹ * (k : G)) • v0 = v0 := smul_stab (k'⁻¹ * k)
  have hb1 : ((j' * j⁻¹ : MulAction.stabilizer G v0) : G) • v1 = v1 := by
    show ((j' : G) * (j : G)⁻¹) • v1 = v1
    rw [show (j' : G) * (j : G)⁻¹ = τ⁻¹ * ((k' : G)⁻¹ * (k : G)) * τ by rw [ha']; group,
      mul_smul, mul_smul, hτ1, ha0, hτinv0]
  have he := hedge (j' * j⁻¹) (k'⁻¹ * k) hb1 ha'
  refine alg_bb ?_ ?_ he
  · rw [← map_mul, mul_inv_cancel_left]
  · rw [← map_mul, inv_mul_cancel_right]

/-- Uniqueness when one representative lies in the vertex stabilizer. -/
theorem unique_ab {v0 v1 : V} {τ h : G} (hτ0 : τ • v0 = v1) (hh0 : h • v0 = v0)
    (hbraid : τ * h * τ = h * τ * h) (f : MulAction.stabilizer G v0 →* Q) (t : Q)
    (hedge : ∀ a b : MulAction.stabilizer G v0, (a : G) • v1 = v1 → (b : G) = τ * a * τ⁻¹ →
      t * f a * t⁻¹ = f b)
    (hτ2 : (τ * τ) • v0 = v0) (ht2 : t * t = f ⟨τ * τ, hτ2⟩)
    (hbr : t * f ⟨h, hh0⟩ * t = f ⟨h, hh0⟩ * t * f ⟨h, hh0⟩)
    {g : G} {j k m : MulAction.stabilizer G v0} (hj : (j : G) = g)
    (hg : g = (k : G) * τ * (m : G)) : f j = f k * t * f m := by
  subst hj
  obtain ⟨u, hu, hju⟩ : ∃ u : MulAction.stabilizer G v0, (u : G) = τ ∧ j = k * u * m :=
    ⟨k⁻¹ * j * m⁻¹, by show (k : G)⁻¹ * (j : G) * (m : G)⁻¹ = τ; rw [hg]; group, by group⟩
  subst hju
  have hv : v1 = v0 := by
    rw [← hτ0, ← hu]
    exact smul_stab u
  have hu1 : (u : G) • v1 = v1 := by
    rw [hv]
    exact smul_stab u
  have hc : t * f u * t⁻¹ = f u := hedge u u hu1 (by rw [hu]; group)
  have h2 : t * t = f u * f u := by
    rw [ht2, ← map_mul]
    congr 1
    exact Subtype.ext (by show τ * τ = (u : G) * (u : G); rw [hu])
  have hH1 : ((⟨h, hh0⟩ : MulAction.stabilizer G v0) : G) • v1 = v1 := by
    rw [hv]
    exact hh0
  have hh := hedge ⟨h, hh0⟩ (u * ⟨h, hh0⟩ * u⁻¹) hH1
    (by show (u : G) * h * (u : G)⁻¹ = τ * h * τ⁻¹; rw [hu])
  rw [map_mul, map_mul, map_inv] at hh
  have hb : f u * f ⟨h, hh0⟩ * f u = f ⟨h, hh0⟩ * f u * f ⟨h, hh0⟩ := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by show (u : G) * h * (u : G) = h * (u : G) * h; rw [hu]; exact hbraid)
  rw [map_mul, map_mul, alg_ab hc h2 hh hb hbr]

/-- **Uniqueness.**  Two representatives of the same element agree. -/
theorem rep_unique {v0 v1 : V} {τ h : G} (hτ0 : τ • v0 = v1) (hτ1 : τ • v1 = v0)
    (hh0 : h • v0 = v0) (hbraid : τ * h * τ = h * τ * h) (f : MulAction.stabilizer G v0 →* Q)
    (t : Q)
    (hedge : ∀ a b : MulAction.stabilizer G v0, (a : G) • v1 = v1 → (b : G) = τ * a * τ⁻¹ →
      t * f a * t⁻¹ = f b)
    (hτ2 : (τ * τ) • v0 = v0) (ht2 : t * t = f ⟨τ * τ, hτ2⟩)
    (hbr : t * f ⟨h, hh0⟩ * t = f ⟨h, hh0⟩ * t * f ⟨h, hh0⟩)
    {g : G} {q q' : Q} (hq : Rep v0 τ f t g q) (hq' : Rep v0 τ f t g q') : q = q' := by
  rcases hq with ⟨j, hj, rfl⟩ | ⟨k, j, hg, rfl⟩
  · rcases hq' with ⟨j', hj', rfl⟩ | ⟨k', j', hg', rfl⟩
    · rw [Subtype.ext (hj.trans hj'.symm)]
    · exact unique_ab hτ0 hh0 hbraid f t hedge hτ2 ht2 hbr hj hg'
  · rcases hq' with ⟨j', hj', rfl⟩ | ⟨k', j', hg', rfl⟩
    · exact (unique_ab hτ0 hh0 hbraid f t hedge hτ2 ht2 hbr hj' hg).symm
    · exact unique_bb hτ1 f t hedge hg hg'

#audit_axioms GroupApproximation.Full.LVBrown.rep_unique

end GroupApproximation.Full.LVBrown
