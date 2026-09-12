import GroupApproximation.Algebra.ValuedMatrixTwoCartan
import GroupApproximation.Kazhdan.LevelTreeAcyclic
import GroupApproximation.Kazhdan.TreeHalfSpaces

/-!
# The Bruhat--Tits tree of `GL_2` over a valued field, and Kazhdan subgroups

The tree step of the rank-two remark after `prop:torsion-defect-ring` of
`non_mf_groups_exist.tex` (tex lines 1146--1150).

For a field `K` with a discrete valuation `v` and uniformizer `π`, the vertices
are the left cosets `GL_2(K) / S` (`S = K^× GL_2(O)`, the zero set of the
displacement `dispInt`), and two cosets are adjacent when the displacement between
representatives is one.  The level of `g S` is `dispInt g`; adjacent levels differ
by one (`dispInt_adj`), every vertex has a unique lower neighbour
(`lower_neighbour` after the Cartan decomposition), and the Cartan decomposition
also connects every vertex to the standard one.  So the graph is a tree
(`LevelTree.isTree_of_level`), and `GL_2(K)` acts on it by left multiplication.

**Consequence.**  A group with property `(T)` mapping to `GL_2(K)` has bounded
displacement: `dispInt (ρ γ)` is bounded uniformly in `γ` (Delorme's theorem through
`TreeAction.exists_dist_bound_of_hasKazhdanPropertyT`).
-/

namespace GroupApproximation
namespace ValuedMatrixTwo

open Matrix

universe u

variable {K : Type u} [Field K] (v : AddValuation K (WithTop ℤ))

/-- The vertices: left cosets of `S`. -/
abbrev Vertex := GL (Fin 2) K ⧸ stab v

theorem dispInt_inv_mul_congr {g g' h h' : GL (Fin 2) K}
    (hg : (QuotientGroup.mk g : Vertex v) = QuotientGroup.mk g')
    (hh : (QuotientGroup.mk h : Vertex v) = QuotientGroup.mk h') :
    dispInt v (g⁻¹ * h) = dispInt v (g'⁻¹ * h') := by
  rw [QuotientGroup.eq] at hg hh
  have e : g'⁻¹ * h' = (g⁻¹ * g')⁻¹ * (g⁻¹ * h) * (h⁻¹ * h') := by group
  rw [e, dispInt_mul_stab v hh, dispInt_stab_mul v ((stab v).inv_mem hg)]

/-- **The Bruhat--Tits graph.** -/
def btGraph : SimpleGraph (Vertex v) where
  Adj x y := ∃ g h : GL (Fin 2) K, (QuotientGroup.mk g : Vertex v) = x ∧
    (QuotientGroup.mk h : Vertex v) = y ∧ dispInt v (g⁻¹ * h) = 1
  symm := ⟨by
    rintro x y ⟨g, h, rfl, rfl, hgh⟩
    refine ⟨h, g, rfl, rfl, ?_⟩
    rw [← dispInt_inv, _root_.mul_inv_rev, inv_inv]
    exact hgh⟩
  loopless := ⟨by
    rintro x ⟨g, h, hg, hh, hgh⟩
    have h0 : dispInt v (g⁻¹ * h) = 0 := (mem_stab v).mp (QuotientGroup.eq.mp (hg.trans hh.symm))
    omega⟩

theorem btGraph_adj_mk (g h : GL (Fin 2) K) :
    (btGraph v).Adj (QuotientGroup.mk g) (QuotientGroup.mk h) ↔ dispInt v (g⁻¹ * h) = 1 := by
  constructor
  · rintro ⟨g', h', hg', hh', h1⟩
    rwa [dispInt_inv_mul_congr v hg' hh'] at h1
  · intro h1
    exact ⟨g, h, rfl, rfl, h1⟩

/-- The level of a vertex: the displacement of a representative. -/
noncomputable def level : Vertex v → ℕ :=
  Quotient.lift (fun g : GL (Fin 2) K ↦ (dispInt v g).toNat) (by
    intro a b hab
    have hs : a⁻¹ * b ∈ stab v := QuotientGroup.leftRel_apply.mp hab
    show (dispInt v a).toNat = (dispInt v b).toNat
    rw [show b = a * (a⁻¹ * b) by group, dispInt_mul_stab v hs])

theorem level_mk (g : GL (Fin 2) K) : level v (QuotientGroup.mk g) = (dispInt v g).toNat := rfl

theorem level_adj {x y : Vertex v} (hxy : (btGraph v).Adj x y) :
    level v y = level v x + 1 ∨ level v x = level v y + 1 := by
  obtain ⟨g, h, rfl, rfl, h1⟩ := hxy
  have t := dispInt_adj v h1
  have hg := dispInt_nonneg v g
  have hh := dispInt_nonneg v h
  rw [level_mk, level_mk]
  omega

variable {π : K} (hπ : v π = 1)

include hπ in
theorem level_unique_lower {x y z : Vertex v} (hxy : (btGraph v).Adj x y)
    (hxz : (btGraph v).Adj x z) (hy : level v y + 1 = level v x)
    (hz : level v z + 1 = level v x) : y = z := by
  obtain ⟨g, h₁, rfl, rfl, h1⟩ := hxy
  obtain ⟨g', h₂, hgg', rfl, h2⟩ := hxz
  rw [dispInt_inv_mul_congr v hgg' rfl] at h2
  obtain ⟨s₁, hs₁, s₂, hs₂, hg⟩ := cartan v hπ g
  generalize hn : (dispInt v g).toNat = n at hg
  have key : ∀ h : GL (Fin 2) K, dispInt v (g⁻¹ * h) = 1 →
      level v (QuotientGroup.mk h) + 1 = level v (QuotientGroup.mk g) →
      (QuotientGroup.mk h : Vertex v) = QuotientGroup.mk (s₁ * diagPow v hπ n * diagPiOne v hπ) := by
    intro h hh hlev
    have hda : dispInt v ((diagPow v hπ n)⁻¹ * (s₁⁻¹ * h)) = 1 := by
      have e : (diagPow v hπ n)⁻¹ * (s₁⁻¹ * h) = s₂ * (g⁻¹ * h) := by rw [hg]; group
      rw [e, dispInt_stab_mul v hs₂, hh]
    have hlow : dispInt v (diagPow v hπ n * ((diagPow v hπ n)⁻¹ * (s₁⁻¹ * h))) + 1 = n := by
      have e : diagPow v hπ n * ((diagPow v hπ n)⁻¹ * (s₁⁻¹ * h)) = s₁⁻¹ * h := by group
      rw [e, dispInt_stab_mul v ((stab v).inv_mem hs₁)]
      rw [level_mk, level_mk, hn] at hlev
      have := dispInt_nonneg v h
      omega
    obtain ⟨b, hb, hab⟩ := lower_neighbour v hπ hda hlow
    rw [QuotientGroup.eq]
    have hh' : h = s₁ * diagPow v hπ n * (diagPiOne v hπ * b) := by
      rw [← hab]
      group
    have e : h⁻¹ * (s₁ * diagPow v hπ n * diagPiOne v hπ) = b⁻¹ := by
      rw [hh']
      group
    rw [e]
    exact (stab v).inv_mem hb
  exact (key h₁ h1 hy).trans (key h₂ h2 hz).symm

theorem reachable_diagPow (s : GL (Fin 2) K) (n : ℕ) :
    (btGraph v).Reachable (QuotientGroup.mk s) (QuotientGroup.mk (s * diagPow v hπ n)) := by
  induction n with
  | zero =>
      rw [diagPow_zero, mul_one]
  | succ n ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      rw [btGraph_adj_mk, diagPow_succ]
      have e : (s * diagPow v hπ n)⁻¹ * (s * (diagPow v hπ n * diagPow v hπ 1)) =
          diagPow v hπ 1 := by group
      rw [e, dispInt_diagPow]
      simp

include hπ in
theorem btGraph_connected : (btGraph v).Connected := by
  haveI : Nonempty (Vertex v) := ⟨QuotientGroup.mk 1⟩
  have hbase : ∀ x : Vertex v, (btGraph v).Reachable (QuotientGroup.mk 1) x := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨s₁, hs₁, s₂, hs₂, hg⟩ := cartan v hπ g
    generalize hn : (dispInt v g).toNat = n at hg
    have h1 : (QuotientGroup.mk 1 : Vertex v) = QuotientGroup.mk s₁ :=
      QuotientGroup.eq.mpr (by simpa using hs₁)
    have h2 : (QuotientGroup.mk g : Vertex v) = QuotientGroup.mk (s₁ * diagPow v hπ n) := by
      rw [QuotientGroup.eq, hg]
      have e : (s₁ * diagPow v hπ n * s₂)⁻¹ * (s₁ * diagPow v hπ n) = s₂⁻¹ := by group
      rw [e]
      exact (stab v).inv_mem hs₂
    rw [h1, h2]
    exact reachable_diagPow v hπ s₁ n
  exact ⟨fun x y ↦ (hbase x).symm.trans (hbase y)⟩

include hπ in
/-- **The Bruhat--Tits graph is a tree.** -/
theorem btGraph_isTree : (btGraph v).IsTree :=
  LevelTree.isTree_of_level (level v) (btGraph_connected v hπ) (fun _ _ h ↦ level_adj v h)
    (fun _ _ _ hxy hxz hy hz ↦ level_unique_lower v hπ hxy hxz hy hz)

theorem btGraph_isGraphAction : TreeAction.IsGraphAction (GL (Fin 2) K) (btGraph v) := by
  intro g x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, btGraph_adj_mk, btGraph_adj_mk,
    smul_eq_mul, smul_eq_mul]
  have e : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
  rw [e]

include hπ in
/-- **Kazhdan groups have bounded displacement on the Bruhat--Tits tree.** -/
theorem exists_dispInt_bound_of_hasKazhdanPropertyT {Γ : Type u} [Group Γ]
    (hT : HasKazhdanPropertyT.{u, u} Γ) (ρ : Γ →* GL (Fin 2) K) :
    ∃ R : ℝ, ∀ γ : Γ, (dispInt v (ρ γ) : ℝ) ≤ R := by
  letI : MulAction Γ (Vertex v) := MulAction.compHom (Vertex v) ρ
  have hG : TreeAction.IsGraphAction Γ (btGraph v) := fun γ x y ↦ btGraph_isGraphAction v (ρ γ) x y
  have hTree := btGraph_isTree v hπ
  obtain ⟨R, hR⟩ := TreeAction.exists_dist_bound_of_hasKazhdanPropertyT hTree hG hT
    (QuotientGroup.mk 1 : Vertex v)
  refine ⟨R, fun γ ↦ ?_⟩
  have hsmul : (γ • (QuotientGroup.mk 1 : Vertex v)) = QuotientGroup.mk (ρ γ) := by
    show ρ γ • (QuotientGroup.mk 1 : Vertex v) = _
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hlev := LevelTree.level_le_add_dist (level v) (fun _ _ h ↦ level_adj v h) hTree.connected
    (QuotientGroup.mk 1 : Vertex v) (γ • (QuotientGroup.mk 1 : Vertex v))
  rw [hsmul, level_mk, level_mk, dispInt_one] at hlev
  have h1 := hR γ
  rw [hsmul] at h1
  have hnn := dispInt_nonneg v (ρ γ)
  have hz : dispInt v (ρ γ) ≤ ((btGraph v).dist (QuotientGroup.mk 1) (QuotientGroup.mk (ρ γ)) : ℤ) := by
    omega
  have hr : (dispInt v (ρ γ) : ℝ) ≤
      ((btGraph v).dist (QuotientGroup.mk 1) (QuotientGroup.mk (ρ γ)) : ℝ) := by
    exact_mod_cast hz
  exact hr.trans h1

end ValuedMatrixTwo
end GroupApproximation

#audit_axioms GroupApproximation.ValuedMatrixTwo.btGraph_isTree
#audit_axioms GroupApproximation.ValuedMatrixTwo.exists_dispInt_bound_of_hasKazhdanPropertyT
