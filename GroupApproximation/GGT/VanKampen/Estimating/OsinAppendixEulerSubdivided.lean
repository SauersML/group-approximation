import GroupApproximation.GGT.VanKampen.CombMapSimpleEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# Euler's count for a graph with every edge subdivided once

Osin's graph `Φ_M` (math/0411039, Appendix, just before Lemma 9.3) has the relator cells as
vertices and one edge through each selected contiguity region.  In a combinatorial map the edge
through a region is realized as two map edges meeting at a *midpoint* vertex, the region's own face
in the dual of the collapsed diagram.  This file proves the Euler count for such a map directly, so
that no suppression of the midpoints is needed.

`SubdividedGraph M ρ C` records the structure: darts are based either at cells or at midpoints, edge
reversal swaps the two kinds, a midpoint carries exactly the two darts of one region, and the two ends
of a region are different cells.  With the hypothesis that no two regions join the same pair of cells
(`noMultiple`), every face of a connected map with more than one region has degree at least six
(`six_le_faceDegree_of_subdividedGraph`), and Euler's formula gives `m ≤ 3(c − 1)` for `m` regions on
`c` cells (`edgeBound_of_subdividedGraph`).
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe v w z

variable (M : CombMap.{v})

/-- A dart property closed under edge reversal and vertex rotation holds everywhere in a connected
map. -/
theorem forall_of_closed (hconnected : M.IsConnected) (P : M.Dart → Prop)
    (halpha : ∀ y, P (M.alpha y) ↔ P y) (hsigma : ∀ y, P (M.sigma y) ↔ P y)
    {d : M.Dart} (hd : P d) (x : M.Dart) : P x := by
  have hmove : ∀ a b, M.Adjacent a b → (P a ↔ P b) := by
    intro a b h
    rcases h with rfl | rfl
    · exact (halpha a).symm
    · exact (hsigma a).symm
  have hclosure : ∀ a b, Relation.EqvGen M.Adjacent a b → (P a ↔ P b) := by
    intro a b h
    induction h with
    | rel a b h => exact hmove a b h
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hclosure d x (hconnected d x)).mp hd

/-- If the first five iterates of the face permutation move a dart, its face has degree at least
six. -/
theorem six_le_faceDegree (d : M.Dart)
    (h1 : M.facePerm d ≠ d)
    (h2 : M.facePerm (M.facePerm d) ≠ d)
    (h3 : M.facePerm (M.facePerm (M.facePerm d)) ≠ d)
    (h4 : M.facePerm (M.facePerm (M.facePerm (M.facePerm d))) ≠ d)
    (h5 : M.facePerm (M.facePerm (M.facePerm (M.facePerm (M.facePerm d)))) ≠ d) :
    6 ≤ M.faceDegree (M.faceOf d) := by
  classical
  let fibre : Finset M.Dart := Finset.univ.filter (fun x => M.faceOf x = M.faceOf d)
  have hsub : ({d, M.facePerm d, M.facePerm (M.facePerm d),
      M.facePerm (M.facePerm (M.facePerm d)),
      M.facePerm (M.facePerm (M.facePerm (M.facePerm d))),
      M.facePerm (M.facePerm (M.facePerm (M.facePerm (M.facePerm d))))} :
        Finset M.Dart) ⊆ fibre := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [fibre, M.faceOf_facePerm]
  have hcard : ({d, M.facePerm d, M.facePerm (M.facePerm d),
      M.facePerm (M.facePerm (M.facePerm d)),
      M.facePerm (M.facePerm (M.facePerm (M.facePerm d))),
      M.facePerm (M.facePerm (M.facePerm (M.facePerm (M.facePerm d))))} :
        Finset M.Dart).card = 6 := by
    simp [h1.symm, h2.symm, h3.symm, h4.symm, h5.symm]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have hfibre : fibre.card = M.faceDegree (M.faceOf d) := by
    simp [fibre, faceDegree, orbitDegree, Nat.card_eq_fintype_card,
      Fintype.card_subtype, faceOf]
  exact hfibre ▸ hle

/-- **A map subdividing every edge of a graph once.**  Darts based at cells carry the cell of their
edge's cell end; darts based at midpoints carry their region and the cell at the far end of their
edge.  A midpoint holds the two darts of one region, whose ends are different cells, and no two
regions join the same pair of cells. -/
structure SubdividedGraph (ρ : Type w) (C : Type z) where
  /-- The darts based at cells; the others are based at midpoints. -/
  IsCellDart : M.Dart → Prop
  /-- The region of the edge carrying a dart. -/
  region : M.Dart → ρ
  /-- The cell at the cell end of the edge carrying a dart. -/
  endCell : M.Dart → C
  cellDart_alpha : ∀ d, IsCellDart (M.alpha d) ↔ ¬ IsCellDart d
  region_alpha : ∀ d, region (M.alpha d) = region d
  endCell_alpha : ∀ d, endCell (M.alpha d) = endCell d
  cellDart_of_vertex : ∀ d e, M.vertexOf d = M.vertexOf e → (IsCellDart d ↔ IsCellDart e)
  endCell_of_vertex : ∀ d e, IsCellDart d → IsCellDart e →
    M.vertexOf d = M.vertexOf e → endCell d = endCell e
  region_of_vertex : ∀ d e, ¬ IsCellDart d → ¬ IsCellDart e →
    M.vertexOf d = M.vertexOf e → region d = region e
  sigma_ne_of_midpoint : ∀ d, ¬ IsCellDart d → M.sigma d ≠ d
  endCell_ne : ∀ d e, ¬ IsCellDart d → ¬ IsCellDart e → region e = region d → d ≠ e →
    endCell d ≠ endCell e
  midpoint_two : ∀ d e x, ¬ IsCellDart d → ¬ IsCellDart e → ¬ IsCellDart x →
    region e = region d → region x = region d → d ≠ e → x = d ∨ x = e
  noMultiple : ∀ d e d' e', ¬ IsCellDart d → ¬ IsCellDart e → ¬ IsCellDart d' →
    ¬ IsCellDart e' → region e = region d → region e' = region d' → d ≠ e → d' ≠ e' →
    endCell d = endCell d' → endCell e = endCell e' → region d = region d'

namespace SubdividedGraph

variable {M} {ρ : Type w} {C : Type z} (S : SubdividedGraph M ρ C)

theorem cellDart_sigma (d : M.Dart) : S.IsCellDart (M.sigma d) ↔ S.IsCellDart d :=
  S.cellDart_of_vertex _ _ (M.vertexOf_sigma d)

theorem cellDart_facePerm (d : M.Dart) :
    S.IsCellDart (M.facePerm d) ↔ ¬ S.IsCellDart d := by
  change S.IsCellDart (M.sigma (M.alpha d)) ↔ _
  rw [S.cellDart_sigma, S.cellDart_alpha]

theorem endCell_sigma (d : M.Dart) (hd : S.IsCellDart d) :
    S.endCell (M.sigma d) = S.endCell d :=
  S.endCell_of_vertex _ _ ((S.cellDart_sigma d).mpr hd) hd (M.vertexOf_sigma d)

theorem region_sigma (d : M.Dart) (hd : ¬ S.IsCellDart d) :
    S.region (M.sigma d) = S.region d :=
  S.region_of_vertex _ _ (fun h => hd ((S.cellDart_sigma d).mp h)) hd (M.vertexOf_sigma d)

include S in
/-- A face permutation step changes the kind of a dart, so odd iterates move every dart. -/
theorem facePerm_ne (d : M.Dart) : M.facePerm d ≠ d := by
  intro h
  have hk := S.cellDart_facePerm d
  rw [h] at hk
  tauto

include S in
theorem facePerm_three_ne (d : M.Dart) :
    M.facePerm (M.facePerm (M.facePerm d)) ≠ d := by
  intro h
  have h1 := S.cellDart_facePerm d
  have h2 := S.cellDart_facePerm (M.facePerm d)
  have h3 := S.cellDart_facePerm (M.facePerm (M.facePerm d))
  rw [h] at h3
  tauto

include S in
theorem facePerm_five_ne (d : M.Dart) :
    M.facePerm (M.facePerm (M.facePerm (M.facePerm (M.facePerm d)))) ≠ d := by
  intro h
  have h1 := S.cellDart_facePerm d
  have h2 := S.cellDart_facePerm (M.facePerm d)
  have h3 := S.cellDart_facePerm (M.facePerm (M.facePerm d))
  have h4 := S.cellDart_facePerm (M.facePerm (M.facePerm (M.facePerm d)))
  have h5 := S.cellDart_facePerm (M.facePerm (M.facePerm (M.facePerm (M.facePerm d))))
  rw [h] at h5
  tauto

/-- One step out of a cell dart reaches the other midpoint dart of its region, whose end is a
different cell. -/
theorem facePerm_of_cell (d : M.Dart) (hd : S.IsCellDart d) :
    ¬ S.IsCellDart (M.facePerm d) ∧ S.region (M.facePerm d) = S.region d ∧
      M.facePerm d ≠ M.alpha d ∧ S.endCell (M.facePerm d) ≠ S.endCell d := by
  have hx : ¬ S.IsCellDart (M.alpha d) := fun h => (S.cellDart_alpha d).mp h hd
  have hy : ¬ S.IsCellDart (M.facePerm d) := fun h => (S.cellDart_facePerm d).mp h hd
  have hreg : S.region (M.facePerm d) = S.region d := by
    change S.region (M.sigma (M.alpha d)) = _
    rw [S.region_sigma _ hx, S.region_alpha]
  have hne : M.facePerm d ≠ M.alpha d := S.sigma_ne_of_midpoint _ hx
  refine ⟨hy, hreg, hne, ?_⟩
  have h := S.endCell_ne (M.alpha d) (M.facePerm d) hx hy (by rw [hreg, S.region_alpha])
    hne.symm
  rw [S.endCell_alpha] at h
  exact h.symm

/-- One step out of a midpoint dart reaches a cell dart at the far end of its edge. -/
theorem facePerm_of_midpoint (d : M.Dart) (hd : ¬ S.IsCellDart d) :
    S.IsCellDart (M.facePerm d) ∧ S.endCell (M.facePerm d) = S.endCell d := by
  have hx : S.IsCellDart (M.alpha d) := (S.cellDart_alpha d).mpr hd
  refine ⟨(S.cellDart_facePerm d).mpr hd, ?_⟩
  change S.endCell (M.sigma (M.alpha d)) = _
  rw [S.endCell_sigma _ hx, S.endCell_alpha]

include S in
/-- **No face of degree two**: a two-step face through a cell dart would join a cell to itself. -/
theorem facePerm_two_ne (d : M.Dart) : M.facePerm (M.facePerm d) ≠ d := by
  intro h
  by_cases hd : S.IsCellDart d
  · obtain ⟨hy, -, -, hend⟩ := S.facePerm_of_cell d hd
    obtain ⟨-, hend'⟩ := S.facePerm_of_midpoint (M.facePerm d) hy
    rw [h] at hend'
    exact hend hend'.symm
  · have hy := (S.cellDart_facePerm d).mpr hd
    obtain ⟨-, -, -, hend⟩ := S.facePerm_of_cell (M.facePerm d) hy
    obtain ⟨-, hend'⟩ := S.facePerm_of_midpoint d hd
    rw [h] at hend
    exact hend hend'.symm

/-- **A four-step face through a cell dart traverses one region out and back**: by `noMultiple`
the two regions it crosses coincide, and both end cells hold only that region. -/
theorem sigma_fixed_of_facePerm_four (d : M.Dart) (hd : S.IsCellDart d)
    (h4 : M.facePerm (M.facePerm (M.facePerm (M.facePerm d))) = d) :
    M.sigma d = d ∧ M.sigma (M.alpha (M.facePerm d)) = M.alpha (M.facePerm d) := by
  -- the first region: midpoint darts `alpha d` and `y₁ := facePerm d`
  obtain ⟨hy₁, hreg₁, hne₁, hend₁⟩ := S.facePerm_of_cell d hd
  have hx₁ : ¬ S.IsCellDart (M.alpha d) := fun h => (S.cellDart_alpha d).mp h hd
  -- the second region: `z₁ := facePerm y₁` is a cell dart at the far end of `y₁`
  obtain ⟨hz₁, hendz₁⟩ := S.facePerm_of_midpoint (M.facePerm d) hy₁
  obtain ⟨hy₂, hreg₂, hne₂, -⟩ := S.facePerm_of_cell (M.facePerm (M.facePerm d)) hz₁
  have hx₂ : ¬ S.IsCellDart (M.alpha (M.facePerm (M.facePerm d))) :=
    fun h => (S.cellDart_alpha _).mp h hz₁
  obtain ⟨-, hendz₂⟩ := S.facePerm_of_midpoint (M.facePerm (M.facePerm (M.facePerm d))) hy₂
  rw [h4] at hendz₂
  -- both regions join the ends of `d` and of `y₁`
  have hsame : S.region (M.alpha d) =
      S.region (M.facePerm (M.facePerm (M.facePerm d))) := by
    apply S.noMultiple (M.alpha d) (M.facePerm d)
      (M.facePerm (M.facePerm (M.facePerm d))) (M.alpha (M.facePerm (M.facePerm d)))
      hx₁ hy₁ hy₂ hx₂
    · rw [hreg₁, S.region_alpha]
    · rw [S.region_alpha, hreg₂]
    · exact hne₁.symm
    · exact hne₂
    · rw [S.endCell_alpha, hendz₂]
    · rw [S.endCell_alpha, hendz₁]
  have hregd : S.region (M.alpha d) = S.region d := S.region_alpha d
  have hregz : S.region (M.alpha (M.facePerm (M.facePerm d))) =
      S.region (M.alpha d) := by
    rw [S.region_alpha, ← hreg₂, ← hsame]
  -- `alpha z₁` is one of the two midpoint darts of the first region, at the end of `y₁`
  have hz₁eq : M.alpha (M.facePerm (M.facePerm d)) = M.facePerm d := by
    rcases S.midpoint_two (M.alpha d) (M.facePerm d) (M.alpha (M.facePerm (M.facePerm d)))
        hx₁ hy₁ hx₂ (by rw [hreg₁, hregd]) hregz hne₁.symm with h | h
    · exfalso
      have hc := congrArg S.endCell h
      rw [S.endCell_alpha, S.endCell_alpha, hendz₁] at hc
      exact hend₁ hc
    · exact h
  -- `y₂` is the other midpoint dart of the first region, at the end of `d`
  have hy₂eq : M.facePerm (M.facePerm (M.facePerm d)) = M.alpha d := by
    rcases S.midpoint_two (M.alpha d) (M.facePerm d)
        (M.facePerm (M.facePerm (M.facePerm d))) hx₁ hy₁ hy₂ (by rw [hreg₁, hregd])
        hsame.symm hne₁.symm with h | h
    · exact h
    · exfalso
      have hc := congrArg S.endCell h
      exact hend₁ (hc.symm.trans hendz₂.symm)
  constructor
  · have h := h4
    rw [hy₂eq] at h
    change M.sigma (M.alpha (M.alpha d)) = d at h
    rwa [M.alpha_involutive] at h
  · have h := congrArg M.alpha hz₁eq
    rw [M.alpha_involutive] at h
    exact h

include S in
/-- **Every face of a connected subdivided graph with more than one region has degree at least
six.** -/
theorem six_le_faceDegree_of_subdividedGraph (hconnected : M.IsConnected)
    (hcount : 4 < M.dartCount) (f : M.Face) : 6 ≤ M.faceDegree f := by
  classical
  refine Quotient.inductionOn' f ?_
  intro d₀
  -- read the face from a cell dart
  obtain ⟨d, hd, hface⟩ : ∃ d, S.IsCellDart d ∧ M.faceOf d = M.faceOf d₀ := by
    by_cases h : S.IsCellDart d₀
    · exact ⟨d₀, h, rfl⟩
    · exact ⟨M.facePerm d₀, (S.cellDart_facePerm d₀).mpr h, M.faceOf_facePerm d₀⟩
  change 6 ≤ M.faceDegree (M.faceOf d₀)
  rw [← hface]
  refine M.six_le_faceDegree d (S.facePerm_ne d) (S.facePerm_two_ne d)
    (S.facePerm_three_ne d) ?_ (S.facePerm_five_ne d)
  intro h4
  obtain ⟨hsd, hsz⟩ := S.sigma_fixed_of_facePerm_four d hd h4
  obtain ⟨hy₁, hreg₁, hne₁, -⟩ := S.facePerm_of_cell d hd
  have hx₁ : ¬ S.IsCellDart (M.alpha d) := fun h => (S.cellDart_alpha d).mp h hd
  -- the four darts of the region form a closed set
  let P : M.Dart → Prop := fun y =>
    y = d ∨ y = M.alpha d ∨ y = M.facePerm d ∨ y = M.alpha (M.facePerm d)
  have hsy : M.sigma (M.facePerm d) = M.alpha d := by
    rcases S.midpoint_two (M.alpha d) (M.facePerm d) (M.sigma (M.facePerm d)) hx₁ hy₁
        (fun h => hy₁ ((S.cellDart_sigma _).mp h))
        (by rw [hreg₁, S.region_alpha])
        (by rw [S.region_sigma _ hy₁, hreg₁, S.region_alpha]) hne₁.symm with h | h
    · exact h
    · exact (S.sigma_ne_of_midpoint _ hy₁ h).elim
  have hsx : M.sigma (M.alpha d) = M.facePerm d := rfl
  have halpha : ∀ y, P (M.alpha y) ↔ P y := by
    intro y
    constructor
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inl ((M.alpha_involutive y).symm.trans (congrArg M.alpha h)))
      · exact Or.inl (M.alpha.injective h)
      · exact Or.inr (Or.inr (Or.inr ((M.alpha_involutive y).symm.trans
          (congrArg M.alpha h))))
      · exact Or.inr (Or.inr (Or.inl (M.alpha.injective h)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (M.alpha_involutive _)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (M.alpha_involutive _)))
  have hsigma : ∀ y, P (M.sigma y) ↔ P y := by
    intro y
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (M.sigma.injective (h.trans hsd.symm))
      · exact Or.inr (Or.inr (Or.inl (M.sigma.injective (h.trans hsy.symm))))
      · exact Or.inr (Or.inl (M.sigma.injective (h.trans hsx.symm)))
      · exact Or.inr (Or.inr (Or.inr (M.sigma.injective (h.trans hsz.symm))))
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl hsd
      · exact Or.inr (Or.inr (Or.inl hsx))
      · exact Or.inr (Or.inl hsy)
      · exact Or.inr (Or.inr (Or.inr hsz))
  have hall := M.forall_of_closed hconnected P halpha hsigma (Or.inl rfl)
  have hsub : (Finset.univ : Finset M.Dart) ⊆
      {d, M.alpha d, M.facePerm d, M.alpha (M.facePerm d)} := by
    intro x _
    rcases hall x with h | h | h | h <;> simp [h]
  have ha := Finset.card_insert_le d
    ({M.alpha d, M.facePerm d, M.alpha (M.facePerm d)} : Finset M.Dart)
  have hb := Finset.card_insert_le (M.alpha d)
    ({M.facePerm d, M.alpha (M.facePerm d)} : Finset M.Dart)
  have hc : ({M.facePerm d, M.alpha (M.facePerm d)} : Finset M.Dart).card ≤ 2 :=
    Finset.card_le_two
  have hle := Finset.card_le_card hsub
  have hdarts : M.dartCount ≤ 4 := by
    simp only [Finset.card_univ, dartCount, Nat.card_eq_fintype_card] at hle ⊢
    omega
  omega

end SubdividedGraph

/-- **Euler's count at six-sided faces.**  A planar map with `4m` darts, at most `c + m` vertices
and every face of degree at least six has `m + 6 ≤ 3c`. -/
theorem midpointCount_add_six_le (hplanar : M.IsPlanar) {c m : ℕ}
    (hdarts : M.dartCount = 4 * m) (hvertices : M.vertexCount ≤ c + m)
    (hface : ∀ f : M.Face, 6 ≤ M.faceDegree f) : m + 6 ≤ 3 * c := by
  classical
  have hEuler := M.euler_eq_two hplanar
  have hedges := M.dartCount_eq_two_mul_edgeCount
  have hsum : 6 * M.faceCount ≤ M.dartCount := by
    calc
      6 * M.faceCount = ∑ _f : M.Face, 6 := by
        simp [faceCount, Nat.mul_comm]
      _ ≤ ∑ f : M.Face, M.faceDegree f := Finset.sum_le_sum fun f _ => hface f
      _ = M.dartCount := M.sum_faceDegree_eq_dartCount
  omega

/-- **The edge bound of a subdivided graph**: `m` regions on `c ≥ 2` cells of a connected planar
map give `m ≤ 3(c − 1)`. -/
theorem edgeBound_of_subdividedGraph {ρ : Type w} {C : Type z} (S : SubdividedGraph M ρ C)
    (hplanar : M.IsPlanar) {c m : ℕ} (hc : 2 ≤ c)
    (hdarts : M.dartCount = 4 * m) (hvertices : M.vertexCount ≤ c + m) :
    m ≤ 3 * (c - 1) := by
  by_cases hsmall : M.dartCount ≤ 4
  · omega
  · have h := M.midpointCount_add_six_le hplanar hdarts hvertices
      (S.six_le_faceDegree_of_subdividedGraph (M.connected_of_planar hplanar) (by omega))
    omega

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.forall_of_closed
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.six_le_faceDegree
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.SubdividedGraph.facePerm_two_ne
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.SubdividedGraph.sigma_fixed_of_facePerm_four
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.SubdividedGraph.six_le_faceDegree_of_subdividedGraph
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.midpointCount_add_six_le
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.edgeBound_of_subdividedGraph
