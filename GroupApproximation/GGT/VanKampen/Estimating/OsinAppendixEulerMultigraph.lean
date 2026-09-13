import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSubdivided
import GroupApproximation.Meta.AxiomGuard

/-!
# Euler's count for a subdivided graph with multiple edges

Osin's graph `Φ'_M` (arXiv:math/0411039v3, Appendix, just before Lemma 9.3) adds to `Φ_M` one
vertex for each section of `∂Δ`, and one edge through each selected region of a cell to a section.
A cell can have several regions to one section, so `Φ'_M` has multiple edges, and condition `(∗)`
asks only for a vertex of `Φ_M` inside every 2-gon.  In Lemma 9.3, "By (∗), every region of it
(except possibly for the outer one) has degree at least three", so the 2-gons enter the Euler count
through the faces of degree two.

`SubdividedMultigraph M ρ C` is `SubdividedGraph` (`Estimating/OsinAppendixEulerSubdivided.lean`)
without `noMultiple`.  This module states and proves:

* `SubdividedMultigraphFaceStatement` (`subdividedMultigraphFace`): every face has degree at least
  four, and in a connected map with more than four darts a face of degree less than six is a
  two-gon (`SubdividedMultigraph.IsTwoGon`), two different regions joining the same two cells and
  consecutive in the rotations at both;
* `MidpointCountTwoGonStatement` (`midpointCountTwoGon`): a planar map with `4m` darts, at most
  `c + m` vertices and every face of degree at least four has `m + 6 ≤ 3c + t`, where `t` is the
  number of faces of degree less than six;
* `EdgeBoundSubdividedMultigraphStatement` (`edgeBoundSubdividedMultigraph`): the same count for a
  planar subdivided multigraph.

A four-step face through a cell dart crosses two regions.  If they are one region, the face runs
out along it and back, both of its end cells hold only that region, and the map is that region
alone (`SubdividedMultigraph.dartCount_le_four_of_facePerm_four`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe v w z

variable (M : CombMap.{v})

/-- If the first three iterates of the face permutation move a dart, its face has degree at least
four. -/
theorem four_le_faceDegree (d : M.Dart)
    (h1 : M.facePerm d ≠ d)
    (h2 : M.facePerm (M.facePerm d) ≠ d)
    (h3 : M.facePerm (M.facePerm (M.facePerm d)) ≠ d) :
    4 ≤ M.faceDegree (M.faceOf d) := by
  classical
  let fibre : Finset M.Dart := Finset.univ.filter (fun x => M.faceOf x = M.faceOf d)
  have hsub : ({d, M.facePerm d, M.facePerm (M.facePerm d),
      M.facePerm (M.facePerm (M.facePerm d))} : Finset M.Dart) ⊆ fibre := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp [fibre, M.faceOf_facePerm]
  have hcard : ({d, M.facePerm d, M.facePerm (M.facePerm d),
      M.facePerm (M.facePerm (M.facePerm d))} : Finset M.Dart).card = 4 := by
    simp [h1.symm, h2.symm, h3.symm]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have hfibre : fibre.card = M.faceDegree (M.faceOf d) := by
    simp [fibre, faceDegree, orbitDegree, Nat.card_eq_fintype_card,
      Fintype.card_subtype, faceOf]
  exact hfibre ▸ hle

/-- **A map subdividing every edge of a multigraph once**: `SubdividedGraph` without
`noMultiple`.  Darts based at cells carry the cell of their edge's cell end; darts based at
midpoints carry their region and the cell at the far end of their edge.  A midpoint holds the two
darts of one region, whose ends are different cells.  Two regions may join the same pair of
cells. -/
structure SubdividedMultigraph (ρ : Type w) (C : Type z) where
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

variable {M}

/-- A subdivided graph is a subdivided multigraph. -/
def SubdividedGraph.toSubdividedMultigraph {ρ : Type w} {C : Type z}
    (S : SubdividedGraph M ρ C) : SubdividedMultigraph M ρ C :=
  { S with }

namespace SubdividedMultigraph

variable {ρ : Type w} {C : Type z} (S : SubdividedMultigraph M ρ C)

/-- **A two-gon**: a face through a cell dart `d` that closes after four steps and crosses two
different regions.  The region of `d` joins `S.endCell d` to `S.endCell (M.facePerm d)`, the region
of `M.facePerm (M.facePerm d)` joins them back, and the two are consecutive in the rotations at
both cells. -/
def IsTwoGon (f : M.Face) : Prop :=
  ∃ d : M.Dart, S.IsCellDart d ∧ M.faceOf d = f ∧
    M.facePerm (M.facePerm (M.facePerm (M.facePerm d))) = d ∧
      S.region (M.facePerm (M.facePerm d)) ≠ S.region d

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

/-- Every face contains a cell dart. -/
theorem exists_cellDart_faceOf (d₀ : M.Dart) :
    ∃ d, S.IsCellDart d ∧ M.faceOf d = M.faceOf d₀ := by
  by_cases h : S.IsCellDart d₀
  · exact ⟨d₀, h, rfl⟩
  · exact ⟨M.facePerm d₀, (S.cellDart_facePerm d₀).mpr h, M.faceOf_facePerm d₀⟩

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

/-- **A four-step face through a cell dart that crosses one region twice traverses that region out
and back**, and both end cells hold only that region. -/
theorem sigma_fixed_of_facePerm_four (d : M.Dart) (hd : S.IsCellDart d)
    (h4 : M.facePerm (M.facePerm (M.facePerm (M.facePerm d))) = d)
    (hR : S.region (M.facePerm (M.facePerm d)) = S.region d) :
    M.sigma d = d ∧ M.sigma (M.alpha (M.facePerm d)) = M.alpha (M.facePerm d) := by
  -- the first region: midpoint darts `alpha d` and `y₁ := facePerm d`
  obtain ⟨hy₁, hreg₁, hne₁, hend₁⟩ := S.facePerm_of_cell d hd
  have hx₁ : ¬ S.IsCellDart (M.alpha d) := fun h => (S.cellDart_alpha d).mp h hd
  -- the second region: `z₁ := facePerm y₁` is a cell dart at the far end of `y₁`
  obtain ⟨hz₁, hendz₁⟩ := S.facePerm_of_midpoint (M.facePerm d) hy₁
  obtain ⟨hy₂, hreg₂, -, -⟩ := S.facePerm_of_cell (M.facePerm (M.facePerm d)) hz₁
  have hx₂ : ¬ S.IsCellDart (M.alpha (M.facePerm (M.facePerm d))) :=
    fun h => (S.cellDart_alpha _).mp h hz₁
  obtain ⟨-, hendz₂⟩ := S.facePerm_of_midpoint (M.facePerm (M.facePerm (M.facePerm d))) hy₂
  rw [h4] at hendz₂
  -- the two regions are one
  have hsame : S.region (M.alpha d) =
      S.region (M.facePerm (M.facePerm (M.facePerm d))) := by
    rw [S.region_alpha, hreg₂, hR]
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

/-- **A four-step face through a cell dart that crosses one region twice is the whole map**: a
connected subdivided multigraph with such a face has at most four darts. -/
theorem dartCount_le_four_of_facePerm_four (hconnected : M.IsConnected) (d : M.Dart)
    (hd : S.IsCellDart d) (h4 : M.facePerm (M.facePerm (M.facePerm (M.facePerm d))) = d)
    (hR : S.region (M.facePerm (M.facePerm d)) = S.region d) : M.dartCount ≤ 4 := by
  classical
  obtain ⟨hsd, hsz⟩ := S.sigma_fixed_of_facePerm_four d hd h4 hR
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
  simp only [Finset.card_univ, dartCount, Nat.card_eq_fintype_card] at hle ⊢
  omega

include S in
/-- **Every face of a subdivided multigraph has degree at least four.** -/
theorem four_le_faceDegree_of_subdividedMultigraph (f : M.Face) : 4 ≤ M.faceDegree f := by
  refine Quotient.inductionOn' f ?_
  intro d₀
  change 4 ≤ M.faceDegree (M.faceOf d₀)
  exact M.four_le_faceDegree d₀ (S.facePerm_ne d₀) (S.facePerm_two_ne d₀)
    (S.facePerm_three_ne d₀)

/-- **A face of degree less than six is a two-gon** in a connected subdivided multigraph with more
than four darts. -/
theorem isTwoGon_of_faceDegree_lt_six (hconnected : M.IsConnected) (hcount : 4 < M.dartCount)
    (f : M.Face) (hf : M.faceDegree f < 6) : S.IsTwoGon f := by
  revert hf
  refine Quotient.inductionOn' f ?_
  intro d₀ hf
  obtain ⟨d, hd, hface⟩ := S.exists_cellDart_faceOf d₀
  change M.faceDegree (M.faceOf d₀) < 6 at hf
  change S.IsTwoGon (M.faceOf d₀)
  rw [← hface] at hf ⊢
  have h4 : M.facePerm (M.facePerm (M.facePerm (M.facePerm d))) = d := by
    by_contra h4
    have h6 := M.six_le_faceDegree d (S.facePerm_ne d) (S.facePerm_two_ne d)
      (S.facePerm_three_ne d) h4 (S.facePerm_five_ne d)
    omega
  refine ⟨d, hd, rfl, h4, fun hR => ?_⟩
  have hsmall := S.dartCount_le_four_of_facePerm_four hconnected d hd h4 hR
  omega

end SubdividedMultigraph

/-- **Euler's count with two-gons.**  A planar map with `4m` darts, at most `c + m` vertices and
every face of degree at least four has `m + 6 ≤ 3c + t`, where `t` is the number of faces of degree
less than six. -/
theorem midpointCount_add_six_le_twoGon (hplanar : M.IsPlanar) {c m : ℕ}
    (hdarts : M.dartCount = 4 * m) (hvertices : M.vertexCount ≤ c + m)
    (hface : ∀ f : M.Face, 4 ≤ M.faceDegree f) :
    m + 6 ≤ 3 * c + (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card := by
  have hEuler := M.euler_eq_two hplanar
  have hedges := M.dartCount_eq_two_mul_edgeCount
  have hsum : 6 * M.faceCount ≤
      M.dartCount + 2 * (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card := by
    calc
      6 * M.faceCount = ∑ _f : M.Face, 6 := by
        simp [faceCount, Nat.mul_comm]
      _ ≤ ∑ f : M.Face, (M.faceDegree f + 2 * (if M.faceDegree f < 6 then 1 else 0)) :=
        Finset.sum_le_sum fun f _ => by
          show 6 ≤ M.faceDegree f + 2 * (if M.faceDegree f < 6 then 1 else 0)
          have := hface f
          split_ifs <;> omega
      _ = M.dartCount +
          2 * (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, M.sum_faceDegree_eq_dartCount,
          Finset.card_filter]
  omega

/-- **The edge bound of a subdivided multigraph**: `m` regions on `c` cells of a planar subdivided
multigraph with `t` faces of degree less than six give `m + 6 ≤ 3c + t`. -/
theorem edgeBound_of_subdividedMultigraph {ρ : Type w} {C : Type z}
    (S : SubdividedMultigraph M ρ C) (hplanar : M.IsPlanar) {c m : ℕ}
    (hdarts : M.dartCount = 4 * m) (hvertices : M.vertexCount ≤ c + m) :
    m + 6 ≤ 3 * c + (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card :=
  midpointCount_add_six_le_twoGon hplanar hdarts hvertices
    S.four_le_faceDegree_of_subdividedMultigraph

/-- **The faces of a subdivided multigraph.**  Every face has degree at least four.  In a connected
map with more than four darts, a face of degree less than six is a two-gon. -/
def SubdividedMultigraphFaceStatement : Prop :=
  ∀ (M : CombMap.{v}) {ρ : Type w} {C : Type z} (S : SubdividedMultigraph M ρ C),
    (∀ f : M.Face, 4 ≤ M.faceDegree f) ∧
      (M.IsConnected → 4 < M.dartCount →
        ∀ f : M.Face, M.faceDegree f < 6 → S.IsTwoGon f)

/-- **Euler's count with two-gons.**  A planar map with `4m` darts, at most `c + m` vertices and
every face of degree at least four has `m + 6 ≤ 3c + t`, where `t` is the number of faces of
degree less than six. -/
def MidpointCountTwoGonStatement : Prop :=
  ∀ (M : CombMap.{v}), M.IsPlanar → ∀ c m : ℕ, M.dartCount = 4 * m →
    M.vertexCount ≤ c + m → (∀ f : M.Face, 4 ≤ M.faceDegree f) →
      m + 6 ≤ 3 * c + (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card

/-- **The edge bound of a subdivided multigraph**: `m` regions on `c` cells of a planar subdivided
multigraph with `t` faces of degree less than six give `m + 6 ≤ 3c + t`. -/
def EdgeBoundSubdividedMultigraphStatement : Prop :=
  ∀ (M : CombMap.{v}) {ρ : Type w} {C : Type z}, SubdividedMultigraph M ρ C → M.IsPlanar →
    ∀ c m : ℕ, M.dartCount = 4 * m → M.vertexCount ≤ c + m →
      m + 6 ≤ 3 * c + (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card

/-- `SubdividedMultigraphFaceStatement` holds. -/
theorem subdividedMultigraphFace : SubdividedMultigraphFaceStatement.{v, w, z} := by
  intro M ρ C S
  exact ⟨S.four_le_faceDegree_of_subdividedMultigraph,
    fun hconnected hcount f hf => S.isTwoGon_of_faceDegree_lt_six hconnected hcount f hf⟩

/-- `MidpointCountTwoGonStatement` holds. -/
theorem midpointCountTwoGon : MidpointCountTwoGonStatement.{v} := by
  intro M hplanar c m hdarts hvertices hface
  exact midpointCount_add_six_le_twoGon hplanar hdarts hvertices hface

/-- `EdgeBoundSubdividedMultigraphStatement` holds. -/
theorem edgeBoundSubdividedMultigraph : EdgeBoundSubdividedMultigraphStatement.{v, w, z} := by
  intro M ρ C S hplanar c m hdarts hvertices
  exact edgeBound_of_subdividedMultigraph S hplanar hdarts hvertices

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.four_le_faceDegree
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.SubdividedMultigraph.sigma_fixed_of_facePerm_four
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.SubdividedMultigraph.dartCount_le_four_of_facePerm_four
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.SubdividedMultigraph.four_le_faceDegree_of_subdividedMultigraph
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.SubdividedMultigraph.isTwoGon_of_faceDegree_lt_six
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.midpointCount_add_six_le_twoGon
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.edgeBound_of_subdividedMultigraph
#audit_closed_axioms GroupApproximation.GGT.VanKampen.CombMap.subdividedMultigraphFace
#audit_closed_axioms GroupApproximation.GGT.VanKampen.CombMap.midpointCountTwoGon
#audit_closed_axioms GroupApproximation.GGT.VanKampen.CombMap.edgeBoundSubdividedMultigraph
